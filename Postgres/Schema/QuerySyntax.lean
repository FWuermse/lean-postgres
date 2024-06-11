/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino, Florian Würmseer
-/

import Lean
import Postgres.Schema.QueryDSL

open Lean Elab Meta Term

namespace QuerySyntax

declare_syntax_cat      parsId
syntax ident          : parsId
syntax "(" parsId ")" : parsId

declare_syntax_cat           selectField
syntax parsId              : selectField
syntax parsId " AS " ident : selectField

declare_syntax_cat                 sqlSelect
syntax "*"                       : sqlSelect
syntax "DISTINCT " "*"           : sqlSelect
syntax selectField,+             : sqlSelect
syntax "DISTINCT " selectField,+ : sqlSelect

declare_syntax_cat           entry
syntax num                 : entry
syntax "-" noWs num        : entry
syntax str                 : entry
syntax scientific          : entry
syntax "-" noWs scientific : entry
syntax "NULL"              : entry
syntax "(" entry ")"       : entry

declare_syntax_cat propSymbol
syntax " = "     : propSymbol
syntax " <> "    : propSymbol
syntax " != "    : propSymbol
syntax " < "     : propSymbol
syntax " <= "    : propSymbol
syntax " > "     : propSymbol
syntax " >= "    : propSymbol

declare_syntax_cat                prop
syntax "TRUE"                   : prop
syntax "FALSE"                  : prop
syntax parsId propSymbol parsId : prop
syntax parsId propSymbol entry  : prop
syntax prop " AND " prop        : prop
syntax prop " OR "  prop        : prop
syntax " NOT " prop             : prop
syntax "(" prop ")"             : prop

declare_syntax_cat join
syntax " INNER " : join
syntax " LEFT "  : join
syntax " RIGHT " : join
syntax " OUTER " : join

declare_syntax_cat                                      sqlFrom
declare_syntax_cat                                      query

syntax ident                                          : sqlFrom
syntax sqlFrom ", " sqlFrom                           : sqlFrom
syntax sqlFrom " AS " ident                           : sqlFrom
syntax sqlFrom join " JOIN " sqlFrom " ON " prop      : sqlFrom
syntax sqlFrom join " JOIN " sqlFrom " USING " parsId : sqlFrom
syntax "(" sqlFrom ")"                                : sqlFrom
syntax "(" query ")"                                  : sqlFrom

syntax "SELECT " sqlSelect " FROM " sqlFrom (" WHERE " prop)? : query

syntax (name := pgquery) "queryOn" ident " | " query : term

def mkStrOfIdent (id : Syntax) : Expr :=
  mkStrLit id.getId.toString

structure QueryState :=
  expr : Expr
  tag : Option String := .none
  as : HashMap String (HashSet String) := HashMap.empty
  tables : HashSet String := HashSet.empty

def QueryState.toString : QueryState → String
  | s => s!"{s.expr}, {s.tag}"

instance : ToString QueryState :=
  ⟨QueryState.toString⟩

-- TODO: is reader sufficient
abbrev SchemaTermElabM := StateRefT QueryState TermElabM

def exprToField : Expr → SchemaTermElabM Field
  | Expr.app ctor (Expr.lit <| Literal.strVal s) =>
    match ctor with
      | Expr.const `Field.nat _ => pure (Field.nat s)
      | Expr.app (Expr.const `Field.varchar _) numExpr => do
        if let .some nat ← getNatValue? numExpr then
          if nat > 255 then
            throwError "The maximum value for Varchar is 255, failure on {numExpr} with value {nat}"
          pure (Field.varchar nat s)
        else throwError s!"Unsupported Length param for Varchar {numExpr}"
      | Expr.const `Field.char _ => pure (Field.char s)
      | Expr.const `Field.date _ => pure (Field.date s)
      | e => throwError s!"Unsupported Field of type: {e}"
  | _ => throwUnsupportedSyntax

def elabField : Field → SchemaTermElabM Expr
  | Field.nat s => pure <| mkApp (mkConst `Field.nat) (mkStrLit s)
  | Field.varchar n s => pure <| mkApp2 (mkConst `Field.varchar) (mkNatLit n) (mkStrLit s)
  | Field.char s => pure <| mkApp (mkConst `Field.char) (mkStrLit s)
  | Field.date s => pure <| mkApp (mkConst `Field.date) (mkStrLit s)

partial def elabStrOfParsId : Syntax → TermElabM Expr
  | `(parsId|$id:ident)      => pure $ mkStrOfIdent id
  | `(parsId|($pars:parsId)) => elabStrOfParsId pars
  | _                        => throwUnsupportedSyntax

partial def parsIdToString : Syntax → String
  | `(parsId|$id:ident)      => id.getId.toString
  | `(parsId|($pars:parsId)) => parsIdToString pars
  | _                        => ""

def elabCol : TSyntax `selectField → SchemaTermElabM Expr
  | `(selectField|$c:parsId)             => do
    mkAppM `SQLSelectField.col #[← elabStrOfParsId c]
  | `(selectField|$c:parsId AS $a:ident) => do
    mkAppM `SQLSelectField.alias #[← elabStrOfParsId c, mkStrOfIdent a]
  | _                                    => throwUnsupportedSyntax

def findFieldsInTable : List Field → String → SchemaTermElabM (List Field) :=
  fun table id => do
    let state ← get
    let sections := id.splitOn "."
    if sections.length > 1 then
      let (pfx, sfx) := sections.splitAt <| sections.length - 1
      let key := ".".intercalate pfx
      let aliases := match state.as.find? key with
        -- get! 0 is safe because of the invariant: length > 1 ∧ splitAt length-1 with 0 has sfx length 1, splitAt length-1 with n+1 has unchanged suffix.
        | some v => v.fold (fun l s => l ++ table.filter (fun f : Field => f.getName == s!"{s}.{sfx.get! 0}")) []
        | none => []
      let direct : List Field := match table.filter (fun f => (f.getName.splitOn ".").getLast! == sfx.get! 0 || f.getName == id) with
        | [] => aliases
        | l => l
      pure direct
    else
      let direct : List Field := match table.find? (fun f => f.getName == id) with
        | some v => [v]
        | none => table.filter (fun f => (f.getName.splitOn ".").getLast! == id)
      pure direct

def elabProjType (cols : List (TSyntax `selectField)): SchemaTermElabM Expr := do
  let state ← get
  let mut selType : List Field := []
  if let .some exprs := state.expr.listLit? then
    let exprs ← exprs.snd.mapM exprToField
    if cols.isEmpty then
      throwError s!"Cannot select from an empty Table"
    for typ in cols do
      match typ with
        | `(selectField|$c:parsId) => do
          let id := parsIdToString c
          let selId := (← findFieldsInTable exprs id)
          selType := selType ++ selId
          if selId.isEmpty then
            throwError s!"Cannot select Field {id} from Table {exprs}"
        | `(selectField|$c:parsId AS $a:ident) => do
          let id := parsIdToString c
          let al := a.getId.toString
          let selId := (← findFieldsInTable exprs id) --.map (Field.setName . al)
          selType := selType ++ selId
          if selId.isEmpty then
            throwError s!"Cannot select Field {id} from Table {exprs}"
        | _ => throwUnsupportedSyntax
    else
      throwUnsupportedSyntax
    mkListLit (mkConst `Field) (← selType.mapM elabField)

def elabSelect : TSyntax `sqlSelect → SchemaTermElabM Expr
  | `(sqlSelect|*)                          => do
    pure <| mkApp2 (mkConst ``SQLSelect.all) (← get).expr (mkConst ``false)
  | `(sqlSelect|DISTINCT *)                 => do
    -- TODO make distinct
    pure <| mkApp2 (mkConst `SQLSelect.all) (← get).expr (mkConst ``true)
  | `(sqlSelect|$cs:selectField,*)          => do
    let cols ← mkListLit (mkConst `SQLSelectField) (← cs.getElems.toList.mapM elabCol)
    let typ ← elabProjType cs.getElems.toList
    set { ← get with expr := typ}
    pure <| mkApp3 (mkConst `SQLSelect.list) typ (mkConst ``false) (cols)
  | `(sqlSelect|DISTINCT $cs:selectField,*) => do
    let cols ← mkListLit (mkConst `SQLSelectField) (← cs.getElems.toList.mapM elabCol)
    let typ ← elabProjType cs.getElems.toList.eraseDup
    set { ← get with expr := typ}
    pure <| mkApp3 (mkConst `SQLSelect.list) typ (mkConst ``false) (cols)
  | _                                       => throwUnsupportedSyntax

def mkApp' (name : Name) (e : Expr) : Expr :=
  mkApp (mkConst name) e

def elabConst (name : Name) : TermElabM Expr :=
  pure $ mkConst name

def negFloat (f : Float) : Float :=
  -1.0 * f

partial def elabEntry : TSyntax `entry → TermElabM Expr
  | `(entry|$v:num)         =>
    mkAppM `DataEntry.EInt #[mkApp' `Int.ofNat (mkNatLit v.getNat)]
  | `(entry|-$v:num)        =>
    mkAppM `DataEntry.EInt $ match v.getNat with
      | Nat.zero   => #[mkApp' `Int.ofNat (mkConst `Nat.zero)]
      | Nat.succ n => #[mkApp' `Int.negSucc (mkNatLit n)]
  | `(entry|$v:scientific)  => do
    mkAppM `DataEntry.EFloat #[← Term.elabScientificLit v (mkConst `Float)]
  | `(entry|-$v:scientific) => do
    let f ← Term.elabScientificLit v (mkConst `Float)
    mkAppM `DataEntry.EFloat #[mkApp' `negFloat f]
  | `(entry|$v:str)         =>
    mkAppM `DataEntry.EString #[mkStrLit $ v.getString]
  | `(entry|NULL)              => elabConst `DataEntry.ENull
  | `(entry|($e:entry))        => elabEntry e
  | _                          => throwUnsupportedSyntax

def elabPropSymbol (stx : TSyntax `propSymbol) (isEntry : Bool) : TermElabM Name :=
  match stx with
  | `(propSymbol|=)  => pure $ if isEntry then `SQLProp.eqE else `SQLProp.eqC
  | `(propSymbol|<>) => pure $ if isEntry then `SQLProp.neE else `SQLProp.neC
  | `(propSymbol|!=) => pure $ if isEntry then `SQLProp.neE else `SQLProp.neC
  | `(propSymbol|<)  => pure $ if isEntry then `SQLProp.ltE else `SQLProp.ltC
  | `(propSymbol|<=) => pure $ if isEntry then `SQLProp.leE else `SQLProp.leC
  | `(propSymbol|>)  => pure $ if isEntry then `SQLProp.gtE else `SQLProp.gtC
  | `(propSymbol|>=) => pure $ if isEntry then `SQLProp.geE else `SQLProp.geC
  | _                => throwUnsupportedSyntax

partial def elabProp : TSyntax `prop → TermElabM Expr
  | `(prop|TRUE)                              => elabConst `SQLProp.tt
  | `(prop|FALSE)                             => elabConst `SQLProp.ff
  | `(prop|$l:parsId $s:propSymbol $r:parsId) => do
    mkAppM (← elabPropSymbol s false) #[← elabStrOfParsId l, ← elabStrOfParsId r]
  | `(prop|$c:parsId $s:propSymbol $e:entry)  => do
    mkAppM (← elabPropSymbol s true) #[← elabStrOfParsId c, ← elabEntry e]
  | `(prop|$l:prop AND $r:prop)               => do
    mkAppM `SQLProp.and #[← elabProp l, ← elabProp r]
  | `(prop|$l:prop OR $r:prop)                => do
    mkAppM `SQLProp.or #[← elabProp l, ← elabProp r]
  | `(prop|NOT $p:prop)                       => do
    mkAppM `SQLProp.not #[← elabProp p]
  | `(prop|($p:prop))                         => elabProp p
  | _                                         => throwUnsupportedSyntax

def elabJoin : TSyntax `join → TermElabM Expr
  | `(join|INNER) => elabConst `SQLJoin.inner
  | `(join|LEFT)  => elabConst `SQLJoin.left
  | `(join|RIGHT) => elabConst `SQLJoin.right
  | `(join|OUTER) => elabConst `SQLJoin.outer
  | _             => throwUnsupportedSyntax

def getListFromExpr : Expr → SchemaTermElabM (List Field) := fun x => do
  if let .some styp := x.listLit? then
    styp.snd.mapM exprToField
  else
    throwUnsupportedSyntax

def tagFromList : SchemaTermElabM Unit := do
  let state ← get
  let list ← getListFromExpr state.expr
  let tagged := match state.tag with
    | some t => list.map fun f => Field.setName f s!"{t}.{f.getName}"
    | none => list
  let typ ← mkListLit (mkConst `Field) (← tagged.mapM elabField)
  set { state with expr := typ, tag := .none }

def concatFrom : QueryState → QueryState → SchemaTermElabM Expr :=
  fun l r => do
    let lfields ← getListFromExpr l.expr
    let rfields ← getListFromExpr r.expr
    let typ ← (lfields ++ rfields).mapM elabField
    let typ ← mkListLit (mkConst `Field) typ
    let state ← get
    set { state with expr := typ, tag := .none }
    pure typ

mutual
partial def elabFrom : TSyntax `sqlFrom → SchemaTermElabM Expr
  | `(sqlFrom|$t:ident)               => do
    let tableName := t.getId.toString
    let state ← get
    -- Get List from Schema
    let typ ← whnf (mkApp state.expr (mkStrOfIdent t))
    -- Set State for Tagging
    set { state with expr := typ, tag := tableName, tables := state.tables.insert tableName }
    -- Remove
    let _ ← tagFromList
    pure <| mkApp2 (mkConst `SQLFrom.table) (← get).expr (mkStrOfIdent t)
  | `(sqlFrom|$f:sqlFrom AS $t:ident) => do
    let frm ← elabFrom f
    let state ← get
    set { state with as := state.as.insert t.getId.toString state.tables }
    pure <| mkApp3 (mkConst `SQLFrom.alias) (← get).expr (frm) (mkStrOfIdent t)
  | `(sqlFrom|$l:sqlFrom, $r:sqlFrom) => do
    let elabFromFun := (elabFrom l).run
    let (lfrm, ltyp) ← elabFromFun (← get)
    let rfrm ← elabFrom r
    let rtyp ← get
    let typ ← concatFrom ltyp rtyp
    elabAppArgs (mkApp3 (mkConst `SQLFrom.implicitJoin) ltyp.expr rtyp.expr typ) #[] #[Arg.expr lfrm, Arg.expr rfrm] .none (explicit := false) (ellipsis := false)
  | `(sqlFrom|$l:sqlFrom $j:join JOIN $r:sqlFrom ON $p:prop) => do
    let (lfrm, lstate) ← (elabFrom l).run (← get)
    let rfrm ← elabFrom r
    let rstate ← get
    let typ ← concatFrom lstate rstate
    set { ← get with tables := lstate.tables.merge rstate.tables, as := lstate.as.mergeWith (fun _ _ b => b) rstate.as}
    elabAppArgs (mkApp3 (mkConst `SQLFrom.join) lstate.expr rstate.expr typ) #[] #[Arg.expr (← elabJoin j), Arg.expr lfrm, Arg.expr rfrm, Arg.expr (← elabProp p)] .none (explicit := false) (ellipsis := false)
  | `(sqlFrom|$l:sqlFrom $j:join JOIN $r:sqlFrom USING $p:parsId) => do
    let (lfrm, ltyp) ← (elabFrom l).run (← get)
    let rfrm ← elabFrom r
    let rtyp ← get
    let typ ← concatFrom ltyp rtyp
    pure <| mkApp4 (mkApp3 (mkConst `SQLFrom.joinUsing) ltyp.expr rtyp.expr typ) (← elabJoin j) lfrm rfrm (← elabStrOfParsId p)
  | `(sqlFrom|($f:sqlFrom))           => do
    elabFrom f
  | `(sqlFrom| ($query:query)) => do
    let qry ← elabQuery query
    pure <| mkApp2 (mkConst `SQLFrom.nestedJoin) (← get).expr qry
  | _                                 => throwUnsupportedSyntax

partial def elabQuery : TSyntax `query → SchemaTermElabM Expr
  | `(query| SELECT $sel FROM $frm:sqlFrom $[WHERE $prp]?) => do
    let whr ← match prp with
      | none     => elabConst `SQLProp.tt
      | some prp => elabProp prp
    let ctx ← get
    let (frm, ftyp) ← (elabFrom frm).run ctx
    let ftyp := { ftyp with tag := .none }
    set ftyp
    let (sel, styp) ← (elabSelect sel).run (← get)
    set styp
    let expr := mkApp4 (mkConst `SQLQuery.mk) styp.expr ftyp.expr sel frm
    let query ← elabAppArgs expr #[] #[Arg.expr whr] .none (explicit := false) (ellipsis := false)
    pure query
  | _ => throwUnsupportedSyntax
end

-- TODO: check elab_rules
elab_rules : term
  | `(pgquery| queryOn $schema | $query) => do
    let env ← getEnv
    -- let ctx ← getLCtx
    -- getLocalDeclFromUserName (find FVAr)
    -- resolveName
    if let .some s := env.find? schema.getId then
      let (query, _) ← (elabQuery query).run { expr := s.value! }
      pure query
    else
      throwUnsupportedSyntax

def schema : String → List Field
  | "myTable" => [Field.nat "id", Field.nat "name"]
  | "otherTable" => [Field.nat "id", Field.date "date"]
  | "thirdTable" => [Field.nat "id", Field.varchar 255 "someField"]
  | _ => []

def x := queryOn QuerySyntax.schema | SELECT name FROM myTable
def nested := queryOn QuerySyntax.schema |
  SELECT *
  FROM (SELECT id
        FROM (SELECT *
              FROM myTable))

def join := queryOn QuerySyntax.schema |
  SELECT date, name FROM myTable INNER JOIN otherTable ON myTable.id = otherTable.id

def implicitJoin := queryOn QuerySyntax.schema |
  SELECT myTable.id AS nm, X.date
  FROM myTable, otherTable AS X
  WHERE myTable.id = otherTable.id

--def empty := queryOn QuerySyntax.schema | SELECT a FROM myTable

def doubleJoin := queryOn QuerySyntax.schema |
  SELECT id FROM otherTable LEFT JOIN (myTable LEFT JOIN myTable ON id = id) ON id = id

def tableAliasNested := queryOn QuerySyntax.schema |
  SELECT y.id FROM thirdTable LEFT JOIN (myTable LEFT JOIN otherTable ON id = id) AS x ON id = id AS y

def selectAliasNested := queryOn QuerySyntax.schema |
  SELECT a.a.id FROM (SELECT id AS a FROM myTable) AS a.a

def selectImplicitSimple := queryOn QuerySyntax.schema |
  SELECT myTable.id FROM myTable

def s : String → List Field
  | "information_schema.tables" => [Field.varchar 255 "table_name", Field.nat "dummy"]
  | _ => []

def query := queryOn QuerySyntax.s |
  SELECT table_name
  FROM information_schema.tables
  WHERE table_schema = "public"
    AND table_type = "BASE TABLE"
