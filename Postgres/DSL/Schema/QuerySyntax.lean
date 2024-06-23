/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino, Florian Würmseer
-/

import Lean
import Postgres.DSL.Schema.QueryDSL

open Lean Elab Meta Term

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

declare_syntax_cat           literal
syntax num                 : literal
syntax "-" noWs num        : literal
syntax str                 : literal
syntax scientific          : literal
syntax "-" noWs scientific : literal
syntax "NULL"              : literal
syntax "(" literal ")"       : literal

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
syntax parsId propSymbol literal  : prop
syntax literal  propSymbol literal  : prop
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
declare_syntax_cat                                      sqlQuery

syntax ident                                          : sqlFrom
syntax sqlFrom ", " sqlFrom                           : sqlFrom
syntax sqlFrom " AS " ident                           : sqlFrom
syntax sqlFrom join " JOIN " sqlFrom " ON " prop      : sqlFrom
syntax sqlFrom join " JOIN " sqlFrom " USING " parsId : sqlFrom
syntax "(" sqlFrom ")"                                : sqlFrom
syntax "(" sqlQuery ")"                               : sqlFrom

syntax "SELECT " sqlSelect " FROM " sqlFrom (" WHERE " prop)? : sqlQuery

syntax (name := pgquery) "queryOn" ident " | " sqlQuery : term

structure QueryState :=
  expr : Expr
  tag : Option String := none
  tableAlias : HashMap String (HashSet String) := HashMap.empty
  fieldProj : Option Expr := none
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
  | `(parsId|$id:ident)      => pure $ mkStrLit id.getId.toString
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
    mkAppM `SQLSelectField.alias #[← elabStrOfParsId c, mkStrLit a.getId.toString]
  | _                                    => throwUnsupportedSyntax

def findFieldsInTable : List Field → String → SchemaTermElabM (List Field) :=
  fun table id => do
    let state ← get
    let sections := id.splitOn "."
    if sections.length > 1 then
      let (pfx, sfx) := sections.splitAt <| sections.length - 1
      let key := ".".intercalate pfx
      let aliases := match state.tableAlias.find? key with
        -- get! 0 is safe because of the invariant: length > 1 ∧ splitAt length-1 with 0 has sfx length 1, splitAt length-1 with n+1 has unchanged suffix.
        | some v => v.fold (fun l s => l ++ table.filter (fun f : Field => f.getName == s!"{s}.{sfx.get! 0}" || (f.getName.splitOn ".").length == 1 && f.getName == sfx.get! 0)) []
        | none => []
      let direct : List Field := match table.filter (fun f => f.getName == id) with
        | [] => aliases
        | l  => l
      pure direct
    else
      let direct : List Field := match table.find? (fun f => f.getName == id) with
        | some v => [v]
        | none => table.filter (fun f => (f.getName.splitOn ".").getLast! == id)
      pure direct

def getListFromExpr : Expr → SchemaTermElabM (List Field) := fun x => do
  if let .some styp := x.listLit? then
    styp.snd.mapM exprToField
  else
    throwUnsupportedSyntax

def elabProjType (cols : List (TSyntax `selectField)): SchemaTermElabM Expr := do
  let state ← get
  let mut selType : List Field := []
  let mut projType : List Field := []
  let exprs ← getListFromExpr state.expr
  if cols.isEmpty then
    throwError s!"Cannot select from an empty Table"
  for typ in cols do
    match typ with
      | `(selectField|$c:parsId) => do
        let id := parsIdToString c
        let selId := (← findFieldsInTable exprs id)
        selType := selType ++ selId
        projType := projType ++ selId
        if selId.isEmpty then
          throwError s!"Cannot select Field {id} from Table {exprs}"
      | `(selectField|$c:parsId AS $a:ident) => do
        let id := parsIdToString c
        let al := a.getId.toString
        let selId := (← findFieldsInTable exprs id)
        let proj := selId.map (Field.setName . al)
        projType := projType ++ proj
        selType := selType ++ selId
        if selId.isEmpty then
          throwError s!"Cannot select Field {id} from Table {exprs}"
      | _ => throwUnsupportedSyntax
  let fieldProj ← mkListLit (mkConst `Field) (← projType.mapM elabField)
  if selType != projType then
    set { state with fieldProj := fieldProj }
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

def elabConst (name : Name) : TermElabM Expr :=
  pure $ mkConst name

def negFloat (f : Float) : Float :=
  -1.0 * f

partial def elabLiteral : TSyntax `literal → TermElabM Expr
  | `(literal|$v:num)         =>
    mkAppM `Literal.int #[mkApp (mkConst `Int.ofNat) (mkNatLit v.getNat)]
  | `(literal|-$v:num)        =>
    mkAppM `Literal.int $ match v.getNat with
      | Nat.zero   => #[mkApp (mkConst `Int.ofNat) (mkConst `Nat.zero)]
      | Nat.succ n => #[mkApp (mkConst `Int.negSucc) (mkNatLit n)]
  | `(literal|$v:scientific)  => do
    mkAppM `Literal.int #[← Term.elabScientificLit v (mkConst `Float)]
  | `(literal|-$v:scientific) => do
    let f ← Term.elabScientificLit v (mkConst `Float)
    mkAppM `Literal.int #[mkApp (mkConst `negFloat) f]
  | `(literal|$v:str)         =>
    mkAppM `Literal.string #[mkStrLit $ v.getString]
  | `(literal|NULL)              => elabConst `DataEntry.ENull
  | `(literal|($e:literal))        => elabLiteral e
  | _                          => throwUnsupportedSyntax

def elabPropSymbol (stx : TSyntax `propSymbol) : TermElabM Name :=
  match stx with
  | `(propSymbol|=)  => pure `SQLProp.eq
  | `(propSymbol|<>) => pure `SQLProp.ne
  | `(propSymbol|!=) => pure `SQLProp.ne
  | `(propSymbol|<)  => pure `SQLProp.lt
  | `(propSymbol|<=) => pure `SQLProp.le
  | `(propSymbol|>)  => pure `SQLProp.gt
  | `(propSymbol|>=) => pure `SQLProp.ge
  | _                => throwUnsupportedSyntax

def elabParsId : TSyntax `parsId → SchemaTermElabM Expr
  | p => do
    let state := ← get
    let id := parsIdToString p
    let fields ← getListFromExpr state.expr
    let selIds := (← findFieldsInTable fields id)
    if selIds.length > 2 then
      throwError s!"The identifyer {id} in your WHERE clause must be unabiguous. Can refer to any of {selIds}"
    if selIds.length = 2 && !(selIds.get! 0).ofSameType (selIds.get! 1) then
      throwError s!"Cannot compare Fields {selIds}"
    let selId := selIds.get! 0
    pure <| mkApp (mkConst `Literal.field) <| ← elabField selId

partial def elabProp : TSyntax `prop → SchemaTermElabM Expr
  | `(prop|TRUE)                              => elabConst `SQLProp.tt
  | `(prop|FALSE)                             => elabConst `SQLProp.ff
  | `(prop|$l:parsId $s:propSymbol $r:parsId) => do
    let rhsLit  ← elabParsId l
    let propSymbol ← mkConst <| ← elabPropSymbol s
    let lhsLit ← elabParsId r
    elabAppArgs propSymbol #[] #[Arg.expr lhsLit, Arg.expr rhsLit] .none (explicit := false) (ellipsis := false)
  | `(prop|$c:parsId $s:propSymbol $e:literal)  => do
    let rhsLit  ← elabParsId c
    let propSymbol ← mkConst <| ← elabPropSymbol s
    let lhsLit ← elabLiteral e
    elabAppArgs propSymbol #[] #[Arg.expr lhsLit, Arg.expr rhsLit] .none (explicit := false) (ellipsis := false)
  | `(prop|$l:literal $s:propSymbol $r:literal)  => do
    let lhsLit ← elabLiteral l
    let rhsLit  ← elabLiteral r
    let propSymbol ← mkConst <| ← elabPropSymbol s
    elabAppArgs propSymbol #[] #[Arg.expr lhsLit, Arg.expr rhsLit] .none (explicit := false) (ellipsis := false)
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
    let typ ← whnf (mkApp state.expr (mkStrLit t.getId.toString))
    -- Set State for Tagging
    set { state with expr := typ, tag := tableName, tables := state.tables.insert tableName }
    -- Remove
    let _ ← tagFromList
    pure <| mkApp2 (mkConst `SQLFrom.table) (← get).expr (mkStrLit t.getId.toString)
  | `(sqlFrom|$f:sqlFrom AS $t:ident) => do
    let frm ← elabFrom f
    let state ← get
    set { state with tableAlias := state.tableAlias.insert t.getId.toString state.tables }
    pure <| mkApp3 (mkConst `SQLFrom.alias) (← get).expr (frm) (mkStrLit t.getId.toString)
  | `(sqlFrom|$l:sqlFrom, $r:sqlFrom) => do
    let elabFromFun := elabFrom l |>.run
    let (lfrm, ltyp) ← elabFromFun (← get)
    let rfrm ← elabFrom r
    let rtyp ← get
    let typ ← concatFrom ltyp rtyp
    elabAppArgs (mkApp3 (mkConst `SQLFrom.implicitJoin) ltyp.expr rtyp.expr typ) #[] #[Arg.expr lfrm, Arg.expr rfrm] .none (explicit := false) (ellipsis := false)
  | `(sqlFrom|$l:sqlFrom $j:join JOIN $r:sqlFrom ON $p:prop) => do
    let (lfrm, lstate) ← elabFrom l |>.run (← get)
    let rfrm ← elabFrom r
    let rstate ← get
    let typ ← concatFrom lstate rstate
    set { ← get with tables := lstate.tables.merge rstate.tables, tableAlias := lstate.tableAlias.mergeWith (fun _ _ b => b) rstate.tableAlias}
    elabAppArgs (mkApp3 (mkConst `SQLFrom.join) lstate.expr rstate.expr typ) #[] #[Arg.expr (← elabJoin j), Arg.expr lfrm, Arg.expr rfrm, Arg.expr (← elabProp p)] .none (explicit := false) (ellipsis := false)
  | `(sqlFrom|$l:sqlFrom $j:join JOIN $r:sqlFrom USING $p:parsId) => do
    let (lfrm, ltyp) ← elabFrom l |>.run (← get)
    let rfrm ← elabFrom r
    let rtyp ← get
    let typ ← concatFrom ltyp rtyp
    pure <| mkApp4 (mkApp3 (mkConst `SQLFrom.joinUsing) ltyp.expr rtyp.expr typ) (← elabJoin j) lfrm rfrm (← elabStrOfParsId p)
  | `(sqlFrom|($f:sqlFrom))           => do
    elabFrom f
  | `(sqlFrom| ($query:sqlQuery)) => do
    let qry ← elabQuery query
    pure <| mkApp2 (mkConst `SQLFrom.nestedJoin) (← get).expr qry
  | _                                 => throwUnsupportedSyntax

partial def elabQuery : TSyntax `sqlQuery → SchemaTermElabM Expr
  | `(sqlQuery| SELECT $sel FROM $frm:sqlFrom $[WHERE $prp]?) => do
    let state ← get
    let (frm, ftyp) ← elabFrom frm |>.run state
    let ftyp := { ftyp with tag := .none }
    set ftyp
    let whr ← match prp with
      | none     => elabConst `SQLProp.tt
      | some prp => elabProp prp
    let (sel, styp) ← elabSelect sel |>.run (← get)
    set styp
    let expr := mkApp4 (mkConst `SQLQuery.mk) styp.expr ftyp.expr sel frm
    let query ← elabAppArgs expr #[] #[Arg.expr whr] .none (explicit := false) (ellipsis := false)
    if let some fTyp := styp.fieldProj then
      set { styp with expr := fTyp }
      pure <| mkApp3 (mkConst `SQLQuery.proj) styp.expr query fTyp
    else
      pure query
  | _ => throwUnsupportedSyntax
end

namespace QuerySyntax

elab_rules : term
  | `(pgquery| queryOn $schema | $query) => do
    let env ← getEnv
    if let .some s := env.find? schema.getId then
      let (query, _) ← elabQuery query |>.run { expr := s.value! }
      pure query
    else
      throwUnsupportedSyntax
