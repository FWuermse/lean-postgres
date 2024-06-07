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
syntax ident                                          : sqlFrom
syntax sqlFrom ", " sqlFrom                           : sqlFrom
syntax sqlFrom " AS " ident                           : sqlFrom
syntax sqlFrom join " JOIN " sqlFrom " ON " prop      : sqlFrom
syntax sqlFrom join " JOIN " sqlFrom " USING " parsId : sqlFrom
syntax "(" sqlFrom ")"                                : sqlFrom

declare_syntax_cat                                                      query
syntax "SELECT " sqlSelect " FROM " sqlFrom (" WHERE " prop)?         : query
syntax "SELECT " sqlSelect " FROM " "(" query ")" (" WHERE " prop)?   : query
syntax "SELECT " sqlSelect " FROM " "(" ident ")" (" WHERE " prop)?   : query

syntax (name := pgquery) "queryOn" ident " | " query : term

def mkStrOfIdent (id : Syntax) : Expr :=
  mkStrLit id.getId.toString

abbrev SchemaTermElabM := StateRefT Expr TermElabM

def exprToField : Expr → SchemaTermElabM Field
  | Expr.app ctor (Expr.lit <| Literal.strVal s) => match ctor with
      | (Expr.const `Field.nat _) => pure (Field.nat s)
      | Expr.app (Expr.const `Field.varchar _) numExpr => do
        if let .some nat ← getNatValue? numExpr then
          if nat > 255 then
            throwError s!"The maximum value for Varchar is 255, failure on {numExpr} with value {nat}"
          pure (Field.varchar nat s)
        else throwError s!"Unsupported Length param for Varchar {numExpr}"
      | (Expr.const `Field.char _) => pure (Field.char s)
      | (Expr.const `Field.date _) => pure (Field.date s)
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

def elabProjType (cols : List (TSyntax `selectField)): SchemaTermElabM Expr := do
  let expr ← get
  let mut selType : List Field := []
    if let .some exprs := expr.listLit? then
      let exprs ← exprs.snd.mapM exprToField
      if cols.isEmpty then
        throwError s!"Cannot select from an empty Table"
      for typ in cols do
        match typ with
          | `(selectField|$c:parsId) => do
            let id := parsIdToString c
            if let .some field := exprs.find? (fun f => f.getName == id) then
              selType := selType.append [field]
            else
              throwError s!"Cannot select Field {id} from Table {exprs}"
          | `(selectField|$c:parsId AS $_) => do
            let id := parsIdToString c
            if let .some field := exprs.find? (fun f => f.getName == id) then
              selType := selType.append [field]
            else
              throwError s!"Cannot select Field {id} from Table {exprs}"
          | _ => throwUnsupportedSyntax
    else
      throwUnsupportedSyntax
    mkListLit (mkConst `Field) (← selType.mapM elabField)

def elabSelect : TSyntax `sqlSelect → SchemaTermElabM Expr
  | `(sqlSelect|*)                          => do
    pure <| mkApp2 (mkConst ``SQLSelect.all) (← get) (mkConst ``false)
  | `(sqlSelect|DISTINCT *)                 => do
    -- TODO make distinct
    pure <| mkApp2 (mkConst `SQLSelect.all) (← get) (mkConst ``true)
  | `(sqlSelect|$cs:selectField,*)          => do
    let cols ← mkListLit (mkConst `SQLSelectField) (← cs.getElems.toList.mapM elabCol)
    let typ ← elabProjType cs.getElems.toList
    set typ
    pure <| mkApp3 (mkConst `SQLSelect.list) typ (mkConst ``false) (cols)
  | `(sqlSelect|DISTINCT $cs:selectField,*) => do
    let cols ← mkListLit (mkConst `SQLSelectField) (← cs.getElems.toList.mapM elabCol)
    let typ ← elabProjType cs.getElems.toList.eraseDup
    set typ
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

def elabJoin : Syntax → TermElabM Expr
  | `(join|INNER) => elabConst `SQLJoin.inner
  | `(join|LEFT)  => elabConst `SQLJoin.left
  | `(join|RIGHT) => elabConst `SQLJoin.right
  | `(join|OUTER) => elabConst `SQLJoin.outer
  | _             => throwUnsupportedSyntax

partial def elabFrom : TSyntax `sqlFrom → SchemaTermElabM Expr
  | `(sqlFrom|$t:ident)               => do
    let ctx ← get
    let typ ← whnf (mkApp ctx (mkStrOfIdent t))
    set typ
    pure <| mkApp2 (mkConst `SQLFrom.table [1]) typ (mkStrOfIdent t)
  | `(sqlFrom|$f:sqlFrom AS $t:ident) => do
    let frm ← elabFrom f
    pure <| mkApp3 (mkConst `SQLFrom.alias [1]) (← get) (frm) (mkStrOfIdent t)
  | `(sqlFrom|$l:sqlFrom, $r:sqlFrom) => do
    let (lfrm, ltyp) ← (elabFrom l).run (← get)
    let rfrm ← elabFrom r
    let rtyp ← get
    if let .some rtyps := rtyp.listLit? then
      if let .some ltyps := ltyp.listLit? then
        let rfields ← rtyps.snd.mapM exprToField
        let lfields ← ltyps.snd.mapM exprToField
        let typ ← (rfields.append lfields).mapM elabField
        let typ ← mkListLit (mkConst `Field) typ
        set typ
        pure <| mkApp2 (mkApp3 (mkConst `SQLFrom.implicitJoin [1]) ltyp rtyp typ) lfrm rfrm
      else
        throwUnsupportedSyntax
    else
      throwUnsupportedSyntax
  | `(sqlFrom|$l:sqlFrom $j:join JOIN $r:sqlFrom ON $p:prop) => do
    let (lfrm, ltyp) ← (elabFrom l).run (← get)
    let rfrm ← elabFrom r
    let rtyp ← get
    if let .some rtyps := rtyp.listLit? then
      if let .some ltyps := ltyp.listLit? then
        let rfields ← rtyps.snd.mapM exprToField
        let lfields ← ltyps.snd.mapM exprToField
        let typ ← (rfields.append lfields).mapM elabField
        let typ ← mkListLit (mkConst `Field) typ
        set typ
        pure <| mkApp4 (mkApp3 (mkConst `SQLFrom.join [1]) ltyp rtyp typ) (← elabJoin j) lfrm rfrm (← elabProp p)
      else
        throwUnsupportedSyntax
    else
      throwUnsupportedSyntax
  | `(sqlFrom|$l:sqlFrom $j:join JOIN $r:sqlFrom USING $p:parsId) => do
    IO.println "TODO"
    throwUnsupportedSyntax
  | `(sqlFrom|($f:sqlFrom))           => elabFrom f
  | _                                 => throwUnsupportedSyntax

partial def elabQuery : TSyntax `query → SchemaTermElabM Expr
  | `(query| SELECT $sel FROM $frm:sqlFrom $[WHERE $prp]?) => do
    let whr ← match prp with
      | none     => elabConst `SQLProp.tt
      | some prp => elabProp prp
    let ctx ← get
    let (frm, ftyp) ← (elabFrom frm).run ctx
    set ftyp
    let (sel, styp) ← (elabSelect sel).run (← get)
    set styp
    let expr := mkApp4 (mkConst `SQLQuery.mk [1]) styp ftyp sel frm
    let query ← elabAppArgs expr #[] #[Arg.expr whr] .none (explicit := false) (ellipsis := false)
    pure query
  | `(query| SELECT $sel FROM ($query:query) $[WHERE $prp]?) => do
   let whr ← match prp with
      | none     => elabConst `SQLProp.tt
      | some prp => elabProp prp
    let ctx ← get
    let (qry, qtyp) ← (elabQuery query).run ctx
    set qtyp
    let (sel, styp) ← (elabSelect sel).run (← get)
    set styp
    let expr := mkApp4 (mkConst `SQLQuery.nstd [1]) styp qtyp sel qry
    let query ← elabAppArgs expr #[] #[Arg.expr whr] .none (explicit := false) (ellipsis := false)
    pure query
  | `(query| SELECT $sel FROM ($id:ident) $[WHERE $prp]?) => do
    IO.println "TODO"
    throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

@[term_elab pgquery] def elabPQQuery : TermElab := fun stx _ =>
  match stx with
  | `(pgquery| queryOn $schema | $query) => do
    let env ← getEnv
    if let .some s := env.find? schema.getId then
      let (query, _) ← (elabQuery query).run s.value!
      pure query
    else
      throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

def schema : String → List Field
  | "myTable" => [Field.nat "id", Field.nat "name"]
  | "otherTable" => [Field.nat "id", Field.date "date"]
  | _ => []

def nested := queryOn QuerySyntax.schema |
  SELECT *
  FROM (SELECT id
        FROM (SELECT *
              FROM myTable))
def join := queryOn QuerySyntax.schema | SELECT name, date FROM myTable INNER JOIN otherTable ON myTable.id = otherTable.id
def implicitJoin := queryOn QuerySyntax.schema |
  SELECT name AS nm, date
  FROM myTable, otherTable
  WHERE myTable.id = otherTable.id
--def empty := queryOn QuerySyntax.schema | SELECT a FROM myTable

def s : String → List Field
  | "information_schema.tables" => [Field.varchar 255 "table_name", Field.nat "dummy"]
  | _ => []

def query := queryOn QuerySyntax.s |
  SELECT table_name
  FROM information_schema.tables
  WHERE table_schema = "public"
    AND table_type = "BASE TABLE"
