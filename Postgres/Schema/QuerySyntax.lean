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

declare_syntax_cat                                 sqlFrom
syntax ident                                     : sqlFrom
syntax sqlFrom ", " sqlFrom                      : sqlFrom
syntax sqlFrom " AS " ident                      : sqlFrom
syntax sqlFrom join " JOIN " sqlFrom " ON " prop : sqlFrom
syntax "(" sqlFrom ")"                           : sqlFrom

declare_syntax_cat                                                      query
syntax "SELECT " sqlSelect " FROM " sqlFrom (" WHERE " prop)?         : query
syntax "SELECT " sqlSelect " FROM " "(" query ")" (" WHERE " prop)?   : query

syntax (name := pgquery) "queryOn" ident " | " query : term

def mkStrOfIdent (id : Syntax) : Expr :=
  mkStrLit id.getId.toString

abbrev SchemaTermElabM := StateRefT Expr TermElabM

def exprToField : Expr → SchemaTermElabM Field
  | Expr.app ctor (Expr.lit $ Literal.strVal s) =>
    let res := match ctor with
      | (Expr.const `Field.nat _) => (Field.nat s)
      | (Expr.app (Expr.const `Field.varchar _) (Expr.lit $ Literal.natVal n)) => (Field.varchar n.toUInt8 s)
      | (Expr.const `Field.char _) => (Field.char s)
      | (Expr.const `Field.date _) => (Field.date s)
      | (Expr.const `Field.nil _) => (Field.nil s)
      | _ => Field.nil ""
    return res
  | _ =>
    return Field.nil ""

def elabField : Field → SchemaTermElabM Expr
  | Field.nat s => pure <| mkApp (mkConst `Field.nat) (mkStrLit s)
  | Field.varchar n s => pure <| mkApp2 (mkConst `Field.varchar) (mkNatLit n.toNat) (mkStrLit s)
  | Field.char s => pure <| mkApp (mkConst `Field.char) (mkStrLit s)
  | Field.date s => pure <| mkApp (mkConst `Field.date) (mkStrLit s)
  | Field.nil s => pure <| mkApp (mkConst `Field.nil) (mkStrLit s)


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
      for typ in cols do
        match typ with
          | `(selectField|$c:parsId) => do
            let id := parsIdToString c
            if let .some field := exprs.find? (fun f => f.getName == id) then
              selType := selType.append [field]
          | `(selectField|$c:parsId AS $_) => do
            let id := parsIdToString c
            if let .some field := exprs.find? (fun f => f.getName == id) then
              selType := selType.append [field]
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
    let app ← whnf (mkApp ctx (mkStrOfIdent t))
    set app
    pure <| mkApp2 (mkConst `SQLFrom.table) app (mkStrOfIdent t)
  | `(sqlFrom|$f:sqlFrom AS $t:ident) => do
    mkAppM `SQLFrom.alias #[← elabFrom f, mkStrOfIdent t]
  | `(sqlFrom|$t₁:sqlFrom, $t₂:sqlFrom) => do mkAppM `SQLFrom.implicitJoin #[← elabFrom t₁, ← elabFrom t₂]
  | `(sqlFrom|$l:sqlFrom $j:join JOIN $r:sqlFrom ON $p:prop) => do
    mkAppM `SQLFrom.join #[← elabJoin j, ← elabFrom l, ← elabFrom r, ← elabProp p]
  | `(sqlFrom|($f:sqlFrom))           => elabFrom f
  | _                                 => throwUnsupportedSyntax

partial def elabQuery : TSyntax `query → SchemaTermElabM (Expr × Expr)
  | `(query| SELECT $sel FROM $frm:sqlFrom $[WHERE $prp]?) => do
    let whr ← match prp with
      | none     => elabConst `SQLProp.tt
      | some prp => elabProp prp
    let ctx ← get
    let (frm, ftyp) ← (elabFrom frm).run ctx
    set ftyp
    let (sel, styp) ← (elabSelect sel).run (← get)
    let query := mkApp5 (mkConst `SQLQuery.mk) ftyp styp sel frm whr
    -- TODO why does this need 4 args not 3??
    let pgquery := mkApp4 (mkConst `PGQuery.simple) ftyp styp ftyp query
    set query
    pure (pgquery, styp)
  | `(query| SELECT $sel FROM ($query:query) $[WHERE $prp]?) => do
   let whr ← match prp with
      | none     => elabConst `SQLProp.tt
      | some prp => elabProp prp
    let ctx ← get
    let ((qry, qtyp), rawQry) ← (elabQuery query).run ctx
    let (sel, styp) ← (elabSelect sel).run qtyp
    pure <| (mkApp6 (mkConst `PGQuery.nested) styp qtyp styp sel rawQry whr, qtyp)
  | _ => throwUnsupportedSyntax

@[term_elab pgquery] def elabPQQuery : TermElab := fun stx _ =>
  match stx with
  | `(pgquery| queryOn $schema | $query) => withAutoBoundImplicit do
    let env ← getEnv
    if let .some s := env.find? schema.getId then
      let (query, _) ← (elabQuery query).run s.value!
      pure query.fst
    else
      throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

def schema (table : String) : List Field := match table with
  | "myTable" => [Field.nat "id", Field.nat "name"]
  | "otherTable" => [Field.date "date"]
  | _ => []

def x := queryOn QuerySyntax.schema | SELECT id, name FROM myTable
def y := x

-- TODO outer type must be limited to inner type in respect to '*'
def z := queryOn QuerySyntax.schema | SELECT * FROM ( SELECT id, name FROM myTable )
