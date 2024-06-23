/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino, Florian Würmseer
-/

import Lean
import Postgres.DSL.QueryDSL

open Lean Elab Meta

declare_syntax_cat      parsIdU
syntax ident          : parsIdU
syntax "(" parsIdU ")" : parsIdU

declare_syntax_cat           selectFieldU
syntax parsIdU              : selectFieldU
syntax parsIdU " AS " ident : selectFieldU

declare_syntax_cat                 sqlSelectU
syntax "*"                       : sqlSelectU
syntax "DISTINCT " "*"           : sqlSelectU
syntax selectFieldU,+             : sqlSelectU
syntax "DISTINCT " selectFieldU,+ : sqlSelectU

declare_syntax_cat           entry
syntax num                 : entry
syntax "-" noWs num        : entry
syntax str                 : entry
syntax scientific          : entry
syntax "-" noWs scientific : entry
syntax "NULL"              : entry
syntax "(" entry ")"       : entry

declare_syntax_cat propUSymbol
syntax " = "     : propUSymbol
syntax " <> "    : propUSymbol
syntax " != "    : propUSymbol
syntax " < "     : propUSymbol
syntax " <= "    : propUSymbol
syntax " > "     : propUSymbol
syntax " >= "    : propUSymbol

declare_syntax_cat                propU
syntax "TRUE"                   : propU
syntax "FALSE"                  : propU
syntax parsIdU propUSymbol parsIdU : propU
syntax parsIdU propUSymbol entry  : propU
syntax propU " AND " propU        : propU
syntax propU " OR "  propU        : propU
syntax " NOT " propU             : propU
syntax "(" propU ")"             : propU

declare_syntax_cat joinU
syntax " INNER " : joinU
syntax " LEFT "  : joinU
syntax " RIGHT " : joinU
syntax " OUTER " : joinU

declare_syntax_cat                                 sqlFromU
syntax ident                                     : sqlFromU
syntax sqlFromU ", " sqlFromU                      : sqlFromU
syntax sqlFromU " AS " ident                      : sqlFromU
syntax sqlFromU joinU " JOIN " sqlFromU " ON " propU : sqlFromU
syntax "(" sqlFromU ")"                           : sqlFromU

syntax (name := query) "query |" "SELECT " sqlSelectU " FROM " sqlFromU (" WHERE " propU)? : term

def mkStrOfIdent (id : Syntax) : Expr :=
  mkStrLit id.getId.toString

partial def elabStrOfParsIdU : Syntax → TermElabM Expr
  | `(parsIdU|$id:ident)      => pure $ mkStrLit id.getId.toString
  | `(parsIdU|($pars:parsIdU)) => elabStrOfParsIdU pars
  | _                        => throwUnsupportedSyntax

def elabColU : TSyntax `selectFieldU → TermElabM Expr
  | `(selectFieldU|$c:parsIdU)             => do
    mkAppM ``SQLSelectField.col #[← elabStrOfParsIdU c]
  | `(selectFieldU|$c:parsIdU AS $a:ident) => do
    mkAppM ``SQLSelectField.alias #[← elabStrOfParsIdU c, mkStrOfIdent a]
  | _                                    => throwUnsupportedSyntax

def elabSelectU : Syntax → TermElabM Expr
  | `(sqlSelectU|*)                          => mkAppM ``SQLUntypedSelect.all #[mkConst ``false]
  | `(sqlSelectU|DISTINCT *)                 => mkAppM ``SQLUntypedSelect.all #[mkConst ``true]
  | `(sqlSelectU|$cs:selectFieldU,*)          => do
    let cols ← mkListLit (mkConst ``SQLSelectField) (← cs.getElems.toList.mapM elabColU)
    mkAppM ``SQLUntypedSelect.list #[mkConst ``false, cols]
  | `(sqlSelectU|DISTINCT $cs:selectFieldU,*) => do
    let cols ← mkListLit (mkConst `SQLSelectField) (← cs.getElems.toList.mapM elabColU)
    mkAppM ``SQLUntypedSelect.list #[mkConst ``true, cols]
  | _                                       => throwUnsupportedSyntax

def mkApp' (name : Name) (e : Expr) : Expr :=
  mkApp (mkConst name) e

def negFloatU (f : Float) : Float :=
  -1.0 * f

partial def elabEntryU : TSyntax `entry → TermElabM Expr
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
  | `(entry|NULL)              => pure <| mkConst `DataEntry.ENull
  | `(entry|($e:entry))        => elabEntryU e
  | _                          => throwUnsupportedSyntax

def elabPropSymbolU (stx : Syntax) (isEntry : Bool) : TermElabM Name :=
  match stx with
  | `(propUSymbol|=)  => pure $ if isEntry then ``SQLUntypedProp.eqE else `SQLUntypedProp.eqC
  | `(propUSymbol|<>) => pure $ if isEntry then ``SQLUntypedProp.neE else `SQLUntypedProp.neC
  | `(propUSymbol|!=) => pure $ if isEntry then ``SQLUntypedProp.neE else `SQLUntypedProp.neC
  | `(propUSymbol|<)  => pure $ if isEntry then ``SQLUntypedProp.ltE else `SQLUntypedProp.ltC
  | `(propUSymbol|<=) => pure $ if isEntry then ``SQLUntypedProp.leE else `SQLUntypedProp.leC
  | `(propUSymbol|>)  => pure $ if isEntry then ``SQLUntypedProp.gtE else `SQLUntypedProp.gtC
  | `(propUSymbol|>=) => pure $ if isEntry then ``SQLUntypedProp.geE else `SQLUntypedProp.geC
  | _                => throwUnsupportedSyntax

partial def elabPropU : Syntax → TermElabM Expr
  | `(propU|TRUE)                              => pure <| mkConst ``SQLUntypedProp.tt
  | `(propU|FALSE)                             => pure <| mkConst ``SQLUntypedProp.ff
  | `(propU|$l:parsIdU $s:propUSymbol $r:parsIdU) => do
    mkAppM (← elabPropSymbolU s false) #[← elabStrOfParsIdU l, ← elabStrOfParsIdU r]
  | `(propU|$c:parsIdU $s:propUSymbol $e:entry)  => do
    mkAppM (← elabPropSymbolU s true) #[← elabStrOfParsIdU c, ← elabEntryU e]
  | `(propU|$l:propU AND $r:propU)               => do
    mkAppM ``SQLUntypedProp.and #[← elabPropU l, ← elabPropU r]
  | `(propU|$l:propU OR $r:propU)                => do
    mkAppM ``SQLUntypedProp.or #[← elabPropU l, ← elabPropU r]
  | `(propU|NOT $p:propU)                       => do
    mkAppM ``SQLUntypedProp.not #[← elabPropU p]
  | `(propU|($p:propU))                         => elabPropU p
  | _                                         => throwUnsupportedSyntax

def elabJoinU : Syntax → TermElabM Expr
  | `(joinU|INNER) => pure <| mkConst `SQLJoin.inner
  | `(joinU|LEFT)  => pure <| mkConst `SQLJoin.left
  | `(joinU|RIGHT) => pure <| mkConst `SQLJoin.right
  | `(joinU|OUTER) => pure <| mkConst `SQLJoin.outer
  | _             => throwUnsupportedSyntax

partial def elabFromU : Syntax → TermElabM Expr
  | `(sqlFromU|$t:ident)               => mkAppM ``SQLUntypedFrom.table #[mkStrOfIdent t]
  | `(sqlFromU|$f:sqlFromU AS $t:ident) => do
    mkAppM ``SQLUntypedFrom.alias #[← elabFromU f, mkStrOfIdent t]
  | `(sqlFromU|$t₁:sqlFromU, $t₂:sqlFromU) => do mkAppM ``SQLUntypedFrom.implicitJoin #[← elabFromU t₁, ← elabFromU t₂]
  | `(sqlFromU|$l:sqlFromU $j:joinU JOIN $r:sqlFromU ON $p:propU) => do
    mkAppM ``SQLUntypedFrom.join #[← elabJoinU j, ← elabFromU l, ← elabFromU r, ← elabPropU p]
  | `(sqlFromU|($f:sqlFromU))           => elabFromU f
  | _                                 => throwUnsupportedSyntax

namespace QuerySyntax

elab_rules : term
  | `(query| query | SELECT $sel FROM $frm $[WHERE $prp]?) => do
    let whr ← match prp with
    | none     => pure <| mkConst ``SQLUntypedProp.tt
    | some prp => elabPropU prp
    mkAppM ``SQLUntypedQuery.mk #[← elabSelectU sel, ← elabFromU frm, whr]
