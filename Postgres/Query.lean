/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer, Jannis Limperg
-/

import Socket
import Lean
import Postgres.Postgres
import Postgres.Response

open Socket Connect Lean Meta Elab Elab.Term QueryResponse

namespace Query

inductive Col where
  | as : String → String → Col
  | col : String → Col

instance : ToString Col where
  toString
    | Col.col str => str
    | Col.as s1 s2 => s1 ++ " AS " ++ s2

inductive Tbl where
  | alias : String → String → Tbl
  | tbl : String → Tbl

instance : ToString Tbl where
  toString col := match col with
    | Tbl.tbl str => str
    | Tbl.alias s1 s2 => s1 ++ " " ++ s2

structure FieldDesc where
  distinct : Bool
  cols : Array Col

private def joinSep (sep : String) (ss : Array String) : String :=
  let firstNonempty? := ss.findIdx? (! ·.isEmpty)
  match firstNonempty? with
  | none => ""
  | some firstNonempty =>
    ss.foldl (start := firstNonempty + 1) (init := ss[firstNonempty]) λ res s =>
      if s.isEmpty then res else res ++ sep ++ s

instance : ToString FieldDesc where
  toString fieldDesc :=
    let distinct := if fieldDesc.distinct then "DISTINCT " else ""
    let fields := fieldDesc.cols.map toString |> joinSep ", "
    distinct ++ fields

inductive Select where
  | all
  | cols : FieldDesc → Select

instance : ToString Select where
  toString select := match select with
    | Select.all => "*"
    | Select.cols fd => toString fd

inductive BinOp where
  | and
  | or

instance : ToString BinOp where
  toString binOp := match binOp with
    | BinOp.and => "AND"
    | BinOp.or => "OR"

inductive SqlExpr
  | bool (b : Bool)
  | binOp (l : SqlExpr) (o : BinOp) (r : SqlExpr)

namespace SqlExpr

protected def toString : SqlExpr → String
  | bool true => "TRUE"
  | bool false => "FALSE"
  | binOp l o r => s!"({SqlExpr.toString l}) {o} ({SqlExpr.toString r})"

instance : ToString SqlExpr :=
  ⟨SqlExpr.toString⟩

end SqlExpr

structure Whr where
  pred : SqlExpr

instance : ToString Whr where
  toString whr := s!"WHERE {whr.pred}"

structure Query where
  select : Select
  frm : Array Tbl
  /--
  TODO:
  whr : Option Whr := none
  groupBy : Option String := none
  having : Option String := none
  limit : Option String := none -/

instance : ToString Query where
  toString q :=
    let frm := q.frm.map toString |> joinSep ", "
    s!"SELECT {q.select} FROM {frm};"

syntax col := str ("AS" str)?

declare_syntax_cat tbl
syntax str : tbl
syntax str str : tbl

syntax fieldDesc := "DISTINCT "? col,+

declare_syntax_cat select
syntax "*" : select
syntax fieldDesc : select

declare_syntax_cat bin_op
syntax "AND" : bin_op
syntax "OR" : bin_op

declare_syntax_cat expr
syntax "TRUE" : expr
syntax "FALSE" : expr
syntax expr bin_op expr : expr -- not sure if this needs to be factored for left-recursion

syntax query := "SELECT " select "FROM " tbl,+ ("WHERE " expr)?

syntax (name := sql) query ";" : term

private def elabStrLit (stx : Syntax) : TermElabM Expr :=
  match stx.isStrLit? with
  | some val => pure $ mkStrLit val
  | none => throwIllFormedSyntax

def elabCol : Syntax → TermElabM Expr
  | `(col| $x:strLit AS $y:strLit) => do
    mkAppM ``Col.as #[← elabStrLit x, ← elabStrLit y]
  | `(col| $x:strLit) => do
    mkAppM ``Col.col #[← elabStrLit x]
  | _ => throwIllFormedSyntax

def elabTbl : Syntax → TermElabM Expr
  | `(tbl| $x:strLit $y:strLit) => do
    mkAppM ``Tbl.alias #[← elabStrLit x, ← elabStrLit y]
  | `(tbl| $x:strLit) => do
    mkAppM ``Tbl.tbl #[← elabStrLit x]
  | _ => throwIllFormedSyntax

def elabFieldDesc : Syntax → TermElabM Expr
  | `(fieldDesc| DISTINCT $cs:col,*) => go true cs
  | `(fieldDesc| $cs:col,*) => go false cs
  | _ => throwIllFormedSyntax
  where
    go (distinct : Bool) (cs : Array Syntax) : TermElabM Expr := do
      let cols ← mkArrayLit (mkConst ``Col) (← cs.mapM elabCol).toList
      let distinct :=
        if distinct then Lean.mkConst ``true else Lean.mkConst ``false
      mkAppM ``FieldDesc.mk $ #[distinct, cols]

def elabSelect : Syntax → TermElabM Expr
  | `(select| *) => mkConst ``Select.all
  | `(select| $d:fieldDesc) => do mkAppM ``Select.cols #[← elabFieldDesc d]
  | _ => throwIllFormedSyntax

def elabBinOp : Syntax → TermElabM Expr
  | `(bin_op| AND) => return mkConst ``BinOp.and
  | `(bin_op| OR) => return mkConst ``BinOp.or
  | _ => throwIllFormedSyntax

partial def elabSqlExpr : Syntax → TermElabM Expr
  | `(expr| TRUE ) => return mkApp (mkConst ``SqlExpr.bool) (mkConst ``true)
  | `(expr| FALSE) => return mkApp (mkConst ``SqlExpr.bool) (mkConst ``false)
  | `(expr| $e₁:expr $o:bin_op $e₂:expr) => do
    mkAppM ``SqlExpr.binOp #[← elabSqlExpr e₁, ← elabBinOp o, ← elabSqlExpr e₂]
  | _ => throwIllFormedSyntax

@[termElab sql]
def elabSql : TermElab := λ stx _ =>
  match stx with
  | `(sql| SELECT $s:select FROM $ts:tbl,* $[WHERE $p:expr]?;) => do
    let select ← elabSelect s
    let frm ← mkArrayLit (mkConst ``Tbl) $
      (← (ts : Array Syntax).mapM elabTbl).toList
    mkAppM ``Query.mk #[select, frm]
  | _ => throwIllFormedSyntax

-- 'Unit test' for elaboration
set_option trace.debug true in
#eval show TermElabM Unit from do
  let stx ← `(SELECT "c₁" AS "c", "c₂" FROM "t₁, t₂" WHERE TRUE OR FALSE;)
  let query ← evalExpr Query ``Query (← elabSql stx none)
  trace[debug] s!"{query}"

def sendQuery (socket : Socket) (query : Query) : IO Section := do
  let req ← socket.send $ toByteArray $ RegularMessage.mk 'Q' (toString query)
  parseQueryResponse socket

end Query
