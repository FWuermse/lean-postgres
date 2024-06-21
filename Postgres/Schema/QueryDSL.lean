/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino, Florian Würmseer
-/

import Postgres.Schema.Literal
import Postgres.Schema.InsertDSL

inductive SQLSelectField
  | col   : String → SQLSelectField
  | alias : String → String         → SQLSelectField

inductive SQLSelect (α : List Field)
  | list : Bool → List SQLSelectField → SQLSelect α
  | all  : Bool → SQLSelect α

inductive RawSQLSelect
  | list : Bool → List SQLSelectField → RawSQLSelect
  | all  : Bool → RawSQLSelect

-- Relation über AST dass feld vom typen ist
inductive SQLProp
  | tt  : SQLProp
  | ff  : SQLProp
  | eq (l r : Literal) : (h: l.interp = r.interp := by rfl) → SQLProp
  | ne (l r : Literal) : (h: l.interp = r.interp := by rfl) → SQLProp
  | lt (l r : Literal) : (h: l.interp = r.interp := by rfl) → SQLProp
  | le (l r : Literal) : (h: l.interp = r.interp := by rfl) → SQLProp
  | gt (l r : Literal) : (h: l.interp = r.interp := by rfl) → SQLProp
  | ge (l r : Literal) : (h: l.interp = r.interp := by rfl) → SQLProp
  | and : SQLProp → SQLProp   → SQLProp
  | or  : SQLProp → SQLProp   → SQLProp
  | not : SQLProp → SQLProp

def x := SQLProp.eq (Literal.int 3) (Literal.field <| Field.nat "")

inductive SQLJoin
  | inner | left | right | outer

mutual
inductive SQLFrom : List Field → Type
  | table        : String → SQLFrom α
  | alias        : SQLFrom α → String  → SQLFrom α
  | join         : SQLJoin → SQLFrom α → SQLFrom β → SQLProp → (h: γ = α ++ β := by simp) → SQLFrom γ
  | implicitJoin : SQLFrom α → SQLFrom β → (h: γ = α ++ β := by simp) → SQLFrom γ
  | nestedJoin   : SQLQuery α → SQLFrom α

inductive SQLQuery : List Field → Type
  | mk : SQLSelect α → SQLFrom β → SQLProp → (h: α ⊆ β := by simp) →  SQLQuery α
  | proj : SQLQuery β → (α : List Field) → SQLQuery α
end

inductive RawSQLFrom
  | table        : String  → RawSQLFrom
  | alias        : RawSQLFrom → String  → RawSQLFrom
  | join         : SQLJoin → RawSQLFrom → RawSQLFrom → SQLProp → RawSQLFrom
  | implicitJoin : RawSQLFrom → RawSQLFrom → RawSQLFrom

inductive RawSQLQuery where
  | mk : RawSQLSelect → RawSQLFrom → SQLProp → RawSQLQuery
  | nstd : RawSQLSelect → RawSQLQuery → SQLProp → RawSQLQuery

def SQLSelectField.toString : SQLSelectField → String
  | col   c   => c
  | .alias c a => s!"{c} AS {a}"

instance : ToString (SQLSelectField) := ⟨SQLSelectField.toString⟩

def SQLSelect.distinct? (d : Bool) : String :=
  if d then "DISTINCT " else default

def SQLSelect.toString : SQLSelect α → String
  | list d l => (distinct? d).append $ ", ".intercalate $ l.map (SQLSelectField.toString)
  | all  d   => (distinct? d).append $ "*"

instance : ToString (SQLSelect α) := ⟨SQLSelect.toString⟩

def SQLProp.toString : SQLProp → String
  | tt      => "TRUE"
  | ff      => "FALSE"
  | eq l r _ => s!"{l} = {r}"
  | ne  l r _ => s!"{l} <> {r}"
  | lt  l r _ => s!"{l} < {r}"
  | le  l r _ => s!"{l} <= {r}"
  | gt  l r _ => s!"{l} > {r}"
  | ge  l r _ => s!"{l} >= {r}"
  | and l r => s!"({l.toString}) AND ({r.toString})"
  | or  l r  => s!"({l.toString}) OR ({r.toString})"
  | not w   => s!"NOT ({w.toString})"

instance : ToString SQLProp := ⟨SQLProp.toString⟩

def SQLJoin.toString : SQLJoin → String
  | inner => "INNER"
  | left  => "LEFT"
  | right => "RIGHT"
  | outer => "OUTER"

instance : ToString SQLJoin := ⟨SQLJoin.toString⟩

mutual
def SQLFrom.toString : SQLFrom α → String
  | SQLFrom.table s              => s
  | SQLFrom.alias f s            => s!"({f.toString}) AS {s}"
  | SQLFrom.join j l r p _       => s!"{l.toString} {j} JOIN {r.toString} ON {p}"
  | SQLFrom.implicitJoin t₁ t₂ _ => s!"{t₁.toString}, {t₂.toString}"
  | SQLFrom.nestedJoin q         => q.toString

def SQLQuery.toString : SQLQuery α → String
  | SQLQuery.mk s f w _ => s!"SELECT {s} FROM {f.toString} WHERE {w}"
  | SQLQuery.proj q _ => s!"{q.toString}"
end

instance : ToString (SQLFrom α) := ⟨SQLFrom.toString⟩

instance : ToString (SQLQuery α) := ⟨SQLQuery.toString⟩
