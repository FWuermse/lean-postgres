/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino, Florian Würmseer
-/

import Postgres.Schema.DataEntries
import Postgres.Schema.InsertDSL

inductive Field
  | nat : String → Field
  | varchar (n : Nat) : String → Field
  | char : String → Field
  | date : String → Field
  deriving BEq, Repr, Hashable

def Field.ToString : Field → String
  | nat s => s!"Nat {s}"
  | varchar n s => s!"Varchar {n} {s}"
  | char s => s!"Char {s}"
  | date s => s!"Date {s}"

def Field.getName : Field → String
  | nat s => s
  | varchar _ s => s
  | char s => s
  | date s => s

def Field.setName : Field → String → Field
  | nat _, new => nat new
  | varchar n _, new => varchar n new
  | char _, new => char new
  | date _, new => date new

instance : ToString Field :=
  ⟨Field.ToString⟩

inductive SQLSelectField
  | col   : String → SQLSelectField
  | alias : String → String         → SQLSelectField

inductive SQLSelect (α : List Field)
  | list : Bool → List SQLSelectField → SQLSelect α
  | all  : Bool → SQLSelect α

inductive RawSQLSelect
  | list : Bool → List SQLSelectField → RawSQLSelect
  | all  : Bool → RawSQLSelect

-- TODO: Comparison between typed fields and literals
inductive SQLProp
  | tt : SQLProp
  | ff : SQLProp
  | eqC : String  → String    → SQLProp
  | neC : String  → String    → SQLProp
  | ltC : String  → String    → SQLProp
  | leC : String  → String    → SQLProp
  | gtC : String  → String    → SQLProp
  | geC : String  → String    → SQLProp
  | eqE : String  → DataEntry → SQLProp
  | neE : String  → DataEntry → SQLProp
  | ltE : String  → DataEntry → SQLProp
  | leE : String  → DataEntry → SQLProp
  | gtE : String  → DataEntry → SQLProp
  | geE : String  → DataEntry → SQLProp
  | and : SQLProp → SQLProp   → SQLProp
  | or  : SQLProp → SQLProp   → SQLProp
  | not : SQLProp → SQLProp

inductive SQLJoin
  | inner | left | right | outer

-- TODO: remove Table
mutual
inductive SQLFrom : List Field → Type where
  | table        : String → SQLFrom α
  | alias        : SQLFrom α → String  → SQLFrom α
  | join         : SQLJoin → SQLFrom α → SQLFrom β → SQLProp → (h: γ = α ++ β := by simp) → SQLFrom γ
  | implicitJoin : SQLFrom α → SQLFrom β → (h: γ = α ++ β := by simp) → SQLFrom γ
  | nestedJoin   : SQLQuery α → SQLFrom α

-- Projection as f : SQLQuery → SQLQuery
inductive SQLQuery : List Field → Type where
  | mk : SQLSelect α → SQLFrom β → SQLProp → (h: α ⊆ β := by simp) →  SQLQuery α
end

def a : SQLFrom [Field.nat "hi"] := SQLFrom.table "test"
def b : SQLFrom [Field.nat "bye"] := SQLFrom.table "test2"
def x : SQLFrom [Field.nat "hi", Field.nat "bye"] := SQLFrom.implicitJoin a b

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
  | eqC l r => s!"{l} = {r}"
  | neC l r => s!"{l} <> {r}"
  | ltC l r => s!"{l} < {r}"
  | leC l r => s!"{l} <= {r}"
  | gtC l r => s!"{l} > {r}"
  | geC l r => s!"{l} >= {r}"
  | eqE l r => s!"{l} = {r}"
  | neE l r => s!"{l} <> {r}"
  | ltE l r => s!"{l} < {r}"
  | leE l r => s!"{l} <= {r}"
  | gtE l r => s!"{l} > {r}"
  | geE l r => s!"{l} >= {r}"
  | and l r => s!"({l.toString}) AND ({r.toString})"
  | or  l r => s!"({l.toString}) OR ({r.toString})"
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
  | SQLFrom.table s             => s
  | SQLFrom.alias f s           => s!"({f.toString}) AS {s}"
  | SQLFrom.join j l r p _      => s!"{l.toString} {j} JOIN {r.toString} ON {p}"
  | SQLFrom.implicitJoin t₁ t₂ _ => s!"{t₁.toString}, {t₂.toString}"
  | SQLFrom.nestedJoin q        => q.toString

def SQLQuery.toString : SQLQuery α → String
  | SQLQuery.mk s f w _ => s!"SELECT {s} FROM {f.toString} WHERE {w}"
end

instance : ToString (SQLFrom α) := ⟨SQLFrom.toString⟩

instance : ToString (SQLQuery α) := ⟨SQLQuery.toString⟩
