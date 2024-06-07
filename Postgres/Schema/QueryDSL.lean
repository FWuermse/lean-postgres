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
  deriving BEq, Repr

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

def Field.interp : Field → Type
  | nat _ => Nat
  | varchar n _ => Varchar n
  | char _ => Char
  | date _ => Date

inductive Table : List Field → Type
  | nil : Table []
  | cons (x : u.interp) (xs : Table us) : Table (u :: us)

def Table.of {us: List Field} (_ : Table us) : List Field := us

inductive SQLFrom : Type → Type (u + 1) where
  | table        : String  → SQLFrom (Table α)
  | alias        : SQLFrom (Table α) → String  → SQLFrom (Table α)
  | join         : SQLJoin → SQLFrom (Table α) → SQLFrom (Table β) → SQLProp → SQLFrom (Table γ)
  | joinUsing    : SQLJoin → SQLFrom (Table α) → SQLFrom (Table β) → DataEntry → SQLFrom (Table γ)
  | implicitJoin : SQLFrom (Table α) → SQLFrom (Table β) → SQLFrom (Table γ)

inductive RawSQLFrom
  | table        : String  → RawSQLFrom
  | alias        : RawSQLFrom → String  → RawSQLFrom
  | join         : SQLJoin → RawSQLFrom → RawSQLFrom → SQLProp → RawSQLFrom
  | implicitJoin : RawSQLFrom → RawSQLFrom → RawSQLFrom

inductive SQLQuery : Type → Type (u + 1) where
  | mk : SQLSelect α → SQLFrom (Table β) → SQLProp → (h: α ⊆ β := by simp) → SQLQuery (Table α)
  | nstd : SQLSelect α → SQLQuery (Table β) → SQLProp → (h: α ⊆ β := by simp) → SQLQuery (Table α)

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

def SQLFrom.toString : SQLFrom α → String
  | table s            => s
  | .alias f s         => s!"({f.toString}) AS {s}"
  | join j l r p       => s!"{l.toString} {j} JOIN {r.toString} ON {p}"
  | joinUsing j l r d  => s!"{l.toString} {j} JOIN {r.toString} USING {d}"
  | implicitJoin t₁ t₂ => s!"{t₁.toString}, {t₂.toString}"

instance : ToString (SQLFrom α) := ⟨SQLFrom.toString⟩

def SQLQuery.toString : SQLQuery α → String
  | mk s f w _ => s!"SELECT {s} FROM {f} WHERE {w}"
  | nstd s q w _ => s!"SELECT {s} FROM ({q.toString}) WHERE {w}"

instance : ToString (SQLQuery α) := ⟨SQLQuery.toString⟩
