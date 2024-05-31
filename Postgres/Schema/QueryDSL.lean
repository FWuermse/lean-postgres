/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino, Florian Würmseer
-/

import Postgres.Schema.DataEntries

inductive Field
  | nat : String → Field
  | varchar (n : UInt8) : String → Field
  | chat : String → Field
  | date : String → Field
  | nil  : String → Field
  deriving BEq, Repr

inductive SQLSelectField (α: Field)
  | col   : String → SQLSelectField α
  | alias : String → String         → SQLSelectField α

inductive SQLSelect (α : List Field)
  | list : Bool → List (SQLSelectField a) → SQLSelect α
  | all  : Bool → SQLSelect α

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

-- TODO: Condition proofs for joins?
inductive SQLFrom (α : List Field)
  | table        : String  → SQLFrom α
  | alias        : SQLFrom α → String  → SQLFrom α
  | join         : SQLJoin → SQLFrom α → SQLFrom α → SQLProp → SQLFrom α
  | implicitJoin : SQLFrom α → SQLFrom α → SQLFrom α
  | nested       : SQLSelect α → SQLFrom α

inductive SQLQuery (α : List Field) where
  | mk : SQLSelect α → SQLFrom α → SQLProp → SQLQuery α

def SQLSelectField.toString : SQLSelectField α → String
  | col   c   => c
  | .alias c a => s!"{c} AS {a}"

instance : ToString (SQLSelectField α) := ⟨SQLSelectField.toString⟩

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
  | .alias f s          => s!"({f.toString}) AS {s}"
  | join  j l r p      => s!"{l.toString} {j} JOIN {r.toString} ON {p}"
  | implicitJoin t₁ t₂ => s!"{t₁.toString}, {t₂.toString}"
  | nested s           => s!"({s})"

instance : ToString (SQLFrom α) := ⟨SQLFrom.toString⟩

def SQLQuery.toString : SQLQuery α → String
  | mk s f w => s!"SELECT {s} FROM {f} WHERE {w}"

instance : ToString (SQLQuery α) := ⟨SQLQuery.toString⟩
