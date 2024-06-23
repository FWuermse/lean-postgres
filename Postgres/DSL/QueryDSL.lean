/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino, Florian Würmseer
-/

import Postgres.DSL.Utils

inductive DataEntry
  | EInt (i : Int)
  | EFloat (f : Float)
  | EString (s : String)
  | ENull
  deriving Inhabited

instance : OfNat DataEntry n where
  ofNat := DataEntry.EInt (Int.ofNat n)

instance : Coe Int DataEntry where
  coe := DataEntry.EInt

instance : Coe Float DataEntry where
  coe := DataEntry.EFloat

instance : Neg DataEntry where
  neg e := match e with
  | DataEntry.EInt   i => ((-1 : Int) * i : Int)
  | DataEntry.EFloat f => ((-1 : Float) * f : Float)
  | _                  => panic! "invalid DataEntry"

instance : OfScientific DataEntry where
  ofScientific m s e := DataEntry.EFloat (OfScientific.ofScientific m s e)

instance : Coe String DataEntry where
  coe := DataEntry.EString

protected def DataEntry.toString (e : DataEntry) : String :=
  match e with
  | EInt e    => toString e
  | EFloat e  => optimizeFloatString $ toString e
  | EString e => s!"'{e}'"
  | ENull     => "NULL"

instance : ToString DataEntry := ⟨DataEntry.toString⟩

inductive SQLSelectField
  | col   : String → SQLSelectField
  | alias : String → String         → SQLSelectField

inductive SQLUntypedSelect
  | list : Bool → List SQLSelectField → SQLUntypedSelect
  | all  : Bool → SQLUntypedSelect

inductive SQLUntypedProp
  | tt : SQLUntypedProp
  | ff : SQLUntypedProp
  | eqC : String  → String    → SQLUntypedProp
  | neC : String  → String    → SQLUntypedProp
  | ltC : String  → String    → SQLUntypedProp
  | leC : String  → String    → SQLUntypedProp
  | gtC : String  → String    → SQLUntypedProp
  | geC : String  → String    → SQLUntypedProp
  | eqE : String  → DataEntry → SQLUntypedProp
  | neE : String  → DataEntry → SQLUntypedProp
  | ltE : String  → DataEntry → SQLUntypedProp
  | leE : String  → DataEntry → SQLUntypedProp
  | gtE : String  → DataEntry → SQLUntypedProp
  | geE : String  → DataEntry → SQLUntypedProp
  | and : SQLUntypedProp → SQLUntypedProp   → SQLUntypedProp
  | or  : SQLUntypedProp → SQLUntypedProp   → SQLUntypedProp
  | not : SQLUntypedProp → SQLUntypedProp

inductive SQLJoin
  | inner | left | right | outer

inductive SQLUntypedFrom
  | table        : String  → SQLUntypedFrom
  | alias        : SQLUntypedFrom → String  → SQLUntypedFrom
  | join         : SQLJoin → SQLUntypedFrom → SQLUntypedFrom → SQLUntypedProp → SQLUntypedFrom
  | implicitJoin : SQLUntypedFrom → SQLUntypedFrom → SQLUntypedFrom

structure SQLUntypedQuery where
  SELECT : SQLUntypedSelect
  FROM   : SQLUntypedFrom
  WHERE  : SQLUntypedProp

def SQLSelectField.toString : SQLSelectField → String
  | col   c   => c
  | .alias c a => s!"{c} AS {a}"

instance : ToString SQLSelectField := ⟨SQLSelectField.toString⟩

def SQLUntypedSelect.distinct? (d : Bool) : String :=
  if d then "DISTINCT " else default

def SQLUntypedSelect.toString : SQLUntypedSelect → String
  | list d l => (distinct? d).append $ ", ".intercalate $ l.map (SQLSelectField.toString)
  | all  d   => (distinct? d).append $ "*"

instance : ToString SQLUntypedSelect := ⟨SQLUntypedSelect.toString⟩

def SQLUntypedProp.toString : SQLUntypedProp → String
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

instance : ToString SQLUntypedProp := ⟨SQLUntypedProp.toString⟩

def SQLJoin.toString : SQLJoin → String
  | inner => "INNER"
  | left  => "LEFT"
  | right => "RIGHT"
  | outer => "OUTER"

instance : ToString SQLJoin := ⟨SQLJoin.toString⟩

def SQLUntypedFrom.toString : SQLUntypedFrom → String
  | table s            => s
  | .alias f s          => s!"({f.toString}) AS {s}"
  | join  j l r p      => s!"{l.toString} {j} JOIN {r.toString} ON {p}"
  | implicitJoin t₁ t₂ => s!"{t₁.toString}, {t₂.toString}"

instance : ToString SQLUntypedFrom := ⟨SQLUntypedFrom.toString⟩

def SQLUntypedQuery.toString (q : SQLUntypedQuery) : String :=
  s!"SELECT {q.SELECT} FROM {q.FROM} WHERE {q.WHERE}"

instance : ToString SQLUntypedQuery := ⟨SQLUntypedQuery.toString⟩
