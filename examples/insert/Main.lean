/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres

open InsertSyntax DeleteSyntax LibPQ PQInsert Delete Query

def main : IO Unit := do
  let insertQuery :=
    INSERT INTO employee
    VALUES [
      -- Type checking for row alignment and types
      (Varchar(15) "Florian", Varchar(15) "Würmseer", 123, 'R', 2014-01-09),
      (Varchar(15) "Erin", Varchar(15) "Jaeger", 999, 'A', 850-03-30)
    ]
  IO.println insertQuery.values
  IO.println insertQuery.table
  let conn ← login "localhost" "5432" "postgres" "postgres" "password"
  let _ ← insert conn insertQuery
  let deleteQuery :=
    DELETE FROM employee WHERE nr = 123 OR nr = 999
  let query :=
    SELECT *
    FROM employee
  let res ← sendQuery conn query
  if let .some r := res then
    IO.println <| "\n".intercalate (r.map (", ".intercalate .))
  let _ ← delete conn deleteQuery
  let res ← sendQuery conn query
  if let .some r := res then
    IO.println <| "\n".intercalate (r.map (", ".intercalate .))

-- Typechecks:
#check [
  ('c', 3, 'd', Varchar(10) "Hello", 2011-11-11),
  ('c', 2, 'e', Varchar(10) "Hi", 2008-12-14),
  ('A', 90, 'F', Varchar(10) "My Varchar", 2022-03-12)
]

-- Doesn't typecheck
-- #check insert [
--   ('a', 4, Varchar(2) "Hi"),
--   ("String", 3, 'd')
-- ]

def schemaWrapper (query : List Univ → Type) (table: String) (schema: String → (List Univ)) := query $ schema table

def mySchema : String → List Univ
  | "employee" => [.char, .nat, .varchar 10, .date]
  | "myTable" => [.nat, .varchar 10]
  | _ => []

def S := schemaWrapper @InsertQuery "myTable" mySchema

def myQuery : S :=
  INSERT INTO myTable VALUES [(10, Varchar(10) "Hi")]

#check myQuery
#check S

--def myQuery2 : S :=
--  INSERT INTO myTable VALUES [(10, 11)]

structure Context where
  connection : Connection
  schema : String → String → String

structure State where
  tes2: String

abbrev SQL := ReaderT Context (StateRefT State IO)

def doAll : SQL String := do
  -- ...
  pure "Success"

def mkCtx (conn : Connection) : IO Context := do
  pure $ Context.mk conn (fun x => fun y => "")

def main' : IO Unit := do
  let conn ← connect ""
  let ctx ← mkCtx conn
  let status := doAll ctx
  pure ()

inductive Field
  | nat : String → Field
  | varchar (n : UInt8) : String → Field
  deriving BEq

def Field.interp : Field → Type
  | nat _ => Nat
  | varchar n _ => Varchar n

inductive Table : List Field → Type
  | nil : Table []
  | cons (x : u.interp) (xs : Table us) : Table (u :: us)

inductive TaggedField where
  | nat : String → Nat → TaggedField
  | varchar : String → Varchar n → TaggedField

def Table.of {us: List Field} (_ : Table us) : List Field := us

inductive SelectField {α : Type}
  | col   : (String → α) → String → SelectField
  | alias : (String → α) → String → String         → SelectField

inductive Select (α : List Field)
  | list : (List (String → Field)) → List (SelectField) → Select α
  | all  : (List (String → Field)) → Select α

inductive From (α : List Field)
  | table : String → From α
  | tables : List String → From α
  | subquery : Select α → From α

inductive Query (α : List Field) where
  | mk : Select α → {β : List Field} → From β → (h : α ⊆ β := by simp) → Query α

def schema (table : String) (name : String) : Field := match table with
  | "myTable" => match name with
    | "id" => Field.nat "id"
    | "name" => Field.nat "name"
    | _ => sorry
  | "otherTable" => match name with
    | "date" => Field.nat "date"
    | _ => sorry
  | _ => sorry

def table_size_one : Table <| Field.nat "id"::Table.of Table.nil := Table.cons .zero Table.nil
def table_size_two : Table <| Field.varchar 5 "name"::@Field.nat "id"::Table.of Table.nil := Table.cons (Varchar.mk "Hi") table_size_one

def tables := ["myTable", "otherTable"]
def selectFields := [SelectField.col (schema "myTable") "id", SelectField.col (schema "otherTable") "date"]
def select : Select [Field.nat "id", Field.nat "date"] := Select.list (tables.map (schema .)) selectFields
def frm : From [Field.nat "id", Field.nat "date"] := From.tables tables
def query := Query.mk select frm -- Type: Query [Field.nat "id", Field.nat "date"]

#check query

def tables' := ["myTable", "otherTable"]
def selectFields' := [SelectField.col (schema "otherTable") "date"]
def select' : Select [Field.nat "id"] := Select.list (tables.map (schema .)) selectFields
def frm' : From [Field.nat "id"] := From.tables tables
def query' := Query.mk select' frm' -- Type: Query [Field.nat "id", Field.nat "date"]

def nested_frm : From [Field.nat "id", Field.nat "date"] := From.subquery select
--def nested_frm2 : From [Field.nat "id", Field.nat "date"] := From.subquery select'
def query2 := Query.mk select' nested_frm (h := by simp)-- has type From [Field.nat "id"] : Type 1 but is expected to have type From [Field.nat "id", Field.nat "date"] : Type 1

def runQuery {α : List Field} (q : Query α) : Table α :=
  sorry
