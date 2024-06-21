/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres

open LibPQ Query

def stringTables (table : Option (List (List String))) : String :=
  match table with
  | none => "Error"
  | some t => "\n".intercalate (t.map (", ".intercalate .))

def schema : String → List Field
  | "employee" => [Field.nat "id", Field.varchar 255 "name"]
  | "customer" => [Field.nat "id", Field.date "date"]
  | "thirdTable" => [Field.nat "id", Field.varchar 255 "someField"]
  | _ => []

def myQueries : SQL Unit := do
  -- Type: SQLQuery [Field.nat "employee.id", Field.varchar 255 "employee.name"]
  let query := queryOn schema |
    SELECT *
    FROM employee
  let res ← sendQuery query
  IO.println $ stringTables res
  IO.println query

  -- Some more quries with schema typing:
  let _simple := queryOn schema |
    SELECT name FROM employee

  let _nested := queryOn schema |
    SELECT *
    FROM (SELECT id
          FROM (SELECT *
                FROM employee))

  let _join := queryOn schema |
    SELECT date, name FROM employee INNER JOIN customer ON employee.id = customer.id

  let _implicitJoin := queryOn schema |
    SELECT employee.id AS nm, X.date
    FROM employee, customer AS X
    WHERE employee.id = customer.id

  -- let _failing := queryOn schema | SELECT a FROM employee
  let _doubleJoin := queryOn schema |
    SELECT id
    FROM customer LEFT JOIN (employee LEFT JOIN employee ON id = id) ON customer.id = employee.id

  let _tableAliasNested := queryOn schema |
    SELECT y.id
    FROM thirdTable LEFT JOIN (employee LEFT JOIN customer ON employee.id = customer.id) AS x ON customer.id = employee.id AS y

  let _selectAliasNested := queryOn schema |
    SELECT a.a.a AS x
    FROM (SELECT id AS a FROM employee) AS a.a

  let _selectImplicitSimple := queryOn schema |
    SELECT id
    FROM employee
    WHERE name = "test" AND id = 21

def main : IO Unit := do
  let conn ← login "localhost" "5432" "postgres" "postgres" "password"
  myQueries.run {conn}
