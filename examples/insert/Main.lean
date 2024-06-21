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
