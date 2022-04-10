/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres

open Insert
open Connect
open Query

def main : IO Unit := do
  let conn ← openConnection "localhost" "5432" "postgres" "postgres" "pw"
  let insertQuery :=
    INSERT INTO employee 
    VALUES [
      -- Type checking for row alignment and types
      (Varchar(15) "Florian", Varchar(15) "Würmseer", 123, 'R', 2014-01-09),
      (Varchar(15) "Erin", Varchar(15) "Jaeger", 999, 'A', 850-03-30)
    ]
  IO.println $ ← insert conn insertQuery
  let query := 
    SELECT surname, nr, employment_date
    FROM employee 
    WHERE employee.employment_date <= "1800-12-31"
  IO.println $ ← sendQuery conn query
  conn.close

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
