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

def main : IO Unit := do
  let conn ← login "localhost" "5432" "postgres" "postgres" "password"
  let query :=
    SELECT *
    FROM employee
  let res ← sendQuery conn query
  IO.println $ stringTables res
  IO.println query
