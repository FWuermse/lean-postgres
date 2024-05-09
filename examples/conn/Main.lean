/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres

open LibPQ
open Query
open Schema

def stringTables (table : Option (List (List String))) : String :=
  match table with
  | none => "Error"
  | some t => "\n".intercalate (t.map (", ".intercalate .))

def main : IO Unit := do
  let conn₁ ← login "localhost" "5432" "postgres" "postgres" "password"
  let conn₂ ← connect "host=localhost port=5432 dbname=postgres user=postgres password=password connect_timeout=10"
  let status := connStatus conn₁
  IO.println <| Connection.toString status
  IO.println <| ← listTables conn₁
  -- conn₂ closed due to ref count
  IO.println <| ← listTables conn₂
  let query :=
    SELECT id, name, age
    FROM mytable
  -- conn₁ closed due to ref count
  let res ← sendQuery conn₁ query
  IO.println $ stringTables res
