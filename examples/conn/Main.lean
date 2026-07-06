/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres

open LibPQ Query QueryAST QuerySyntax

def stringTables (table : Option (List (List String))) : String :=
  match table with
  | none => "Error"
  | some t => "\n".intercalate (t.map (", ".intercalate .))

def schema : Schema := [
  ("employee", [
    ("id", "employee", .bigInt)]),
  ("customer", [
    ("id", "customer", .bigInt),
    ("date", "customer", .date)])]

def main : IO Unit := do
  let conn ← login "localhost" "5432" "postgres" "postgres" "password"
  let status := conn.status
  IO.println <| status.toString
  let q := pquery( schema |- SELECT * FROM employee )
  let res ← sendQuery q |>.run ⟨conn⟩
  IO.println <| stringTables res
