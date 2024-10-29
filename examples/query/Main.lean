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

def schema : Schema := [("employee", [("id", "employee", .bigInt)]), ("myTable", [("id", "myTable", .bigInt), ("name", "myTable", .text), ("age", "myTable", .integer)])]

def queriesOnSchema : SQL Unit := do
  let query := pquery( schema |- SELECT myTable.id, myTable.age FROM myTable ∶ [("id", "myTable", .bigInt), ("age", "myTable", .integer)] )
  let res ← sendQuery query
  IO.println <| stringTables res
  IO.println query

def main : IO Unit := do
  let conn ← login "0.0.0.0" "5432" "postgres" "postgres" "password"
  queriesOnSchema.run {conn}
  pure ()
