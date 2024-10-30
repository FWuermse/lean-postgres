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

def schema : Schema := [("employee", [("id", "employee", .bigInt)]), ("customer", [("id", "customer", .bigInt), ("date", "customer", .date)])]

def queriesOnSchema : SQL Unit := do
  let query := pquery( schema |- SELECT * FROM employee ∶ [("id", "employee", DataType.bigInt)] )
  let res ← sendQuery query
  IO.println <| stringTables res
  IO.println query

def testQueries : SQL Unit := do
  let schema : Schema := [("employee", [("id", "employee", DataType.bigInt)]), ("customer", [("id", "customer", .bigInt), ("date", "customer", .date)])]
  #check pquery( schema |- SELECT * FROM employee ∶ [("id", "employee", DataType.bigInt)] )
  #check pquery( schema |- SELECT * FROM employee, customer ∶ [("id", "employee", DataType.bigInt), ("id", "customer", DataType.bigInt), ("date", "customer", DataType.date)] )
  #check pquery( schema |- SELECT customer.date FROM employee, customer ∶ [("date", "customer", DataType.date)] )
  #check pquery( schema |- SELECT customer.id FROM employee, customer ∶ [("id", "customer", DataType.bigInt)] )
  #check pquery( schema |- SELECT employee.id FROM employee, customer ∶ [("id", "employee", DataType.bigInt)] )
  #check pquery( schema |- SELECT b.id FROM employee AS b, customer ∶ [("id", "b", DataType.bigInt)] )
  #check pquery( schema |- SELECT employee.id AS fakeID FROM employee ∶ [("fakeID", "employee", DataType.bigInt)] )
  #check pquery( schema |- SELECT a.id FROM (SELECT * FROM customer) AS a ∶ [("id", "a", DataType.bigInt)] )
  #check pquery( schema |- SELECT customer.id FROM customer WHERE +(customer.id / 2) = (-1 + 0.0) AND TRUE ∶ [("id", "customer", DataType.bigInt)] )
  #check pquery( schema |- SELECT customer.id FROM customer WHERE (customer.date + 8) > customer.date ∶ [("id", "customer", DataType.bigInt)] )
  #check pquery( schema |- SELECT a.a.a FROM (SELECT customer.id AS a FROM customer) AS a.a ∶ [("a", "a.a", DataType.bigInt)] )
  #check pquery( schema |- SELECT a.id FROM (SELECT b.id FROM (SELECT customer.id FROM customer) AS b) AS a ∶ [("id", "a", DataType.bigInt)] )

def main : IO Unit := do
  let conn ← login "0.0.0.0" "5432" "postgres" "postgres" "password"
  queriesOnSchema.run {conn}
  testQueries.run {conn}
  pure ()
