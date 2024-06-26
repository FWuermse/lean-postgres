/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres

open DDLSyntax LibPQ DDL

def ddl_commands : SQL Unit := do
  -- Clear
  let dropQuery :=
    DROP TABLE IF EXISTS employee
  let res ← dropTable dropQuery
  if let .ok r := res then
    IO.println $ r.toString
  let insertQuery :=
    CREATE TABLE IF NOT EXISTS employee (name Varchar(15), surname Varchar(15), nr Num, letter Char, employment_date Date)
  IO.println insertQuery.toString
  let res ← createTable insertQuery
  if let .ok r := res then
    IO.println $ r.toString
  IO.println <| ← listTables

def main : IO Unit := do
  let conn ← login "localhost" "5432" "postgres" "postgres" "password"
  ddl_commands.run {conn}
