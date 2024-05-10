# Lean4 Postgresql

## Installation

### Lake

Add the following dependency to your `lakefile.lean` :

```lean
import Lake
open System Lake DSL

require Postgres from "../.."

package conn where

@[default_target]
lean_exe conn where
  moreLinkArgs := #["-lpq", "-L/opt/homebrew/opt/libpq/lib"]
  root := `Main
```

## Usage

### Requirements

Requires a running Postgres instance e.G. via Docker:

```sh
docker run -d --name postgres -e POSTGRES_PASSWORD=password -v ~/my-volume:/var/lib/postgresql/data -p 5432:5432 postgres
```

### Code

Currently only simple queries and inserts are supported:

```lean
import Postgres

open PQInsert
open Connect
open Query

def main : IO Unit := do
  -- Open connection
  let conn ← login "localhost" "5432" "postgres" "postgres" "password"
  let insertQuery :=
    CREATE TABLE IF NOT EXISTS employee (name Varchar(15), surname Varchar(15), nr Num, letter Char, employment_date Date)
  let res ← createTable conn insertQuery
  if let .some r := res then
    IO.println $ Result.toString r
  -- Print tables
  IO.println <| ← listTables conn
  -- Insert values
  let insertQuery :=
    INSERT INTO employee
    VALUES [
      -- Type checking for row alignment and types
      (Varchar(15) "Florian", Varchar(15) "Würmseer", 123, 'R', 2014-01-09),
      (Varchar(15) "Erin", Varchar(15) "Jaeger", 999, 'A', 850-03-30)
    ]
  let _status ← insert conn insertQuery

  let query := 
    SELECT surname, nr, employment_date
    FROM employee 
    WHERE employee.employment_date <= "1800-12-31"

  let res ← sendQuery conn query
  if let .some r := res then
    IO.println <| >"\n".intercalate (r.map (", ".intercalate .))
```

Output:

```sh
NOTICE:  relation "employee" already exists, skipping
commandOk
[mytable, employee]
'Jaeger', 999, 0850-03-30
```

Please find more examples in the [example folder](https://github.com/FWuermse/lean-postgres/tree/master/examples/open-connection).

## TODOs
- [ ] Schema validation
