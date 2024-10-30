# Lean4 Postgresql

This library embeds PostgreSQL syntax and semantics into Lean 4. The rules for the type system are taken from the Postgres [documentation](https://www.postgresql.org/docs/) and [source code](https://github.com/postgres/postgres) version 17.

## Installation

### Lake

Add the following dependency to your `lakefile.lean` :

```lean
import Lake
open System Lake DSL

require Postgres from git "https://github.com/FWuermse/lean-postgres" @ "master"

package conn where

@[default_target]
lean_exe conn where
  moreLinkArgs := #["-lpq", "-L/<your path to libpq>"]
  root := `Main
```

## Usage

### Requirements

Requires a running Postgres instance e.G. via Docker:

```sh
docker run -d --name postgres -e POSTGRES_PASSWORD=password -v ~/my-volume:/var/lib/postgresql/data -p 5432:5432 postgres
```

### Code

```lean
import Postgres

open LibPQ Query QueryAST QuerySyntax

def stringTables (table : Option (List (List String))) : String :=
  match table with
  | none => "Error"
  | some t => "\n".intercalate (t.map (", ".intercalate .))

def schema : Schema := [("employee", [("id", "employee", .bigInt)]), ("customer", [("id", "customer", .bigInt), ("date", "customer", .date)])]

def queriesOnSchema : SQL Unit := do
  let query := pquery( schema |-
    SELECT customer.date AS d
    FROM employee, customer
    WHERE -(employee.id * -2) = customer.id
      AND customer.id != 0 ∶ [("d", "customer", .date)] )
  let res ← sendQuery query
  IO.println <| stringTables res
  IO.println query

def main : IO Unit := do
  let conn ← login "0.0.0.0" "5432" "postgres" "postgres" "password"
  queriesOnSchema.run {conn}
  testQueries.run {conn}
  pure ()
```

```SQL
$ ./.lake/build/bin/query

    d      
2003-01-03
1997-11-29
```

Please find more examples in the [example folder](https://github.com/FWuermse/lean-postgres/tree/master/examples).

## Supported DataTypes

|DataType|Usage|Limitations|
|-|-|-|
|NULL|empty type||
|Integer|32 bit integer||
|BigInt|64 bit integer||
|bit|fixed length bit array||
|varBit|variable length bit array||
|boolean|TRUE or FALSE||
|char|fixed length character array||
|varchar|variable length character array||
|text|character array of arbitrary length||
|date|Date of the form yyyy-mm-dd|validation not month specific, no other formats supported|
|double|64 bit floating point number|only double no floats supported|

## Supported features on this branch
- [ ] Query
  - [x] Fields and aliases
  - [ ] Select as arbitrary expression
  - [ ] Table selection
    - [x] Tables
    - [x] Join on (inner, outer, right, left)
    - [ ] Join using
    - [x] Implicit join
    - [x] Nested queries
    - [ ] Union
    - [ ] Intersection
  - [ ] Expression functions and operators
    - [x] Logical operators
    - [x] Comparison operators
    - [ ] Comparison functions
    - [x] Mathematical operators
    - [ ] Mathematical functions
    - [x] String operators
    - [ ] String functions
    - [ ] Bit operators
    - [ ] Bit functions
    - [ ] Geometric operators
    - [ ] Geometric functions
    - [ ] XML functions
    - [ ] JSON functions
  - [ ] Type Conversions
    - [x] Char/String conversions
    - [x] Date conversions
    - [x] Number conversions
    - [ ] Date conversions
- [ ] Insert
- [ ] Delete
- [ ] DDL
