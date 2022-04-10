# Lean4 Postgresql

This is mainly a project to learn about practical lean, networking and databases.

The Protocol documentation: [Frontend/Backend Protocol](https://www.postgresql.org/docs/9.3/protocol.html)

Heavily relies on [Socket.lean](https://github.com/xubaiw/Socket.lean) for the TCP Socket.

## Installation

### Lake

Add the following dependency to your `lakefile.lean` :

```lean
package your-package where
  dependencies := #[{
    name := `postgres
    src := Source.git "https://github.com/FWuermse/lean-postgres.git" "master"
  }]
```

## Usage

### Requirements

Requires a running Postgres instance e.G. via Docker:

```sh
docker run -d --name postgres -e POSTGRES_PASSWORD=password -v ~/my-volume:/var/lib/postgresql/data -p 5432:5432 postgres
```

and currently only supports free text password auth, enabled by changing the following line in your `~/my-volume/pg_hba.conf`

from

```sh
host all all all scram-sha-256
```

to

```sh
host all all all password
```

### Code

Currently only simple queries and inserts are supported:

```lean
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
```

Output:

```sh
INSERT 0 2
surname × nr × employment_date
(Jaeger, 999, 0850-03-30)
```

Please find more examples in the [example folder](https://github.com/FWuermse/lean-postgres/tree/master/examples/open-connection).

## TODOs

- Include connection to [mathematical relations](https://github.com/hargoniX/lean-hm/blob/master/Hm/Relation.lean)
- Better error response parsing
- Support create table and delete statements
