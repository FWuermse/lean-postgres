# Lean4 Postgresql Frontend-Backend-protocol

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

Currently only simple queries are supported:

```lean
import Postgres

open Connect
open Query

def main : IO Unit := do
  let conn ← openConnection "localhost" "5432" "postgres" "postgres" "pw"
  let query := SELECT "pilot", "flugzeug" FROM "pf";
  let resp ← sendQuery conn query
  IO.println resp
  conn.close
```

Please find more examples in the [example folder](https://github.com/FWuermse/lean-postgres/tree/master/examples/open-connection).

## TODOs

- Include connection to [mathematical relations](https://github.com/hargoniX/lean-hm/blob/master/Hm/Relation.lean)
- Extend query Syntax and TermElab
- Support insert, create table and delete statements
