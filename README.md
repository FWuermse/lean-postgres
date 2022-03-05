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

### Requirement

Requires a running Postgres instance e.G. via Docker:

```sh
docker run -d --name postgres -e POSTGRES_PASSWORD=password -v ~/my-volume:/var/lib/postgresql/data -p 5432:5432 postgres
```

### Code

Currently only simple queries are supported:

```lean
import Postgres

open Connect Query

def main : IO Unit := do
  let conn ← openConnection "localhost" "5432" "postgres" "postgres" "password"
  let query := SELECT "customer_age" AS "age", "customer_name" FROM "company_data";
  let resp ← sendQuery conn query
  IO.println s!"ByteArray response: {resp}"
  conn.close
```

Please find more examples in the [example folder](https://github.com/FWuermse/lean-postgres/tree/master/examples/open-connection).

## TODOs

- Include connection to [mathematical relations](https://github.com/hargoniX/lean-hm/blob/master/Hm/Relation.lean)
- Extend query Syntax and TermElab
- Support insert, create table and delete statements
