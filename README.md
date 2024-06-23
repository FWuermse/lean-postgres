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

Please find examples in the [example folder](https://github.com/FWuermse/lean-postgres/tree/master/examples/open-connection).

## TODOs
- [ ] DDL schema validation
- [ ] Insert schema validation
