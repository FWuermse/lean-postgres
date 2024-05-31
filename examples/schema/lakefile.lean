import Lake
open System Lake DSL

require Postgres from "../.."

package DDL where

@[default_target]
lean_exe DDL where
  moreLinkArgs := #["-lpq", "-L/opt/homebrew/opt/libpq/lib"]
  root := `Main
