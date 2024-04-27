import Lake
open System Lake DSL

require Postgres from "../.."

package query where

@[default_target]
lean_exe query where
  moreLinkArgs := #["-lpq", "-L/opt/homebrew/opt/libpq/lib"]
  root := `Main
