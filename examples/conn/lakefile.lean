import Lake
open System Lake DSL

require Postgres from "../.."

package conn where

@[default_target]
lean_exe conn where
  moreLinkArgs := #["-lpq", "-L/opt/homebrew/opt/libpq/lib"]
  root := `Main
