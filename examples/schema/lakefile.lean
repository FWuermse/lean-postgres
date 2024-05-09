import Lake
open System Lake DSL

require Postgres from "../.."

package schema where

@[default_target]
lean_exe schema where
  moreLinkArgs := #["-lpq", "-L/opt/homebrew/opt/libpq/lib"]
  root := `Main
