import Lake
open System Lake DSL

require Postgres from "../.."

package insert where

@[default_target]
lean_exe insert where
  moreLinkArgs := #["-lpq", "-L/opt/homebrew/opt/libpq/lib"]
  root := `Main
