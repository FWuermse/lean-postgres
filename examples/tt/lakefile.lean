import Lake
open System Lake DSL

package DDL where

@[default_target]
lean_exe DDL where
  moreLinkArgs := #["-lpq", "-L/opt/homebrew/opt/libpq/lib"]
  root := `Main
