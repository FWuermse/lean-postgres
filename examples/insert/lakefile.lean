import Lake
open System Lake DSL

require Postgres from "../.."

package insert where

@[default_target]
lean_exe insert where
  root := `Main
