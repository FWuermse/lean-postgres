import Lake
open Lake DSL

require alloy from git "https://github.com/tydeu/lean4-alloy/" @ "master"
require std from git "https://github.com/leanprover/std4.git" @ "main"

package Postgres where
  -- add package configuration options here

module_data alloy.c.o : BuildJob FilePath
@[default_target]
lean_lib Postgres where
  precompileModules := true
  nativeFacets := #[Module.oFacet, `alloy.c.o]
  moreLeancArgs := #["-fPIC", "-I/opt/homebrew/opt/libpq/include"]
  moreLinkArgs := #["-lpq", "-L/opt/homebrew/opt/libpq/lib"]
  -- add library configuration options here
