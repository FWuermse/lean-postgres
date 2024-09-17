import Lake
open Lake DSL

require alloy from git "https://github.com/tydeu/lean4-alloy" @ "master"

package Postgres where
  buildType := .debug
  -- add package configuration options here

module_data alloy.c.o.export : BuildJob FilePath
module_data alloy.c.o.noexport : BuildJob FilePath
@[default_target]
lean_lib Postgres where
  precompileModules := true
  nativeFacets := fun shouldExport =>
    if shouldExport then
      #[Module.oExportFacet, `alloy.c.o.export]
    else
      #[Module.oNoExportFacet, `alloy.c.o.noexport]
  moreLeancArgs := #["-fPIC", "-I/opt/homebrew/opt/libpq/include"]
  moreLinkArgs := #["-lpq", "-L/opt/homebrew/opt/libpq/lib"]
