import Lake
open Lake DSL

require alloy from git "https://github.com/tydeu/lean4-alloy"@"a712058ff5ca47f670f6d25ea2b2a7385d9523ae"

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
  moreLeancArgs := #["-fPIC", "-I/usr/include/libpq"]
  moreLinkArgs := #["-lpq", "-L/usr/lib"]
