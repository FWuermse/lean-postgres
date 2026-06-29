import Lake
open Lake DSL

package «examples» where
  -- add package configuration options here

lean_lib «Examples» where
  -- add library configuration options here

@[default_target]
lean_exe «examples» where
  root := `Main
