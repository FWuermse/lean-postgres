import Lake
open Lake DSL

-- Resolve postgres include/lib dirs: prefer pg_config, then common brew paths.
def pgDirs : IO (String × String) := do
  let r ← IO.Process.output { cmd := "pg_config", args := #["--includedir", "--libdir"] }
  if r.exitCode == 0 then
    let lines := r.stdout.splitOn "\n" |>.map String.trim |>.filter (· ≠ "")
    if lines.length >= 2 then return (lines[0]!, lines[1]!)
  -- Homebrew Apple Silicon
  let m1 ← IO.Process.output { cmd := "test", args := #["-d", "/opt/homebrew/opt/libpq/include"] }
  if m1.exitCode == 0 then
    return ("/opt/homebrew/opt/libpq/include", "/opt/homebrew/opt/libpq/lib")
  -- Homebrew Intel
  let intel ← IO.Process.output { cmd := "test", args := #["-d", "/usr/local/opt/libpq/include"] }
  if intel.exitCode == 0 then
    return ("/usr/local/opt/libpq/include", "/usr/local/opt/libpq/lib")
  return ("/usr/include/postgresql", "/usr/lib")

package Postgres where
  buildType := .debug

extern_lib libPostgresFFI pkg := do
  let leanInc ← getLeanIncludeDir
  let (pgInc, _pgLib) ← pgDirs
  let srcFile := pkg.dir / "Postgres" / "LibPQ.c"
  let oFile   := pkg.buildDir / "Postgres" / "LibPQ.o"
  let libFile := pkg.buildDir / "libPostgresFFI.a"
  let srcJob ← inputFile srcFile false
  let oJob ← buildO oFile srcJob
    #["-fPIC", s!"-I{leanInc}", s!"-I{pgInc}"]
  buildStaticLib libFile #[oJob]

@[default_target]
lean_lib Postgres where
  precompileModules := true
  moreLinkArgs := #[
    "-L/opt/homebrew/opt/libpq/lib",  -- Homebrew Apple Silicon
    "-L/usr/local/opt/libpq/lib",     -- Homebrew Intel
    "-lpq"
  ]
