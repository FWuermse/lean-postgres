import Postgres

open Connect
open Query

def zeroToSpace : UInt8 → UInt8
| 0 => 32
| x => x

def main : IO Unit := do
  let conn ← openConnection "localhost" "5432" "postgres" "postgres" "pw"
  let query := SELECT "pilot", "flugzeug" FROM "pf";
  let resp ← sendQuery conn query
  IO.println $ String.fromUTF8Unchecked $ List.toByteArray $ List.map zeroToSpace resp.toList
  conn.close
