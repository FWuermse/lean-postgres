import Postgres

open Connection

def zeroToSpace : UInt8 → UInt8
| 0 => 32
| x => x

def main : IO Unit := do
  let conn ← openConnection "localhost" "5432" "postgres" "postgres" "pw"
  let resp ← sendQuery conn "SELECT * FROM pf;"
  IO.println "TEST"
  IO.println $ String.fromUTF8Unchecked $ List.toByteArray $ List.map zeroToSpace resp.toList
  conn.close
