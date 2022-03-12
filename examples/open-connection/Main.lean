import Postgres

open Connect
open Query

def main : IO Unit := do
  let conn ← openConnection "localhost" "5432" "postgres" "postgres" "pw"
  let query := SELECT "pilot", "flugzeug" FROM "pf";
  let resp ← sendQuery conn query
  IO.println $ resp.rowDesc.fields.map (λ x => x.colName)
  IO.println $ resp.dataRow.map (λ x => x.fields.map (λ x => x.data))
