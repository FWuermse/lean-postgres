import Postgres.Query
import Postgres.LibPQ
import Postgres.Syntax.SchemaSyntax
import Postgres.Syntax.SchemaDSL

open Query
open LibPQ
open SchemaSyntax
open SchemaDSL

namespace Table

def listTables (conn : Connection) : IO (List String) := do
  let query :=
    SELECT table_name
    FROM information_schema.tables
    WHERE table_schema = "public"
      AND table_type = "BASE TABLE"
  let tables ← sendQuery conn query
  let res := match tables with
    | some xs => xs.map "\n".intercalate
    | _ => []
  pure res

def createTable (conn : Connection) (query : SQLCreate) : IO (Option ResultStatus) := do
  let res ← exec conn query.toString
  if resStatus res != .tuplesOk then
    let error ← resErr res
    IO.println <| error
    pure Option.none
  else
    pure <| Option.some <| resStatus res
