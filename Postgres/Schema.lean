import Postgres.LibPQ
import Postgres.Syntax.SchemaSyntax
import Postgres.Syntax.QuerySyntax
import Postgres.Syntax.SchemaDSL
import Postgres.Query

open LibPQ
open SchemaDSL SchemaSyntax Query

namespace Schema

def listTables (conn : Connection) : IO (List String) := do
  let query : SQLQuery :=
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
  if resStatus res != .commandOk then
    let error ← connErr conn
    IO.println <| error
    pure Option.none
  else
    pure <| Option.some <| resStatus res

def dropTable (conn : Connection) (query : SQLDrop) : IO (Option ResultStatus) := do
  let res ← exec conn query.toString
  if resStatus res != .commandOk then
    let error ← connErr conn
    IO.println <| error
    pure Option.none
  else
    pure <| Option.some <| resStatus res
