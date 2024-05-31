import Postgres.LibPQ
import Postgres.Untyped.DDLSyntax
import Postgres.Untyped.QuerySyntax
import Postgres.Untyped.DDLDSL
import Postgres.Query

open LibPQ
open DDLDSL DDLSyntax Query

namespace DDL

def listTables (conn : Connection) : IO (List String) := do
  let query : SQLQuery :=
    SELECT table_name
    FROM information_DDL.tables
    WHERE table_DDL = "public"
      AND table_type = "BASE TABLE"
  let tables ← sendQuery conn query
  let res := match tables with
    | some xs => xs.map "\n".intercalate
    | _ => []
  pure res

def createTable (conn : Connection) (query : SQLCreate) : IO Response := do
  let res ← exec conn query.toString
  if res.status != .commandOk then
    let errorMessage ← conn.error
    pure <| .error errorMessage
  else
    pure <| .ok res.status

def dropTable (conn : Connection) (query : SQLDrop) : IO Response := do
  let res ← exec conn query.toString
  if res.status != .commandOk then
    let errorMessage ← conn.error
    IO.println <| errorMessage
    pure <| .error errorMessage
  else
    pure <| .ok res.status
