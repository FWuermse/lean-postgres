import Postgres.LibPQ
import Postgres.Syntax.DeleteDSL

open LibPQ Connection DeleteDSL

namespace Delete

def delete (conn : Connection) (query : SQLDelete) : IO (Option ResultStatus) := do
  let res ← exec conn query.toString
  if res.status != .tuplesOk then
    let error ← conn.error
    IO.println <| error
    pure .none
  else
    pure <| res.status
