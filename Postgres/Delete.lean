import Postgres.LibPQ
import Postgres.Syntax.DeleteDSL

open LibPQ Connection DeleteDSL

namespace Delete

def delete (conn : Connection) (query : SQLDelete) : IO (Option ResultStatus) := do
  let res ← exec conn query.toString
  if resStatus res != .tuplesOk then
    let error ← connErr conn
    IO.println <| error
    pure Option.none
  else
    pure <| resStatus res
