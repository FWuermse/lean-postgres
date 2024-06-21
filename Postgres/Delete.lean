/-
  Copyright (c) 2024 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres.LibPQ
import Postgres.Schema.DeleteDSL

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
