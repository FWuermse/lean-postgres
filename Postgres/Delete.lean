/-
  Copyright (c) 2024 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres.LibPQ
import Postgres.DSL.DeleteDSL

open LibPQ Connection DeleteDSL

namespace Delete

def delete (query : SQLDelete) : SQL (Option ResultStatus) := do
  let ctx ← read
  let conn := ctx.conn
  let res ← exec conn query.toString
  if res.status != .tuplesOk then
    let error ← conn.error
    IO.println <| error
    pure .none
  else
    pure <| res.status
