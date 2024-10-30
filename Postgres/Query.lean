/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer, Jannis Limperg
-/

import Postgres.LibPQ
import Postgres.DSL.QueryAST
import Postgres.DSL.QuerySyntax

open LibPQ Connection QueryAST

namespace Query

def sendQuery (query : Query) : SQL <| Option <| List <| List String := do
  let ctx ← read
  let conn := ctx.conn
  let res ← exec conn query.toString
  if res.status != .tuplesOk then
    let error ← conn.error
    IO.println <| error
    pure .none
  else
    let rows := List.map Nat.toUSize <| List.range (← nTuples res).toNat
    let columns := List.map Nat.toUSize <| List.range (← nFields res).toNat
    let table ← rows.mapM fun x => columns.mapM fun y => getValue res x y
    pure table

end Query
