/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer, Jannis Limperg
-/

import Postgres.LibPQ
import Postgres.Syntax.QueryDSL

open LibPQ Connection

namespace Query

def sendQuery (connection : Connection) (query : SQLQuery) : IO <| Option <| List <| List String := do
  let res ← exec connection query.toString
  if resStatus res != .tuplesOk then
    let error ← connErr connection
    IO.println <| error
    pure Option.none
  else
    let rows := List.map Nat.toUSize <| List.range (← nTuples res).toNat
    let columns := List.map Nat.toUSize <| List.range (← nFields res).toNat
    let table ← rows.mapM (λ x: USize => columns.mapM (λ y: USize => (getValue res x y)))
    pure table
end Query
