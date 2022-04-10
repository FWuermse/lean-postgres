/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer, Jannis Limperg
-/

import Socket
import Lean
import Postgres.Connection
import Postgres.Response
import SqlUtils.SQLSyntax

open Socket Connect Lean Meta Elab Elab.Term Response.QueryResponse

namespace Query

def sendQuery (socket : Socket) (query : SQLQuery) : IO Section := do
  let req ← socket.send $ toByteArray $ RegularMessage.mk 'Q' (toString query)
  parseQueryResponse socket

end Query
