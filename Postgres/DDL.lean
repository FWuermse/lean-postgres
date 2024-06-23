/-
  Copyright (c) 2024 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres.LibPQ
import Postgres.DSL.DDLSyntax
import Postgres.DSL.QuerySyntax
import Postgres.DSL.QueryDSL
import Postgres.DSL.DDLDSL
import Postgres.Query

open LibPQ
open DDLDSL DDLSyntax Query

namespace DDL

def listTables : SQL (List String) := do
  let query := query |
    SELECT table_name
    FROM information_schema.tables
    WHERE table_schema = "public"
      AND table_type = "BASE TABLE"
  let tables ← sendUntypedQuery query
  let res := match tables with
    | some xs => xs.map "\n".intercalate
    | _ => []
  pure res

def createTable (query : SQLCreate) : SQL Response := do
  let ctx ← read
  let conn := ctx.conn
  let res ← exec conn query.toString
  if res.status != .commandOk then
    let errorMessage ← conn.error
    pure <| .error errorMessage
  else
    pure <| .ok res.status

def dropTable (query : SQLDrop) : SQL Response := do
  let ctx ← read
  let conn := ctx.conn
  let res ← exec conn query.toString
  if res.status != .commandOk then
    let errorMessage ← conn.error
    IO.println <| errorMessage
    pure <| .error errorMessage
  else
    pure <| .ok res.status
