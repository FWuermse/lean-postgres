/-
  Copyright (c) 2024 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres.LibPQ
import Postgres.DSL.InsertDSL

open LibPQ Connection InsertDSL

namespace PQInsert

def insert {α : List Univ} (query : @InsertQuery α) : SQL Response := do
  let ctx ← read
  let conn := ctx.conn
  -- Only stored for the duration of the pq session
  let seed := s!"{← IO.rand 0 1000000000}"
  let table := query.table
  let values := query.values
  let tuple := values.head?
  let amount := match tuple with
    | .none => 0
    | .some t => t.toStringList.length.toUSize
  let placeholders := List.map (. + 1) ∘ List.range <| amount.toNat
  let placeholders := placeholders.map (s!"${.}")
  -- TODO: sanitize
  let rawQuery := s!"INSERT INTO {table} VALUES ({", ".intercalate placeholders})"
  let res ← prepare conn seed rawQuery amount ⟨#[]⟩
  if res.status != .commandOk then
    let error ← conn.error
    pure <| .error error
  else
    let mut response := .error "Insert was invoked without values to be inserted."
    for tuple in values do
      let res ← execPrepared conn seed amount tuple.toStringList.toArray ⟨#[]⟩ ⟨#[]⟩ 0
      if res.status != .commandOk then
        let errorMessage ← conn.error
        response := .error errorMessage
        break
      else
        response := .ok res.status
    pure response
