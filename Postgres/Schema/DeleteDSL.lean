/-
  Copyright (c) 2024 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/


import Postgres.Schema.QueryDSL

namespace DeleteDSL

inductive DeleteFrom
  | table : String → DeleteFrom
  | alias : String → String → DeleteFrom

def DeleteFrom.toString : DeleteFrom → String
  | .table name => name
  | .alias name al => s!"{name} AS {al}"

instance : ToString DeleteFrom :=
  ⟨DeleteFrom.toString⟩

inductive SQLDelete
  | mk : DeleteFrom → SQLProp → SQLDelete

def SQLDelete.toString : SQLDelete → String
  | .mk df p => s!"DELETE FROM {df} WHERE {p}"

instance : ToString SQLDelete :=
  ⟨SQLDelete.toString⟩
