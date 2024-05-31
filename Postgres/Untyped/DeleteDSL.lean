import Postgres.Untyped.QueryDSL

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
