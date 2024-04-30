import Postgres.Query
import Postgres.LibPQ
import Postgres.Insert

open Query
open LibPQ
open Insert

namespace Table

def listTables (conn : Connection) : IO (List String) := do
  let query :=
    SELECT table_name
    FROM information_schema.tables
    WHERE table_schema = "public"
      AND table_type = "BASE TABLE"
  let tables ← sendQuery conn query
  let res := match tables with
    | some xs => xs.map "\n".intercalate
    | _ => []
  pure res

inductive CreateScope where
  | local
  | global

inductive SQLCreate where
  | table : CreateScope → Bool → String → SQLFields → SQLCreate

inductive CreateFields where
  | fields : List String × InsertType → CreateFields
