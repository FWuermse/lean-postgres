import Postgres.LibPQ
import Postgres.Syntax.InsertDSL

open LibPQ Connection InsertDSL

namespace PQInsert

def insert {α : List Univ} (conn : Connection) (query : @InsertQuery α) : IO (Option ResultStatus) := do
  -- Only stored for the duration of the pq session
  let seed := s!"{← IO.rand 0 1000000000}"
  let table := query.table
  let values := query.values
  let tuple := values.head?
  let amount := match tuple with
    | .none => 0
    | .some t => Nat.toUSize ∘ List.length ∘ Tuple.toStringList <| t
  let placeholders := List.map (. + 1) ∘ List.range <| amount.toNat
  let placeholders := placeholders.map (s!"${.}")
  -- TODO: sanitize
  let rawQuery := s!"INSERT INTO {table} VALUES ({", ".intercalate placeholders})"
  let res ← prepare conn seed rawQuery amount ⟨#[]⟩
  if resStatus res != .commandOk then
    let error ← connErr conn
    IO.println <| error
    pure Option.none
  else
    let ress ← values.mapM (
      fun t => execPrepared conn seed amount t.toStringList.toArray ⟨#[]⟩ ⟨#[]⟩ 0
    )
    let success := (ress.foldl (fun b a => b && (resStatus a == .commandOk)) true)
    if !success then
      let error ← connErr conn
      IO.println <| ress.map (Result.toString ∘ resStatus <| .)
      IO.println <| error
      pure Option.none
    else
      pure <| Option.some <| resStatus res
