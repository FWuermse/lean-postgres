/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres

open Insert
open LibPQ

def main : IO Unit := do
  let conn := login "localhost" "5432" "postgres" "postgres" "password"
  let _ ← exec conn "CREATE TABLE IF NOT EXISTS mytable (id SERIAL PRIMARY KEY, name VARCHAR(50), age INT)"
  let _ ← exec conn "SELECT table_name FROM information_schema.tables WHERE table_schema = 'public' AND table_type = 'BASE TABLE'"
