/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres

open Insert
open LibPQ

def main : IO Unit := do
  let _ ← connect "localhost" "5432" "postgres" "postgres" "pw"
