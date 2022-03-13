/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres

open Connect
open Query

def main : IO Unit := do
  let conn ← openConnection "localhost" "5432" "postgres" "postgres" "pw"
  let query := SELECT pilot, flugzeug FROM pf;
  let resp ← sendQuery conn query
  IO.println resp
  conn.close
