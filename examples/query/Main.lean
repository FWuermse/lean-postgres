/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres

def main : IO Unit := do
  let query :=
    SELECT surname, nr, employment_date
    FROM employee
    WHERE employee.employment_date <= "1800-12-30"
  IO.println query
