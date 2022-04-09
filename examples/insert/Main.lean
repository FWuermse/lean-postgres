/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres

open Insert

def main : IO Unit := do
  insert [
    ('c', 3, 'd', Varchar(10) "Hello"),
    ('c', 2, 'e', Varchar(10) "Hi"),
    ('A', 90, 'F', Varchar(10) "My Varchar")
  ]
  IO.println "Not yet implemented. Nothing was inserted."
