/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres

open Insert
open LibPQ
open Query
open Table

def printStatus (res : Result) : IO Unit := do
  let status := resStatus res
  match status with
   | .tuplesOk => IO.println "TuplesOk"
   | .pipelineAborted => IO.println "pipelineAborted"
   | .pipelineSync    => IO.println "pipelineSync"
   | .singleTuple     => IO.println "singleTuple"
   | .copyBoth        => IO.println "copyBoth"
   | .fatalError      => IO.println "fatalError"
   | .nonfatalError   => IO.println "nonfatalError"
   | .badResponse     => IO.println "badResponse"
   | .copyIn          => IO.println "copyIn"
   | .copyOut         => IO.println "copyOut"
   | .commandOk       => IO.println "commandOk"
   | .emptyQuery      => IO.println "mptyQuery"

def stringTables (table : Option (List (List String))) : String :=
match table with
| none => "Error"
| some t => "\n".intercalate (t.map (", ".intercalate .))

def main : IO Unit := do
  let conn ← login "localhost" "5432" "postgres" "postgres" "password"
  IO.println <| ← listTables conn
  let query :=
    SELECT id, name, age
    FROM mytable
  let res ← sendQuery conn query
  IO.println $ stringTables res
