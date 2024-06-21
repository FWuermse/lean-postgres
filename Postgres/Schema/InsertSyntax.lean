/-
  Copyright (c) 2024 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres.Schema.InsertDSL

open InsertDSL

open Lean Elab Meta

namespace InsertSyntax

declare_syntax_cat sqlType
syntax char : sqlType
syntax num : sqlType
syntax "Varchar(" num ") " str : sqlType
syntax num "-" num "-" num : sqlType

syntax:1000 "(" sqlType,* ")" : term

macro_rules
  | `(( $elems,* )) => do
    let rec expandListLit (i : Nat) (skip : Bool) (result : Lean.TSyntax `term) : Lean.MacroM $ Lean.Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => match elems.elemsAndSeps[i]! with
        | `(sqlType|$c:char) => expandListLit i true (← ``((Tuple.cons $c $result : Tuple (Univ.char::Tuple.of $result))))
        | `(sqlType|$n:num) => expandListLit i true (← ``((Tuple.cons ($n : Nat) $result : Tuple (Univ.nat::Tuple.of $result))))
        | `(sqlType|Varchar($n:num) $v:str) => expandListLit i true (← ``((Tuple.cons (Varchar.mk $v) $result : Tuple (Univ.varchar ($n)::Tuple.of $result)))) -- TODO nicer syntax for varchar len
        | `(sqlType|$y:num-$m:num-$d:num) => expandListLit i true (← ``((Tuple.cons (Date.mk $y $m $d) $result : Tuple (Univ.date::Tuple.of $result))))
        | _ => expandListLit i true  (← ``(Tuple.cons `(( $elems,* )) $result)) -- TODO throw error here
    if elems.elemsAndSeps.size < 64 then
      expandListLit elems.elemsAndSeps.size false (← ``(Tuple.nil))
    else
      `(%[ `(( $elems,* )) | Tuple.nil ])

syntax "INSERT INTO " ident " VALUES " : term

macro_rules
  | `(INSERT INTO $id:ident VALUES $values) => ``(InsertQuery.mk $(quote id.getId.toString) $values)
