import Lean
open Lean Elab Meta
open List (length)

inductive Varchar (i : UInt8) where
  | mk : (s: String) → (h : s.length <= i.toNat := by simp) → Varchar i

namespace Insert
inductive Univ
  | nat
  | char
  | varchar (n : UInt8)

def Univ.interp : Univ → Type
  | nat => Nat
  | char => Char
  | varchar n => Varchar n

inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil  : HList β []
  | cons : β i → HList β is → HList β (i::is)

abbrev Tuple := HList Univ.interp

def Tuple.of {us: List Univ} (x : Tuple us) : List Univ := us

declare_syntax_cat sqlType
syntax char : sqlType
syntax num : sqlType
syntax "Varchar(" num ") " str : sqlType

syntax "(" sqlType,* ")" : term
macro_rules
  | `(( $elems,* )) => do
    let rec expandListLit (i : Nat) (skip : Bool) (result : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => match elems.elemsAndSeps[i] with
        | `(sqlType|$c:charLit) => expandListLit i true (← ``((HList.cons $c $result : Tuple (Univ.char::Tuple.of $result))))
        | `(sqlType|$n:numLit) => expandListLit i true (← ``((HList.cons ($n : Nat) $result : Tuple (Univ.nat::Tuple.of $result))))
        | `(sqlType|Varchar($n:numLit) $v:strLit) => expandListLit i true (← ``((HList.cons (Varchar.mk $v) $result : Tuple (Univ.varchar ($n)::Tuple.of $result)))) -- TODO nicer syntax for varchar len
        | _ => expandListLit i true  (← ``(HList.cons $(elems.elemsAndSeps[i]) $result))
    if elems.elemsAndSeps.size < 64 then
      expandListLit elems.elemsAndSeps.size false (← ``(HList.nil))
    else
      `(%[ $elems,* | Tuple.nil ])

inductive Response
-- TODO define proper response type

def insert {α : List Univ} (x : List (Tuple α)) : Response :=
  sorry -- TODO impelement insert

end Insert

open Insert Insert.Univ

-- Typechecks:
#check insert [
  ('c', 3, 'd', Varchar(10) "Hello"),
  ('c', 2, 'e', Varchar(10) "Hi"),
  ('A', 90, 'F', Varchar(10) "My Varchar")
]

#check insert [
  (1, 100, 'c', 'd'),
  (20, 99, '@', 'x'),
  (100, 1, '$', '€')
]

-- Doesn't typecheck
-- #check insert [
--   ('a', 4, Varchar(2) "Hi"),
--   ("String", 3, 'd')
-- ]
-- 
-- #check insert [
--   (Varchar(255) "Hello World", 2, 'c'),
--   (Varchar(254) "Hello World", 100, 'A')
-- ]
-- 