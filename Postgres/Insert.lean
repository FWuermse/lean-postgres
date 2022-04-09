import Lean

inductive Varchar (i : UInt8) where
  | mk : (s: String) → (h : s.length <= i.toNat := by simp) → Varchar i

instance : ToString (Varchar i) where
  toString vc := match vc with
    | Varchar.mk s _ => s

inductive Date where
  | mk : (y : Nat) → (m : Fin 13) → (d : Fin 32) → (h : m >= 1 ∧ d >= 1 := by simp) →  Date

instance : ToString Date where
  toString date := match date with
    | Date.mk y m d _ => s!"'{y}-{m}-{d}'"

inductive Univ
  | nat
  | char
  | varchar (n : UInt8)
  | date

def Univ.interp : Univ → Type
  | nat => Nat
  | char => Char
  | varchar n => Varchar n
  | date => Date

inductive Tuple : List Univ → Type
  | nil : Tuple []
  | cons (x : u.interp) (xs : Tuple us) : Tuple (u :: us)

namespace Insert

def Tuple.of {us: List Univ} (x : Tuple us) : List Univ := us

declare_syntax_cat sqlType
syntax char : sqlType
syntax num : sqlType
syntax "Varchar(" num ") " str : sqlType
syntax num "-" num "-" num : sqlType


syntax "(" sqlType,* ")" : term
macro_rules
  | `(( $elems,* )) => do
    let rec expandListLit (i : Nat) (skip : Bool) (result : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => match elems.elemsAndSeps[i] with
        | `(sqlType|$c:charLit) => expandListLit i true (← ``((Tuple.cons $c $result : Tuple (Univ.char::Tuple.of $result))))
        | `(sqlType|$n:numLit) => expandListLit i true (← ``((Tuple.cons ($n : Nat) $result : Tuple (Univ.nat::Tuple.of $result))))
        | `(sqlType|Varchar($n:numLit) $v:strLit) => expandListLit i true (← ``((Tuple.cons (Varchar.mk $v) $result : Tuple (Univ.varchar ($n)::Tuple.of $result)))) -- TODO nicer syntax for varchar len
        | `(sqlType|$y:numLit-$m:numLit-$d:numLit) => expandListLit i true (← ``((Tuple.cons (Date.mk $y $m $d) $result : Tuple (Univ.date::Tuple.of $result))))
        | _ => expandListLit i true  (← ``(Tuple.cons $(elems.elemsAndSeps[i]) $result))
    if elems.elemsAndSeps.size < 64 then
      expandListLit elems.elemsAndSeps.size false (← ``(Tuple.nil))
    else
      `(%[ $elems,* | Tuple.nil ])

inductive Response
-- TODO define proper response type

def insert {α : List Univ} (x : List (Tuple α)) : Response :=
  sorry -- TODO impelement insert

end Insert

open Insert

-- Typechecks:
#check insert [
  ('c', 3, 'd', Varchar(10) "Hello"),
  ('c', 2, 'e', Varchar(10) "Hi"),
  ('A', 90, 'F', Varchar(10) "My Varchar")
]

#check insert [
  (1, 100, 'c', 'd', 2011-11-11),
  (20, 99, '@', 'x', 2008-12-14),
  (100, 1, '$', '€', 2022-03-12)
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