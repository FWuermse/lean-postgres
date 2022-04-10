import Socket
import Postgres.Util
import Postgres.Response
import Lean

open List (map)
open Util
open Socket
open Response

open Lean Elab Meta 

class ToByteArray (α : Type u) where
  toByteArray : α → ByteArray

export ToByteArray (toByteArray)

inductive Varchar (i : UInt8) where
  | mk : (s: String) → (h : s.length <= i.toNat := by simp) → Varchar i

instance : ToString (Varchar i) where
  toString vc := match vc with
    | Varchar.mk s _ => s!"'{s}'"

inductive Date where
  | mk : (y : Nat) → (m : Fin 13) → (d : Fin 32) → (h : m > 0 ∧ d > 0 := by simp) →  Date

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

inductive TaggedUniv where
  | nat : Nat → TaggedUniv
  | char : Char → TaggedUniv
  | varchar : Varchar n → TaggedUniv
  | date : Date → TaggedUniv

def toTaggedUniv {u : Univ} (x : u.interp) : TaggedUniv := match u with
  | Univ.nat => TaggedUniv.nat (cast rfl x : Nat)
  | Univ.char => TaggedUniv.char (cast rfl x : Char)
  | Univ.varchar n => TaggedUniv.varchar (cast rfl x : Varchar n)
  | Univ.date => TaggedUniv.date (cast rfl x : Date)

def Tuple.toStringList : Tuple xs → List String
  | Tuple.nil => []
  | @Tuple.cons _ u y ys => match toTaggedUniv y with
    | TaggedUniv.nat n => s!"{n}"::ys.toStringList
    | TaggedUniv.char c => s!"'{c}'"::ys.toStringList
    | TaggedUniv.varchar vc => s!"{vc}"::ys.toStringList
    | TaggedUniv.date d => s!"{d}"::ys.toStringList

instance : ToString (Tuple u) where
  toString := (s!"({.})") ∘ ", ".intercalate ∘ Tuple.toStringList

def Tuple.of {us: List Univ} (x : Tuple us) : List Univ := us

namespace Insert

structure InsertType where
  method : Char
  length : UInt32
  insert : String
  «postfix» : UInt8

instance : ToByteArray InsertType where
  toByteArray it := foldByteArray [
    it.method.toString.toUTF8,
    uInt32ToByteArray it.length,
    it.insert.toUTF8,
    ByteArray.mk #[it.postfix]
  ]

structure InsertQuery {α : List Univ} where
  table : String
  values : List (Tuple α)


declare_syntax_cat sqlType
syntax char : sqlType
syntax num : sqlType
syntax "Varchar(" num ") " str : sqlType
syntax num "-" num "-" num : sqlType

syntax:1000 "(" sqlType,* ")" : term

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
        | _ => expandListLit i true  (← ``(Tuple.cons $(elems.elemsAndSeps[i]) $result)) -- TODO throw error here
    if elems.elemsAndSeps.size < 64 then
      expandListLit elems.elemsAndSeps.size false (← ``(Tuple.nil))
    else
      `(%[ $elems,* | Tuple.nil ])

def parseInsertResponse (socket : Socket) : IO String := do
  let method := Char.ofNat (← socket.recv 1)[0].toNat
  if method = 'C' then
    let length := toUInt32LE $ ← socket.recv 4
    let responseMsg := takeNAsStr length.toNat (← socket.recv (length - 4).toUSize)
    let method := Char.ofNat (← socket.recv 1)[0].toNat
    let length := toUInt32LE $ ← socket.recv 4
    let status := takeNAsStr length.toNat (← socket.recv (length -4).toUSize)
    pure $ responseMsg.fst.dropRight 1
  else
    -- TODO parse error
    IO.println "Error with insert response"
    pure ""


def insert {α : List Univ} (socket : Socket) (insert : @InsertQuery α) : IO String := do
  let rows := ", ".intercalate $ map toString insert.values
  let query := s!"INSERT INTO {insert.table} VALUES {rows};"
  let insertType := InsertType.mk 'Q' (query.length.toUInt32 + 6) query 0
  let req ← socket.send ∘ toByteArray $ insertType
  parseInsertResponse socket

syntax "INSERT INTO " ident " VALUES " : term

macro_rules
  | `(INSERT INTO $id:ident VALUES $values) => ``(InsertQuery.mk $(quote id.getId.toString) $values)

end Insert
