/-
  Copyright (c) 2024 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres.Util
import Postgres.DSL.Literal

open Util Literal

class ToByteArray (α : Type u) where
  toByteArray : α → ByteArray

export ToByteArray (toByteArray)

inductive Univ
  | nat
  | char
  | varchar (n : Nat)
  | date

def Univ.interp : Univ → Type
  | nat => Nat
  | char => Char
  | varchar n => Varchar n
  | date => Date

def Univ.toString : Univ → String
  | nat => "INT"
  | char => "CHAR"
  | varchar n => s!"Varchar({n})"
  | date => "DATE"

instance : ToString Univ :=
  ⟨Univ.toString⟩

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
  | @Tuple.cons _ _ y ys => match toTaggedUniv y with
    | TaggedUniv.nat n => s!"{n}"::ys.toStringList
    | TaggedUniv.char c => s!"{c}"::ys.toStringList
    | TaggedUniv.varchar vc => s!"{vc}"::ys.toStringList
    | TaggedUniv.date d => s!"{d}"::ys.toStringList

instance : ToString (Tuple u) where
  toString := (s!"({.})") ∘ ", ".intercalate ∘ Tuple.toStringList

def Tuple.of {us: List Univ} (_ : Tuple us) : List Univ := us

namespace InsertDSL

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
  -- TODO: fieldNames : List String
