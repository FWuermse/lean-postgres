/-
  Copyright (c) 2024 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Postgres.Schema.Utils

inductive Varchar (n : Nat) where
  | mk : (s: String) → (h : s.length <= n := by decide) → Varchar n

instance : ToString (Varchar i) where
  toString vc := match vc with
    | Varchar.mk s _ => s!"{s}"

inductive Date where
  | mk : (y : Nat) → (m : Fin 13) → (d : Fin 32) → (h : m > 0 ∧ d > 0 := by simp) →  Date

instance : ToString Date where
  toString date := match date with
    | Date.mk y m d _ => s!"{y}-{m}-{d}"

inductive Field
  | nat : String → Field
  | varchar (n : Nat) : String → Field
  | char : String → Field
  | date : String → Field
  deriving BEq, Repr, Hashable, Inhabited

def Field.ofSameType : Field → Field → Bool
  | .nat _, .nat _ => true
  | .varchar _ _, .varchar _ _ => true
  | .char _, .char _ => true
  | .date _, .date _ => true
  | _, _ => false

def Field.interp : Field → Type
  | .nat _ => Int
  | .varchar n _ => String
  | .char _ => Char
  | .date _ => Date

def Field.ToString : Field → String
  | nat s => s!"Nat {s}"
  | varchar n s => s!"Varchar {n} {s}"
  | char s => s!"Char {s}"
  | date s => s!"Date {s}"

def Field.getName : Field → String
  | nat s => s
  | varchar _ s => s
  | char s => s
  | date s => s

def Field.setName : Field → String → Field
  | nat _, new => nat new
  | varchar n _, new => varchar n new
  | char _, new => char new
  | date _, new => date new

instance : ToString Field :=
  ⟨Field.ToString⟩

inductive Literal
  | int (i : Int)
  | float (f : Float)
  | string (s : String)
  | field (f : Field)
  | nil
  deriving Inhabited

def Literal.interp : Literal → Type
  | .int _ => Int
  | .float _ => Float
  | .string _ => String
  | .field f => f.interp
  | nil => Literal

def NIL : Literal := .nil

instance : OfNat Literal n where
  ofNat := .int (Int.ofNat n)

instance : Coe Int Literal where
  coe  := .int

instance : Coe Float Literal where
  coe := .float

instance : OfScientific Literal where
  ofScientific m s e := .float (OfScientific.ofScientific m s e)

instance : Coe String Literal where
  coe := .string

instance : Coe Field Literal where
  coe := .field

protected def Literal.toString (e : Literal) : String :=
  match e with
  | .int e    => toString e
  | .float e  => optimizeFloatString $ toString e
  | .string e => s!"'{e}'"
  | .field f => f.getName
  | .nil     => "NULL"

instance : ToString Literal := ⟨Literal.toString⟩
