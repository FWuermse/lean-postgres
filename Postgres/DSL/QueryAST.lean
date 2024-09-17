import Lean
open Lean Syntax

namespace QueryAST

-- instance LawfulBEq
inductive DataType
  | null
  | integer
  | bigInt
  | bit
  | varbit
  | boolean
  | char
  | varchar
  | date
  | text
  | double
  deriving BEq, DecidableEq, Repr

def DataType.toString
  | null    => "null"
  | integer => "integer"
  | bigInt  => "bigInt"
  | bit     => "bit"
  | varbit  => "varbit"
  | boolean => "boolean"
  | char    => "char"
  | varchar => "varchar"
  | date    => "date"
  | text    => "text"
  | double  => "double"

instance : ToString DataType :=
  ⟨DataType.toString⟩

instance : LawfulBEq DataType where
  eq_of_beq := by
    intro a b hab
    rw [BEq.beq] at hab <;>
    cases a <;>
    cases b <;>
    try contradiction <;>
    rfl
    repeat rfl
  rfl := by
    intro h
    . rw [BEq.beq]
      cases h <;> rfl

abbrev RelationType := List (String × String × DataType)

abbrev Schema := List (String × RelationType)

/-
# Value

Following https://www.postgresql.org/docs/current/datatype.html
-/
inductive Value
  | bigInt (i : Int) (stx : Syntax)
  | bit (len : Nat) (stream : Array Bool) (stx : Syntax)
  | boolean (b : Bool) (stx : Syntax)
  | char (len : Nat) (string : String) (stx : Syntax)
  | date (year : Nat) (month : Fin 13) (day : Fin 32) (stx : Syntax)
  | double (d : Float) (stx : Syntax)
  | integer (i : Int) (stx : Syntax)
  | null (stx : Syntax)
  | text (value : String) (stx : Syntax)
  | varbit (len : Nat) (stream : Array Bool) (stx : Syntax)
  | varchar (len : Nat) (string : String) (stx : Syntax)

def Value.toString
  | Value.bigInt i _ => s!"{i}"
  | Value.bit _ s _ => s!"{s}"
  | Value.boolean b _ =>
    match b with
    | true => "TRUE"
    | false => "FALSE"
  | Value.char _ s _ => s
  | Value.date y m d _ => s!"{y}-{m}-{d}"
  | Value.double d _ => s!"{d}"
  | Value.integer i _ => s!"{i}"
  | Value.null _ => "NULL"
  | Value.text t _ => t
  | Value.varbit _ s _ => s!"{s}"
  | Value.varchar _ s _ => s

instance : ToString Value :=
  ⟨Value.toString⟩

inductive Join
  | inner (stx : Syntax)
  | left (stx : Syntax)
  | right (stx : Syntax)
  | outer (stx : Syntax)

def Join.toString : Join → String
  | inner _ => "INNER"
  | left  _ => "LEFT"
  | right _ => "RIGHT"
  | outer _ => "OUTER"

instance : ToString Join := ⟨Join.toString⟩

/-
# Operators

Following the grammar of https://www.postgresql.org/docs/current/sql-syntax-lexical.html#SQL-SYNTAX-OPERATORS
-/
inductive BoolBinOp
  | and
  | or
  deriving DecidableEq, Repr

inductive AExprCmpOp
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
  deriving DecidableEq, Repr

inductive AExprOp
  | add
  | sub
  | mul
  | div
  | mod
  | con
  deriving DecidableEq, Repr

inductive UnaryOp
  | add
  | sub
  | not
  deriving DecidableEq, Repr

inductive Operator
  | acop (op : AExprCmpOp)
  | aop (op : AExprOp)
  | bop (op : BoolBinOp)
  deriving DecidableEq, Repr

def Operator.toString
  | acop .eq => " = "
  | acop .ge => " > "
  | acop .gt => " >= "
  | acop .le => " <= "
  | acop .lt => " < "
  | acop .ne => " <> "
  | aop .add => " + "
  | aop .con => " || "
  | aop .div => " / "
  | aop .mod => " % "
  | aop .mul => " * "
  | aop .sub => " - "
  | bop .and => " AND "
  | bop .or => " OR "

def UnaryOp.toString
  | add => "+"
  | not => "NOT "
  | sub => "-"

instance : ToString Operator :=
  ⟨Operator.toString⟩

/-
# Value Expression

Following the grammar of https://www.postgresql.org/docs/current/sql-expressions.html

## DataType T
DataType

## Context Ctx
RelationType (contents of the From-clause Type)
-/
inductive Expression
  | value (l : Value) (stx : Syntax)
  | field (name : String) (table : String) (stx : Syntax)
  | bin (lhs : Expression) (op : Operator) (rhs : Expression) (stx : Syntax)
  | un (op : UnaryOp) (expr : Expression) (stx : Syntax)
  -- | function (name : String) (params : List Expression)

def Expression.toString
  | Expression.value v _ => s!"{v}"
  | Expression.field n t _ => s!"{t}.{n}"
  | Expression.bin l o r _ => s!"{l.toString} {o} {r.toString}"
  | Expression.un o e _ => o.toString ++ e.toString

instance : ToString Expression :=
  ⟨Expression.toString⟩

/-
# SelectField

## DataType T
DataType

## Context Ctx
RelationType

## Predicates
(name, _) ∈ Ctx
-/
inductive SelectField
  | col (name : String) (table : String) (stx : Syntax)
  | alias (name : String) (table : String) («alias» : String)

def SelectField.toString
  | col n t _ => s!"{t}.{n}"
  | .alias n t a => s!"{t}.{n} AS {a}"

def SelectField.name
  | col n t _ => s!"{t}.{n}"
  | «alias» n t _ => s!"{t}.{n}"

instance : ToString SelectField :=
  ⟨SelectField.toString⟩

def SelectField.postfix
  | col s _ _ => s
  | «alias» s _ _ => s

def SelectField.getTuple (T : RelationType) : SelectField → Option (String × String × DataType)
  | col n t _ => T.find? fun (name, table, _) => n == name && t == table
  | «alias» n t a =>
    match T.find? fun (name, table, _) => n == name && t == table with
    | .some (_, table, type) => (a, table, type)
    | .none => .none

/-
# Select

## DataType T
RelationType

## Context Ctx
RelationType

## Predicates
list: ∀ s ∈ List SelectFields, WellFormedSelectField s
all: ∀ x ∈ T, x ∈ Γ
-/
inductive Select
  | list (distinct : Bool) (sf : List SelectField) (stx : Syntax)
  | all  (distinct : Bool) (stx : Syntax)

def Select.toString
  | Select.list d sf _ =>
    match d with
    | true => ("DISTINCT" ++ (", ".intercalate <| sf.map fun sf => s!"{sf}"))
    | false => ", ".intercalate <| sf.map fun sf => s!"{sf}"
  | Select.all d _ =>
    match d with
    | true => "DISTRINCT *"
    | false => "*"

instance : ToString Select :=
  ⟨Select.toString⟩

/-
# From

## DataType T
RelationType

## Context Ctx
Schema

## Predicates
table: (name, T) ∈ Ctx
alias: WellFormedFrom ∧ (alias, _) ∉ Ctx (maybe?)
join/implicitJoin: WellFormedFrom₁ ∧ WellFormedFrom₂ ∧ T = a ++ b ∧ WellFormedProp
nestedJoin: WellFormedQuery q
-/
-- replace with simpler version where possible (table (name : String))
inductive From where
  | table (name : String) (stx : Syntax)
  | alias (frm : From) (als : String) (stx : Syntax)
  | join (jOp : Join) (fst : From) (snd : From) (onCond : Expression) (stx : Syntax)
  | implicitJoin (fst : From) (snd : From) (stx : Syntax)
  --| joinUsing (fst : From) (snd : From) (cols : List Expression)
  -- Nested join must have alias (see: https://www.postgresql.org/docs/current/queries-table-expressions.html#QUERIES-SUBQUERIES)
  | nestedJoin (sel : Select) (frm : From) (whr : Expression) (als : String) (stx : Syntax)

def From.toString
  | From.table n _ => n
  | From.alias f a _ => s!"{f.toString} AS {a}"
  | From.join o l r c _ => s!"{l.toString} {o} {r.toString} {c}"
  | From.implicitJoin l r _ => s!"{l.toString}, {r.toString}"
  | From.nestedJoin s f w a _ => s!"(SELECT {s} FROM {f.toString} WHERE {w}) AS {a}"

instance : ToString From :=
  ⟨From.toString⟩

/-
# Query

## DataType T
RelationType

## Context Ctx
Schema

## Predicates
WellDataTyped Select in ctx
WellDataTyped From in ctx
WellDataTyped Where in ctx
-/
structure Query where
  select : Select
  «from» : From
  «where» : Expression
  «syntax» : Syntax

def Query.toString
  | Query.mk s f w _ => s!"SELECT {s} FROM {f} WHERE {w}"

instance : ToString Query :=
  ⟨Query.toString⟩

end QueryAST
