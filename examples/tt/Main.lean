import Lean

@[simp]
def Forall (p : α → Prop) : List α → Prop
  | [] => True
  | x :: [] => p x
  | x :: l => p x ∧ Forall p l

namespace Forall

theorem and_true_iff : p ∧ True ↔ p := iff_of_eq (and_true _)

@[simp]
theorem forall_cons (p : α → Prop) (x : α) : ∀ l : List α, Forall p (x :: l) ↔ p x ∧ Forall p l
  | [] => (and_true_iff).symm
  | _ :: _ => Iff.rfl

@[simp]
theorem forall_iff_forall_mem : ∀ {l : List α}, Forall p l ↔ ∀ x ∈ l, p x
  | [] => (iff_true_intro <| List.forall_mem_nil _).symm
  | x :: l => by rw [List.forall_mem_cons, forall_cons, forall_iff_forall_mem]

@[simp]
instance (p : α → Prop) [DecidablePred p] : DecidablePred (Forall p) := fun _ =>
  decidable_of_iff' _ forall_iff_forall_mem

end Forall

open Lean Syntax

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
  | date (year : Nat) (month : Fin 13) (year : Fin 32) (stx : Syntax)
  | double (d : Float) (stx : Syntax)
  | integer (i : Int) (stx : Syntax)
  | null (stx : Syntax)
  | text (value : String) (stx : Syntax)
  | varbit (len : Nat) (stream : Array Bool) (stx : Syntax)
  | varchar (len : Nat) (string : String) (stx : Syntax)

inductive WellFormedValue : Value → DataType → Prop
  | bigInt : i < Int.ofNat 2^64 → i > -Int.ofNat 2^64 → WellFormedValue (.bigInt i stx) .bigInt
  | bit : b.size = n → WellFormedValue (.bit n b stx) .bit
  | boolean : WellFormedValue (.boolean b stx) .boolean
  | char : s.length = n → WellFormedValue (.char n s stx) .char
  | date : m > 0 ∧ d > 0 → WellFormedValue (.date y m d stx) .date
  | double : WellFormedValue (.double f stx) .double
  | integer : i < Int.ofNat 2^32 → i > -Int.ofNat 2^32 → WellFormedValue (.integer i stx) .integer
  | null : WellFormedValue (.null stx) .null
  | text : WellFormedValue (.text s stx) .text
  | varbit : b.size ≤ n → WellFormedValue (.varbit n b stx) .varbit
  | varchar : s.length ≤ n → WellFormedValue (.varchar n s stx) .varchar

/-
When two compatible types are used in the same expression the more general will be the output type.
This only works for a subset of types such as number or text types.

Following the conversion of:
  https://www.postgresql.org/docs/current/functions-math.html
  https://www.postgresql.org/docs/current/datatype-character.html
  https://www.postgresql.org/docs/current/functions-datetime.html
-/
inductive WellFormedNumConv : DataType → DataType → DataType → Prop
  -- Cover each relevant case for partMoreGeneral
  | eq :
    a = .integer ∨ a = .bigInt ∨ a = .double →
    b = a →
    ----------------------------------
    WellFormedNumConv a b a
  | intBigInt :
    a = .integer →
    b = .bigInt →
    ----------------------------------
    WellFormedNumConv a b .bigInt
  | bigIntDouble :
    a = .bigInt →
    b = .double →
    ----------------------------------
    WellFormedNumConv a b .double
  | intDouble :
    a = .integer →
    b = .double →
    ----------------------------------
    WellFormedNumConv a b .double
  | symm :
    WellFormedNumConv a b T →
    ----------------------------------
    WellFormedNumConv b a T

inductive WellFormedCharConv : DataType → DataType → DataType → Prop
  | char :
    a = .char ∨ a = .varchar ∨ a = .text →
    b = a →
    ----------------------------------
    WellFormedCharConv a b a
  | cvc :
    a = .char →
    b = .varchar →
    WellFormedCharConv a b .varchar
  | vctx :
    a = .varchar →
    b = .text →
    WellFormedCharConv a b .text
  | ctx :
    a = .char →
    b = .text →
    WellFormedCharConv a b .text
  | symm :
    WellFormedCharConv a b T →
    ----------------------------------
    WellFormedCharConv b a T

inductive WellFormedConv : DataType → DataType → Prop
  | numeric :
    WellFormedNumConv T₁ T₂ T₃ →
    WellFormedConv T₁ T₂
  | char :
    WellFormedCharConv T₁ T₂ T₃ →
    WellFormedConv T₁ T₂
  | eq :
    T₁ = T₂ →
    WellFormedConv T₁ T₂

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

/-
# Expression Typing Judgements
Following the comparison from:
  https://www.postgresql.org/docs/current/functions-logical.html
  https://www.postgresql.org/docs/current/functions-comparison.html
  https://www.postgresql.org/docs/current/functions-math.html
  https://www.postgresql.org/docs/current/functions-datetime.html
  https://www.postgresql.org/docs/current/functions-string.html
-/
inductive WellFormedExpression : RelationType → Expression → DataType → Prop
  | value v :
    WellFormedValue v T →
    ----------------------------------
    WellFormedExpression Γ (.value v stx) T
  | field :
    (name, table, T) ∈ Γ →
    ----------------------------------
    WellFormedExpression Γ (.field name table stx) T
  | fieldPostfix (t : String) :
    Γ.count (name, t, T) = 1 →
    ----------------------------------
    WellFormedExpression Γ (.field name t stx) T
  | not :
    WellFormedExpression Γ e .boolean →
    ----------------------------------
    WellFormedExpression Γ (.un .not e stx) .boolean
  -- Bool not otherwise comparable (see: https://www.postgresql.org/docs/current/functions-logical.html)
  | bcmp :
    WellFormedExpression Γ lhs .boolean →
    WellFormedExpression Γ rhs .boolean →
    ----------------------------------
    WellFormedExpression Γ (.bin lhs (.bop op) rhs stx) .boolean
  | acmp :
    WellFormedExpression Γ lhs T₁ →
    WellFormedExpression Γ rhs T₂ →
    WellFormedConv T₁ T₂ →
    ----------------------------------
    WellFormedExpression Γ (.bin lhs (.acop op) rhs stx) .boolean
  | aexpr :
    WellFormedExpression Γ lhs T₁ →
    WellFormedExpression Γ rhs T₂ →
    WellFormedNumConv T₁ T₂ T →
    ----------------------------------
    WellFormedExpression Γ (.bin lhs (.aop op) rhs stx) T
 | concat :
    -- Inference is not bidirectional (see: https://www.postgresql.org/docs/current/functions-string.html)
    WellFormedExpression Γ lhs .text →
    WellFormedExpression Γ rhs T₂ →
    -- Also must check for non-array (however array not yet supported)
    ----------------------------------
    WellFormedExpression Γ (.bin lhs (.aop .con) rhs stx) .text
  | pos :
    WellFormedExpression Γ e T →
    T = .integer ∨ T = .bigInt ∨ T = .double →
    ----------------------------------
    WellFormedExpression Γ (.un .add e stx) T
  | neg :
    WellFormedExpression Γ e T →
    T = .integer ∨ T = .bigInt ∨ T = .double →
    ----------------------------------
    WellFormedExpression Γ (.un .sub e stx) T
  -- Date ops are not symmetrical (see: https://www.postgresql.org/docs/current/functions-datetime.html)
  | dateadd :
    WellFormedExpression Γ lhs .date →
    WellFormedExpression Γ rhs .integer →
    ----------------------------------
    WellFormedExpression Γ (.bin lhs (.aop .add) rhs stx) .date
  | datesub :
    WellFormedExpression Γ lhs .date →
    WellFormedExpression Γ rhs .integer →
    ----------------------------------
    WellFormedExpression Γ (.bin lhs (.aop .sub) rhs stx) .date

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

inductive WellFormedSelectField : RelationType → SelectField → DataType → Prop
  | col :
    (name, table, T) ∈ Γ →
    ----------------------------------
    WellFormedSelectField Γ (.col name table stx) T
    -- Postgres doesn't support nested aliases such as 'a AS b, b AS c'
  | alias :
    (name, table, T) ∈ Γ →
    ----------------------------------
    WellFormedSelectField Γ (.alias name table a) T

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

/-
TODO: support for functions such as count etc.
-/
inductive WellFormedSelect : RelationType → Select → RelationType → Prop
  | list (ss : List SelectField) :
    Forall (∃t, WellFormedSelectField Γ . t) ss →
    (T = ss.filterMap fun s => s.getTuple Γ) →
    ----------------------------------
    WellFormedSelect Γ (.list b ss stx) T
  | all :
    Γ = T →
    ----------------------------------
    WellFormedSelect Γ t T

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

inductive WellFormedFrom : Schema → From → RelationType → Prop
  | table :
    (name, T) ∈ Γ →
    ----------------------------------
    WellFormedFrom Γ (.table name stx) T
  -- From aliases override the from table information: https://www.postgresql.org/docs/7.1/queries.html#QUERIES-WHERE
  | alias :
    WellFormedFrom Γ f T →
    u = (T.map fun (name, _, ty) => (name, tableAlias, ty)) →
    ----------------------------------
    WellFormedFrom Γ (.alias f tableAlias stx) u
  | join :
    WellFormedFrom Γ f₁ T₁ →
    WellFormedFrom Γ f₂ T₂ →
    WellFormedExpression (T₁ ++ T₂) e .boolean →
    ----------------------------------
    WellFormedFrom Γ (.join j f₁ f₂ e stx) (T₁ ++ T₂)
    -- See https://www.postgresql.org/docs/current/queries-table-expressions.html#QUERIES-JOIN
/-   | joinUsing (cols : List String) :
    WellFormedFrom Γ f₁ T₁ →
    WellFormedFrom Γ f₂ T₂ →
    Forall (fun s => ∃ t T, WellFormedExpression (T₁ ∪ T₂) (.field s t) T) cols →
    ----------------------------------
    WellFormedFrom Γ (.joinUsing f₁ f₂ e) ((T₁ ∪ T₂).filter fun (a, _, _) => a ∈ cols) -/
  | implicitJoin :
    WellFormedFrom Γ f₁ T₁ →
    WellFormedFrom Γ f₂ T₂ →
    ----------------------------------
    WellFormedFrom Γ (.implicitJoin f₁ f₂ stx) (T₁ ++ T₂)
  | nestedFrom :
    WellFormedSelect Tf s Ts →
    WellFormedFrom Γ f Tf →
    WellFormedExpression Tf e .boolean →
    -- Nested join must have alias (see: https://www.postgresql.org/docs/current/queries-table-expressions.html#QUERIES-SUBQUERIES)
    u = (Ts.map fun (name, _, ty) => (name, tableAlias, ty)) →
    ----------------------------------
    WellFormedFrom Γ (.nestedJoin s f e tableAlias stx) u

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

inductive WellFormedQuery : Schema → Query → RelationType → Prop
  | mk :
    WellFormedSelect Tf s Ts →
    WellFormedFrom Γ f Tf →
    WellFormedExpression Tf e .boolean →
    ----------------------------------
    WellFormedQuery Γ ⟨s, f, e, stx⟩ Ts

def getFromTable (Γ : Schema) : (t : From) → Except (String × Syntax) RelationType
  | .table name stx =>
    let table := Γ.find? fun (n, _) => n == name
    match table with
    | .some (_, t) => .ok t
    | .none => .error (s!"Could not find table {name}", stx)
  | .alias frm a _ => do
    let rt ← getFromTable Γ frm
    return rt.map fun (n, _, T) => (n, a, T)
  | .implicitJoin frm₁ frm₂ _ => do
    let fst ← getFromTable Γ frm₁
    let snd ← getFromTable Γ frm₂
    return fst ++ snd
  | .join _ frm₁ frm₂ _ _ => do
    let fst ← getFromTable Γ frm₁
    let snd ← getFromTable Γ frm₂
    return fst ++ snd
  | .nestedJoin s f _ a _ =>
    match s with
    | .all _ _ => do
      let fromTable ← getFromTable Γ f
      return fromTable.map fun (n, _, T) => (n, a, T)
    | .list _ ss _ => do
      let fromTable ← getFromTable Γ f
      let res := ss.filterMap (fun s => SelectField.getTuple fromTable s)
      return res.map fun (n, _, T) => (n, a, T)

@[simp]
def checkSelectField (Γ : RelationType) (s : SelectField) (T : DataType) : Except String (Σ' T, WellFormedSelectField Γ s T) :=
  match s with
  | .col name table _ => do
    if h : (name, table, T) ∈ Γ then
      pure ⟨T, WellFormedSelectField.col h⟩
    else
      .error s!"Selected field {table}.{name} is not in the current context."
  | .alias name table a =>
    if h : (name, table, T) ∈ Γ then
      pure ⟨T, WellFormedSelectField.alias h⟩
    else
      .error s!"Selected field {table}.{name} as {a} is not in the current context."

-- (Maybe remove dicidable)
instance (Γ : RelationType) (T : DataType) : DecidablePred (fun s : SelectField => (checkSelectField Γ s T).isOk) :=
  fun s =>
    match s with
    | .col name table _ =>
      if h : (name, table, T) ∈ Γ then
        isTrue (by simp [h]; rfl)
      else
        isFalse (by simp [h]; rfl)
    | .alias name table a =>
      if h : (name, table, T) ∈ Γ then
        isTrue (by simp [h]; rfl)
      else
        isFalse (by simp [h]; rfl)

instance (Γ : RelationType) (s : SelectField) : Decidable (∃T, WellFormedSelectField Γ s T) :=
  match s with
  | .col name table _ =>
      match hfind : Γ.find? fun (n, t, _) => (n, t) = (name, table) with
      | .some (n, t, T) =>
        isTrue (by
          simp_all
          apply Exists.intro
          have hmem : (name, table, T) ∈ Γ :=
            (by
              have h_eq : n = name ∧ t = table := (by
                have h := List.find?_some hfind
                have ht_eq : (n, t) = (name, table) := by
                  simp [eq_true_of_decide] at h
                  simp
                  exact h
                cases ht_eq
                apply And.intro <;> rfl)
              apply List.mem_of_find?_eq_some
              . exact h_eq.left ▸ h_eq.right ▸ hfind)
          apply WellFormedSelectField.col hmem)
        | .none => isFalse (by
          simp_all [not_exists, List.find?_eq_none]
          intro dt
          have h_neq : (name, table, dt) ∉ Γ  := (by
            intro hmem
            have hfalse := hfind (name, table, dt) hmem
            apply hfalse <;> rfl)
          intro wfsf
          cases wfsf
          apply h_neq
          assumption)
  | .alias name table a =>
      match hfind : Γ.find? fun (n, t, _) => (n, t) = (name, table) with
      | .some (n, t, T) =>
        isTrue (by
          simp_all
          apply Exists.intro
          have hmem : (name, table, T) ∈ Γ :=
            (by
              have h_eq : n = name ∧ t = table := (by
                have h := List.find?_some hfind
                have ht_eq : (n, t) = (name, table) := by
                  simp [eq_true_of_decide] at h
                  simp
                  exact h
                cases ht_eq
                apply And.intro <;> rfl)
              apply List.mem_of_find?_eq_some
              . exact h_eq.left ▸ h_eq.right ▸ hfind)
          apply WellFormedSelectField.alias hmem)
        | .none => isFalse (by
          simp_all [not_exists, List.find?_eq_none]
          intro dt
          have h_neq : (name, table, dt) ∉ Γ  := (by
            intro hmem
            have hfalse := hfind (name, table, dt) hmem
            apply hfalse <;> rfl)
          intro wfsf
          cases wfsf
          apply h_neq
          assumption)

def checkSel (Γ T : RelationType) (s : Select) : Except (String × Syntax) (Σ' T, WellFormedSelect Γ s T) :=
  match s with
  | .all _ stx =>
    if h : Γ = T then
      let wsel := WellFormedSelect.all h
      pure ⟨T, wsel⟩
    else
      .error (s!"The type T: {T} of `SELECT *` must match the FROM clause {Γ}.", stx)
  | .list _ ss stx => do
    let T := ss.filterMap fun s => SelectField.getTuple Γ s
    if h : Forall (fun s : SelectField => ∃ t, WellFormedSelectField Γ s t) ss then
      pure ⟨T, WellFormedSelect.list ss h rfl⟩
    else
      .error (s!"All selected fields {ss} must be well formed in the context {Γ}.", stx)

def checkValue (v : Value) : Except (String × Syntax) (Σ' T, WellFormedValue v T) :=
  match v with
  | .null _ => pure ⟨.null, .null⟩
  | .integer i stx => do
    if h₁ : i < 2^32 then
      if h₂ : i > -2^32 then
        pure ⟨.integer, .integer h₁ h₂⟩
      else
        .error (s!"Integer value of {i} causes an overflow.", stx)
    else
      .error (s!"Integer value of {i} causes an overflow.", stx)
  | .bigInt i stx => do
    if h₁ : i < 2^64 then
      if h₂ : i > -2^64 then
        pure ⟨.bigInt, .bigInt h₁ h₂⟩
      else
        .error (s!"Integer value of {i} causes an overflow.", stx)
    else
      .error (s!"Integer value of {i} causes an overflow.", stx)
  | .bit n ba stx => if h : ba.size = n then
      pure ⟨.bit, .bit h⟩
    else
      .error (s!"ByteStream {ba} must have exactly length {n}", stx)
  | .varbit n ba stx => if h : ba.size ≤ n then
      pure ⟨.varbit, .varbit h⟩
    else
      .error (s!"ByteStream {ba} must not exceed length {n}", stx)
  | .boolean _ _ => pure ⟨.boolean, .boolean⟩
  | .char n s stx => if h : s.length = n then
      pure ⟨.char, .char h⟩
    else
      .error (s!"String {s} must have exactly length {n}", stx)
  | .varchar n s stx => if h : s.length ≤ n then
      pure ⟨.varchar, .varchar h⟩
    else
      .error (s!"String {s} must not exceed length {n}", stx)
  | .date y m d stx => if h : m > 0 ∧ d > 0 then
      pure ⟨.date, .date h⟩
    else
      .error (s!"Invalid date: {y}-{m}-{d}", stx)
  | .text _ _ => pure ⟨.text, .text⟩
  | .double _ _ => pure ⟨.double, .double⟩

def checkNumConv (fst : DataType) (snd : DataType) : Except String (Σ' T, WellFormedNumConv fst snd T) :=
  if hfst : fst = DataType.integer ∨ fst = .bigInt ∨ fst = .double then
    if hsnd : snd = fst then
      pure ⟨fst, .eq hfst hsnd⟩
    else
      match fst, snd with
      | .integer, .bigInt => pure ⟨_, .intBigInt rfl rfl⟩
      | .integer, .double => pure ⟨_, .intDouble rfl rfl⟩
      | .bigInt, .double => pure ⟨_, .bigIntDouble rfl rfl⟩
      | .bigInt, .integer => pure ⟨_, .symm <| .intBigInt rfl rfl⟩
      | .double, .integer => pure ⟨_, .symm <| .intDouble rfl rfl⟩
      | .double, .bigInt => pure ⟨_, .symm <| .bigIntDouble rfl rfl⟩
      | _, _ => .error s!"{fst} and {snd} are not comparable number types."
  else
    .error s!"{fst} and {snd} are not comparable number types"

def checkCharConv (fst : DataType) (snd : DataType) : Except String (Σ' T, WellFormedCharConv fst snd T) :=
  if hfst : fst = DataType.char ∨ fst = .varchar ∨ fst = .text then
    if hsnd : snd = fst then
      pure ⟨fst, WellFormedCharConv.char hfst hsnd⟩
    else
      match fst, snd with
      | .char, .varchar => pure ⟨_, .cvc rfl rfl⟩
      | .char, .text => pure ⟨_, .ctx rfl rfl⟩
      | .varchar, .text => pure ⟨_, .vctx rfl rfl⟩
      | .varchar, .char => pure ⟨_, .symm <| .cvc rfl rfl⟩
      | .text, .char => pure ⟨_, .symm <| .ctx rfl rfl⟩
      | .text, .varchar => pure ⟨_, .symm <| .vctx rfl rfl⟩
      | _, _ => .error s!"{fst} and {snd} are not comparable char types."
  else
    .error s!"{fst} and {snd} are not comparable char types"

def checkConv (fst : DataType) (snd : DataType) : Except String (PLift <| WellFormedConv fst snd) := do
  if let .ok ⟨_, h⟩ := checkNumConv fst snd then
    return PLift.up <| .numeric h
  else
    if let .ok ⟨_, h⟩ := checkCharConv fst snd then
      return PLift.up <| .char h
    else
      if h : fst = snd then
        return PLift.up <| WellFormedConv.eq h
      else
        .error "Types {fst} and {snd} are not comparable"

def checkExpression (Γ : RelationType) (e : Expression) : Except (String × Syntax) (Σ' T, WellFormedExpression Γ e T) :=
  match e with
  | .value v _ => do
    let ⟨T, hv⟩ ← checkValue v
    pure ⟨T, .value v hv⟩
  | .field name table stx =>
    let field := (Γ.find? fun (n, _) => n == name).orElse fun _ => (Γ.find? fun (n, _) => n == name)
    if let .some (_, _, t) := field then
      if h : (name, table, t) ∈ Γ then
        let waexpr := WellFormedExpression.field
        pure ⟨t, waexpr h⟩
      else
        .error (s!"The field {name} is not present in this context {Γ}.", stx)
    else
      .error (s!"The field {name} is not present in this context {Γ}.", stx)
  | .un .not bexpr stx => do
    let ⟨T, wbe⟩ ← checkExpression Γ bexpr
    if h : T = .boolean then
      pure ⟨.boolean, .not <| h ▸ wbe⟩
    else
      .error ("Only boolean expressions can be negated.", stx)
  | .un op aexpr stx => do
    let ⟨T, wae⟩ ← checkExpression Γ aexpr
    if h : T = .integer ∨ T = .bigInt ∨ T = .double then
      match op with
      | .add => pure ⟨T, .pos wae h⟩
      | .sub => pure ⟨T, .neg wae h⟩
      | _ => .error (s!"Only numeric expressions can have a sign. {T} is not numeric.", stx)
    else
      .error (s!"Only numeric expressions can have a sign. {T} is not numeric.", stx)
  | .bin bexpr₁ (.bop op) bexpr₂ stx => do
    let ⟨T₁, fst⟩ ← checkExpression Γ bexpr₁
    let ⟨T₂, snd⟩ ← checkExpression Γ bexpr₂
    if h₁ : T₁ = .boolean then
      if h₂ : T₂ = .boolean then
          pure ⟨.boolean, .bcmp (h₁ ▸ fst) (h₂ ▸ snd)⟩
      else
        .error (s!"Operator{(Operator.bop op)}only supports boolean expressions on rhs: {T₂}.", stx)
    else
      .error (s!"Operator{(Operator.bop op)}only supports boolean expressions on lhs: {T₁}.", stx)
  | .bin aexpr₁ (.acop _) aexpr₂ stx => do
    let ⟨a₁, fst⟩ ← checkExpression Γ aexpr₁
    let ⟨a₂, snd⟩ ← checkExpression Γ aexpr₂
    let wf ← match checkConv a₁ a₂ with
    | .ok r => pure r
    | .error e => .error (e, stx)
    return ⟨.boolean, .acmp fst snd wf.down⟩
  | .bin aexpr₁ (.aop op) aexpr₂ stx => do
    let ⟨a₁, fst⟩ ← checkExpression Γ aexpr₁
    let ⟨a₂, snd⟩ ← checkExpression Γ aexpr₂
    if h : a₁ = .date ∧ a₂ = .integer then
      match op with
      | .add => return ⟨.date, .dateadd (h.left ▸ fst) (h.right ▸ snd)⟩
      | .sub => return ⟨.date, .datesub (h.left ▸ fst) (h.right ▸ snd)⟩
      | _ => .error (s!"Invalid operationr {(Operator.aop op)} on type Date.", stx)
    else
      let wf ← match checkNumConv a₁ a₂ with
      | .ok r => pure r
      | .error e => .error (e, stx)
      return ⟨wf.fst, .aexpr fst snd wf.snd⟩

def checkFrom (Γ : Schema) (T : RelationType) (t : From) : Except (String × Syntax) (Σ' T, WellFormedFrom Γ t T) :=
  match t with
  | .table name stx =>
    if mem : (name, T) ∈ Γ then
      let wfrm := .table mem
      pure ⟨T, wfrm⟩
    else
      .error (s!"Table {name} : {T} not in Schema {Γ}.", stx)
  | .alias frm a _ => do
    let ⟨T, wfrm⟩ ← checkFrom Γ (← getFromTable Γ frm) frm
    pure ⟨T.map fun (n, _, ty) => (n, a, ty), .alias wfrm rfl⟩
  | .implicitJoin frm₁ frm₂ _ => do
    let ⟨T₁, wfrm₁⟩ ← checkFrom Γ (← getFromTable Γ frm₁) frm₁
    let ⟨T₂, wfrm₂⟩ ← checkFrom Γ (← getFromTable Γ frm₂) frm₂
    pure ⟨T₁++T₂, .implicitJoin wfrm₁ wfrm₂⟩
  | .join _ frm₁ frm₂ prop stx => do
    let ⟨T₁, wfrm₁⟩ ← checkFrom Γ (← getFromTable Γ frm₁) frm₁
    let ⟨T₂, wfrm₂⟩ ← checkFrom Γ (← getFromTable Γ frm₂) frm₂
    let prp ← checkExpression (T₁ ++ T₂) prop
    let wfrm := WellFormedFrom.join wfrm₁ wfrm₂
    if h : prp.fst = .boolean then
      pure ⟨T₁ ++ T₂, wfrm (h ▸ prp.snd)⟩
    else
      .error ("Where clauses can only contain boolean expressions.", stx)
  | .nestedJoin sel frm whr a stx => do
    let fromTable ← getFromTable Γ frm
    let ⟨Tf, wfrm⟩ ← checkFrom Γ fromTable frm
    let ⟨Ts, wsel⟩ ← checkSel Tf fromTable sel
    let wwhr ← checkExpression Tf whr
    if heq : T = (Ts.map fun (n, _, ty) => (n, a, ty)) ∧ wwhr.fst = .boolean then
      return ⟨T, .nestedFrom (wsel) wfrm (heq.right ▸ wwhr.snd) heq.left⟩
    else
      .error (s!"Nested From type {T} must match Select {(Ts.map fun (n, _, ty) => (n, a, ty))} type.", stx)

def checkQuery (Γ : Schema) : (t : Query) → (T : RelationType) → Except (String × Syntax) (Σ' T, (WellFormedQuery Γ t T))
  | ⟨sel, frm, whr, stx⟩, T => do
    let fromTable ← getFromTable Γ frm
    let ⟨Tf, wfrm⟩ ← checkFrom Γ fromTable frm
    let ⟨Ts, wsel⟩ ← checkSel Tf T sel
    let wwhr ← checkExpression Tf whr
    if heq : Ts = T ∧ wwhr.fst = .boolean then
      return ⟨Ts, (.mk (heq.left ▸ wsel) wfrm (heq.right ▸ wwhr.snd))⟩
    else
      .error (s!"Query type {T} must match Select {Ts} type.", stx)

open Lean Elab Meta Term

def exprToDataType : Expr → TermElabM DataType
  | .const ``DataType.null _ => pure .null
  | .const ``DataType.integer _ => pure .integer
  | .const ``DataType.bigInt _ => pure .bigInt
  | .const ``DataType.bit _ => pure .bit
  | .const ``DataType.varbit _ => pure .varbit
  | .const ``DataType.boolean _ => pure .boolean
  | .const ``DataType.char _ => pure .char
  | .const ``DataType.varchar _ => pure .varchar
  | .const ``DataType.date _ => pure .date
  | .const ``DataType.text _ => pure .text
  | .const ``DataType.double _ => pure .double
  | e => throwError "Unsupported DataType: {e}"

declare_syntax_cat                    value
syntax num                          : value
syntax str                          : value
syntax scientific                   : value
syntax "NULL"                       : value
syntax "(" value ")"                : value

declare_syntax_cat                    selectField
syntax ident                        : selectField
syntax ident " AS " ident           : selectField

declare_syntax_cat                    sqlSelect
syntax "*"                          : sqlSelect
syntax "DISTINCT " "*"              : sqlSelect
syntax selectField,+                : sqlSelect
syntax "DISTINCT " selectField,+    : sqlSelect

declare_syntax_cat                    op
syntax " = "                        : op
syntax " <> "                       : op
syntax " != "                       : op
syntax " < "                        : op
syntax " <= "                       : op
syntax " > "                        : op
syntax " >= "                       : op
syntax " + "                        : op
syntax " - "                        : op
syntax " / "                        : op
syntax " * "                        : op
syntax " % "                        : op
syntax " || "                       : op

declare_syntax_cat                    expr
syntax "TRUE"                       : expr
syntax "FALSE"                      : expr
syntax value                        : expr
syntax ident                        : expr
syntax:65 "+" expr:66               : expr
syntax:65 "-" expr:66               : expr
syntax:64 expr:65 op expr:65        : expr
syntax:63 expr " AND " expr         : expr
syntax:63 expr " OR "  expr         : expr
syntax:63 " NOT " expr              : expr
syntax "(" expr ")"                 : expr

declare_syntax_cat                    join
syntax " INNER "                    : join
syntax " LEFT "                     : join
syntax " RIGHT "                    : join
syntax " OUTER "                    : join

declare_syntax_cat                                              sqlQuery
declare_syntax_cat                                              sqlFrom

syntax ident                                                  : sqlFrom
syntax sqlFrom ", " sqlFrom                                   : sqlFrom
syntax sqlFrom " AS " ident                                   : sqlFrom
syntax sqlFrom join " JOIN " sqlFrom " ON " expr              : sqlFrom
syntax sqlFrom join " JOIN " sqlFrom " USING " expr           : sqlFrom
syntax "(" sqlQuery ")" " AS " ident                          : sqlFrom
syntax "(" sqlFrom ")"                                        : sqlFrom

syntax "SELECT " sqlSelect " FROM " sqlFrom (" WHERE " expr)? : sqlQuery

syntax (name := pgquery) "pquery(" ident " |- " sqlQuery " ∶ " term ")" : term

partial def elabValue (stx : TSyntax `value) : TermElabM Expr := do
  let expr := match stx with
    -- defaults to integer (see https://www.postgresql.org/docs/7.3/datatype.html)
  | `(value|$v:num) => return mkApp2 (mkConst ``Value.integer) (mkApp (mkConst ``Int.ofNat) (mkNatLit v.getNat)) (← quoteAutoTactic stx)
  | `(value|$v:scientific) => return mkApp2 (mkConst ``Value.double) (← Term.elabScientificLit v (mkConst `Float)) (← quoteAutoTactic stx)
    -- Defaults to text: (see https://www.postgresql.org/docs/current/datatype-character.html)
  | `(value|$v:str) => return mkApp3 (mkConst ``Value.varchar) (mkNatLit 255) (mkStrLit v.getString) (← quoteAutoTactic stx)
  | `(value|NULL) => return mkApp (Lean.mkConst ``Value.null) (← quoteAutoTactic stx)
  | `(value|($v:value)) => elabValue v
  | _ => throwUnsupportedSyntax
  -- TODO: Include remaining types
  expr

def elabOp : TSyntax `op → TermElabM Expr
  | `(op|=)  => return mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.eq)
  | `(op|<>) => return mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.ne)
  | `(op|!=) => return mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.ne)
  | `(op|<)  => return mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.lt)
  | `(op|<=) => return mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.le)
  | `(op|>)  => return mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.gt)
  | `(op|>=) => return mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.ge)
  | `(op|+) => return mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.add)
  | `(op|-) => return mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.sub)
  | `(op|/) => return mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.div)
  | `(op|*) => return mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.mul)
  | `(op|%) => return mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.mod)
  | `(op|||) => return mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.con)
  | _                => throwUnsupportedSyntax

-- Can be optimized by checking in the branches rather than at the end
partial def elabExpression (stx : TSyntax `expr) : TermElabM Expr := match stx with
  | `(expr|$v:value) => return mkApp2 (mkConst ``Expression.value) (← elabValue v) (← quoteAutoTactic stx)
  | `(expr|$id:ident) =>
    match id.getId with
    | .str fst snd => return mkApp3 (mkConst ``Expression.field) (mkStrLit snd) (mkStrLit fst.toString) (← quoteAutoTactic stx)
    | _ => throwUnsupportedSyntax
  | `(expr|+ $ae:expr) => return mkApp3 (mkConst ``Expression.un) (mkConst ``UnaryOp.add) (← elabExpression ae) (← quoteAutoTactic stx)
  | `(expr|- $ae:expr) => return mkApp3 (mkConst ``Expression.un) (mkConst ``UnaryOp.sub) (← elabExpression ae) (← quoteAutoTactic stx)
  | `(expr|$be₁:expr AND $be₂:expr) => do
    let be₁ ← elabExpression be₁
    let be₂ ← elabExpression be₂
    return mkApp4 (mkConst ``Expression.bin) be₁ (mkApp (mkConst ``Operator.bop) (mkConst ``BoolBinOp.and)) be₂ (← quoteAutoTactic stx)
  | `(expr|$be₁:expr OR $be₂:expr) => do
    let be₁ ← elabExpression be₁
    let be₂ ← elabExpression be₂
    return mkApp4 (mkConst ``Expression.bin) be₁ (mkApp (mkConst ``Operator.bop) (mkConst ``BoolBinOp.or)) be₂ (← quoteAutoTactic stx)
  | `(expr|$ae₁:expr $ps:op $ae₂:expr) => do
    let ae₁ ← elabExpression ae₁
    let ae₂ ← elabExpression ae₂
    let op ← elabOp ps
    let stx ← quoteAutoTactic stx
    return mkApp4 (mkConst ``Expression.bin) ae₁ op ae₂ stx
  | `(expr|($be:expr)) => elabExpression be
  | `(expr|TRUE) => return mkApp2 (mkConst ``Expression.value) (mkApp2 (mkConst ``Value.boolean) (mkConst ``true) (← quoteAutoTactic stx)) (← quoteAutoTactic stx)
  | `(expr|FALSE) => return mkApp2 (mkConst ``Expression.value) (mkApp2 (mkConst ``Value.boolean) (mkConst ``false) (← quoteAutoTactic stx)) (← quoteAutoTactic stx)
  | `(expr|NOT $be:expr) => return mkApp3 (mkConst ``Expression.un) (mkConst ``UnaryOp.not) (← elabExpression be) (← quoteAutoTactic stx)
  | s => throwError s

def elabSelectField (stx : TSyntax `selectField) : TermElabM Expr := match stx with
  | `(selectField|$field:ident) =>
    match field.getId with
    | .str fst snd =>
      return mkApp3 (mkConst ``SelectField.col) (mkStrLit snd) (mkStrLit fst.toString) (← quoteAutoTactic stx)
    | _ => throwUnsupportedSyntax
  | `(selectField|$field:ident AS $as:ident) =>
    match field.getId with
    | .str fst snd =>
      let fieldName := snd
      let tableName := fst.toString
      let «alias» := as.getId.toString
      return mkApp3 (mkConst ``SelectField.alias) (mkStrLit fieldName) (mkStrLit tableName) (mkStrLit «alias»)
    | _ => throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

def elabSelect (stx : TSyntax `sqlSelect) : TermElabM Expr := match stx with
  | `(sqlSelect|*) => return mkApp2 (mkConst ``Select.all) (mkConst ``Bool.false) (← quoteAutoTactic stx)
  | `(sqlSelect|DISTINCT *) => return mkApp2 (mkConst ``Select.all) (mkConst ``Bool.true) (← quoteAutoTactic stx)
  | `(sqlSelect|$cs:selectField,*) => do
    let exprs ← cs.getElems.toList.mapM elabSelectField
    let cols ← mkListLit (mkConst ``SelectField) exprs
    return mkApp3 (mkConst ``Select.list) (mkConst ``Bool.false) cols (← quoteAutoTactic stx)
  | `(sqlSelect|DISTINCT $cs:selectField,*) => do
    let exprs ← cs.getElems.toList.mapM elabSelectField
    let cols ← mkListLit (mkConst ``SelectField) exprs
    return mkApp3 (mkConst ``Select.list) (mkConst ``Bool.true) cols (← quoteAutoTactic stx)
  | _ => throwUnsupportedSyntax

def elabJoin (stx : TSyntax `join) : TermElabM Expr :=
  match stx with
  | `(join|INNER) => return mkApp (mkConst ``Join.inner) (← quoteAutoTactic stx)
  | `(join|LEFT)  => return mkApp (mkConst ``Join.left) (← quoteAutoTactic stx)
  | `(join|RIGHT) => return mkApp (mkConst ``Join.right) (← quoteAutoTactic stx)
  | `(join|OUTER) => return mkApp (mkConst ``Join.outer) (← quoteAutoTactic stx)
  | _             => throwUnsupportedSyntax

partial def elabFrom (stx : TSyntax `sqlFrom) : TermElabM Expr := match stx with
  | `(sqlFrom|$t:ident) => return mkApp2 (mkConst ``From.table) (mkStrLit t.getId.toString) (← quoteAutoTactic stx)
  | `(sqlFrom|$f:sqlFrom AS $t:ident) =>
    return mkApp3  (mkConst ``From.alias) (← elabFrom f) (mkStrLit t.getId.toString) (← quoteAutoTactic stx)
  | `(sqlFrom|$l:sqlFrom, $r:sqlFrom) => do
    let l ← elabFrom l
    let r ← elabFrom r
    return mkApp3 (mkConst ``From.implicitJoin) l r (← quoteAutoTactic stx)
  | `(sqlFrom|$l:sqlFrom $j:join JOIN $r:sqlFrom ON $p:expr) => do
    let l ← elabFrom l
    let r ← elabFrom r
    let j ← elabJoin j
    let p ← elabExpression p
    return mkApp5 (mkConst ``From.join) j l r p (← quoteAutoTactic stx)
  | `(sqlFrom|($f:sqlFrom))           => elabFrom f
  | `(sqlFrom| (SELECT $sel:sqlSelect FROM $frm:sqlFrom $[WHERE $expr]?) AS $id:ident) => do
    let sel ← elabSelect sel
    let frm ← elabFrom frm
    let whr ← match expr with
    | none => pure <| mkApp2 (mkConst ``Expression.value) (mkApp2 (mkConst ``Value.boolean) (mkConst ``true) (← quoteAutoTactic stx)) (← quoteAutoTactic stx)
    | some expr => elabExpression expr
    let al := id.getId.toString
    return mkApp5 (mkConst ``From.nestedJoin) sel frm whr (mkStrLit al) (← quoteAutoTactic stx)
  | _ => throwUnsupportedSyntax

def elabQuery (stx : TSyntax `sqlQuery) : TermElabM Expr := match stx with
  | `(sqlQuery| SELECT $sel FROM $frm:sqlFrom $[WHERE $expr]?) => do
    let frm ← elabFrom frm
    let whr ← match expr with
    | none => pure <| mkApp2  (mkConst ``Expression.value) (mkApp2 (mkConst ``Value.boolean) (mkConst ``true) (← quoteAutoTactic stx)) (← quoteAutoTactic stx)
    | some expr => elabExpression expr
    let sel ← elabSelect sel
    return mkApp4 (mkConst ``Query.mk) sel frm whr (← quoteAutoTactic stx)
  | _ => throwUnsupportedSyntax

structure TypedQuery where
  ctx: Schema
  query: Query
  type: RelationType

def checkQuery! (Γ : Schema) (t : Query) (T : RelationType) : Except (String × Syntax) TypedQuery :=
  match checkQuery Γ t T with
  | .ok rt => .ok ⟨Γ, t, rt.fst⟩
  | .error e => .error e

elab_rules : term
  | `(pgquery| pquery( $id |- $query ∶ $relation )) => do
    let env ← getEnv
    if let .some s := env.find? id.getId then
      let query ← elabQuery query
      let checked ← elabAppArgs (mkConst ``checkQuery!) #[] #[Arg.expr s.value!, Arg.expr query, Arg.stx relation] .none (explicit := false) (ellipsis := false)
      let qAST ← unsafe evalExpr (Except (String × Syntax) TypedQuery) (.app (.app (.const `Except [0, 0]) (.app (.app (.const `Prod [0, 0]) (.const `String [])) (.const `Lean.Syntax []))) (.const ``TypedQuery [])) checked
      let stx ← getRef
      match qAST with
      | .ok _ => pure query
      | .error (e, estx) =>
        match stx.find? (. == estx) with
        | .some estx => throwErrorAt estx e
        | .none => throwError "Error location Syntax {estx} in AST not in currently elaborated Syntax {stx}."
    else
      throwUnsupportedSyntax

def schema : Schema := [("employee", [("id", "employee", DataType.bigInt)]), ("customer", [("id", "customer", .bigInt), ("date", "customer", .date)])]

-- Should select all ✓
#check pquery( schema |- SELECT * FROM employee ∶ [("id", "employee", DataType.bigInt)] )
-- Should fail on typo ✓
#check pquery( schema |- SELECT * FROM employee ∶ [("idd", "employee", DataType.bigInt)] )
-- Should not select too many ✓
#check pquery( schema |- SELECT * FROM employee ∶ [("id", "employee", DataType.bigInt), ("id", "employee", .bigInt)] )
-- Should not select too few ✓
#check pquery( schema |- SELECT * FROM customer ∶ [("id", "customer", DataType.bigInt)] )
-- Should select all joined ✓
#check pquery( schema |- SELECT * FROM employee, customer ∶ [("id", "employee", DataType.bigInt), ("id", "customer", DataType.bigInt), ("date", "customer", DataType.date)] )
-- Should select some ✓
#check pquery( schema |- SELECT customer.date FROM employee, customer ∶ [("date", "customer", DataType.date)] )
-- Should fail on ambiguity × (Non prefixed field inference not yet supported)
#check pquery( schema |- SELECT id FROM employee, customer ∶ [("date", "customer", DataType.date)] )
-- Should select only corresponding id ✓
#check pquery( schema |- SELECT customer.id FROM employee, customer ∶ [("id", "customer", DataType.bigInt)] )
#check pquery( schema |- SELECT employee.id FROM employee, customer ∶ [("id", "employee", DataType.bigInt)] )
-- Should fail on outdated select field ✓
#check pquery( schema |- SELECT employee.id FROM employee AS b, customer ∶ [("id", "b", DataType.bigInt)] )
-- Should succeed with table alias ✓
#check pquery( schema |- SELECT b.id FROM employee AS b, customer ∶ [("id", "b", DataType.bigInt)] )
-- Should succeed with field alias ✓
#check pquery( schema |- SELECT employee.id AS fakeID FROM employee ∶ [("fakeID", "employee", DataType.bigInt)] )
-- Should only allow nesting with alias ×
#check pquery( schema |- SELECT a.id FROM (SELECT * FROM customer) AS a ∶ [("id", "a", DataType.bigInt)] )
#check pquery( schema |- SELECT a.id FROM (SELECT * FROM customer) ∶ [("id", "a", .bigInt)] )
-- Should succeed on correct expr ✓
#check pquery( schema |- SELECT customer.id FROM customer WHERE +(customer.id / 2) = (-1 + 0.0) AND TRUE ∶ [("id", "customer", DataType.bigInt)] )
#check pquery( schema |- SELECT customer.id FROM customer WHERE (customer.date + 8) > customer.date ∶ [("id", "customer", DataType.bigInt)] )
-- Should fail on wrong value
#check pquery( schema |- SELECT * FROM employee WHERE 9999999999 > 0 ∶ [("id", "employee", DataType.bigInt)] )
-- Should fail on wrong expr
#check pquery( schema |- SELECT customer.id FROM customer WHERE 9 AND TRUE ∶ [("id", "customer", DataType.bigInt)] )
#check pquery( schema |- SELECT customer.id FROM customer WHERE TRUE + 8 ∶ [("id", "customer", DataType.bigInt)] )
#check pquery( schema |- SELECT customer.id FROM customer WHERE (8 + customer.date) > customer.date ∶ [("id", "customer", DataType.bigInt)] )
-- Should succeed on double dot alias ✓
#check pquery( schema |- SELECT a.a.a FROM (SELECT customer.id AS a FROM customer) AS a.a ∶ [("a", "a.a", DataType.bigInt)] )
-- Should nest deeply ✓
#check pquery( schema |- SELECT a.id FROM (SELECT b.id FROM (SELECT customer.id FROM customer) AS b) AS a ∶ [("id", "a", DataType.bigInt)] )

def schema2 : Schema :=
  [
    ("Students", [
      ("student_id", "Students", DataType.integer),
      ("student_name", "Students", DataType.varchar),
      ("gender", "Students", DataType.integer),
      ("age", "Students", DataType.integer),
      ("major", "Students", DataType.text)
    ]),
    ("Courses", [
      ("course_id", "Courses", DataType.integer),
      ("course_name", "Courses", DataType.text),
      ("course_credits", "Courses", DataType.integer)
    ]),
    ("Enrollments", [
      ("enrollment_id", "Enrollments", DataType.integer),
      ("student_id", "Enrollments", DataType.text),
      ("semester", "Enrollments", DataType.varchar),
      ("grade", "Enrollments", DataType.char),
      ("student_id", "Enrollments", DataType.integer),
      ("course_id", "Enrollments", DataType.integer),
    ]),
  ]

#check pquery( schema2 |-
SELECT
    Students.student_id,
    Students.student_name,
    Students.gender,
    Students.age,
    Students.major,
    Courses.course_name,
    Courses.course_credits,
    Enrollments.semester,
    Enrollments.grade
FROM
    Students
INNER JOIN
    Enrollments ON Students.student_id = Enrollments.student_id
INNER JOIN
    Courses ON Enrollments.course_id = Courses.course_id
∶ [("student_id", "Students", DataType.integer),
    ("student_name", "Students", DataType.varchar),
    ("gender", "Students", DataType.integer),
    ("age", "Students", DataType.integer),
    ("major", "Students", DataType.text),
    ("course_name", "Courses", DataType.text),
    ("course_credits", "Courses", DataType.integer),
    ("semester", "Enrollments", DataType.varchar),
    ("grade", "Enrollments", DataType.char)
    ]
)
