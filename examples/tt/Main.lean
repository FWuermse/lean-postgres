import Aesop
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
  | bigInt (i : Int)
  | bit (len : Nat) (stream : Array Bool)
  | boolean (b : Bool)
  | char (len : Nat) (string : String)
  | date (year : Nat) (month : Fin 13) (year : Fin 32)
  | double (d : Float)
  | integer (i : Int)
  | null
  | text (value : String)
  | varbit (len : Nat) (stream : Array Bool)
  | varchar (len : Nat) (string : String)

inductive WellFormedValue : Value → DataType → Prop
  | bigInt : i < Int.ofNat 2^64 → i > -Int.ofNat 2^64 → WellFormedValue (.bigInt i) .bigInt
  | bit : b.size = n → WellFormedValue (.bit n b) .bit
  | boolean : WellFormedValue (.boolean b) .boolean
  | char : s.length = n → WellFormedValue (.char n s) .char
  | date : m > 0 ∧ d > 0 → WellFormedValue (.date y m d) .date
  | double : WellFormedValue (.double f) .double
  | integer : i < Int.ofNat 2^32 → i > -Int.ofNat 2^32 → WellFormedValue (.integer i) .integer
  | null : WellFormedValue (.null) .null
  | text : WellFormedValue (.text s) .text
  | varbit : b.size ≤ n → WellFormedValue (.varbit n b) .varbit
  | varchar : s.length ≤ n → WellFormedValue (.varchar n s) .varchar

/-
When two compatible types are used in the same expression the more general will be the output type.
This only works for a subset of types such as number or text types.

Following the conversion of:
  https://www.postgresql.org/docs/current/functions-math.html
  https://www.postgresql.org/docs/current/datatype-character.html
  https://www.postgresql.org/docs/current/functions-datetime.html
-/
def partMoreGeneral : DataType → DataType → DataType
  | .double, .bigInt => .double
  | .double, .integer => .double
  | .bigInt, .integer => .bigInt
  | .text, .varchar => .text
  | .text, .char => .text
  | .varchar, .char => .varchar
  | .date, .integer => .date
  | _, _ => .null

inductive WellFormedNumConv : DataType → DataType → DataType → Prop
  | numeric :
    fst = .integer ∨ fst = .bigInt ∨ fst = .double →
    snd = .integer ∨ snd = .bigInt ∨ snd = .double →
    ----------------------------------
    WellFormedNumConv fst snd (partMoreGeneral fst snd)

inductive WellFormedCharConv : DataType → DataType → DataType → Prop
  | char :
    fst = .char ∨ fst = .varchar ∨ fst = .text →
    snd = .char ∨ snd = .varchar ∨ snd = .text →
    ----------------------------------
    WellFormedCharConv fst snd (partMoreGeneral fst snd)

inductive WellFormedConv : DataType → DataType → Prop
  | numeric :
    WellFormedNumConv T₁ T₂ T₃ →
    WellFormedConv T₁ T₂
  | char :
    WellFormedCharConv T₁ T₂ T₃ →
    WellFormedConv T₁ T₂
  | eq : WellFormedConv T T

inductive Join
  | inner | left | right | outer

def Join.toString : Join → String
  | inner => "INNER"
  | left  => "LEFT"
  | right => "RIGHT"
  | outer => "OUTER"

instance : ToString Join := ⟨Join.toString⟩

/-
# Operators

Following the grammar of https://www.postgresql.org/docs/current/sql-syntax-lexical.html#SQL-SYNTAX-OPERATORS
-/
inductive BoolBinOp
  | and
  | or
  deriving DecidableEq

inductive AExprCmpOp
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
  deriving DecidableEq

inductive AExprOp
  | add
  | sub
  | mul
  | div
  | mod
  | concat
  deriving DecidableEq

inductive UnaryOp
  | add
  | sub
  | not
  deriving DecidableEq

inductive Operator
  | acop (op : AExprCmpOp)
  | aop (op : AExprOp)
  | bop (op : BoolBinOp)
  | uop (op : UnaryOp)
  deriving DecidableEq

def Operator.toString
  | acop .eq => " = "
  | acop .ge => " > "
  | acop .gt => " >= "
  | acop .le => " <= "
  | acop .lt => " < "
  | acop .ne => " <> "
  | aop .add => " + "
  | aop .concat => " || "
  | aop .div => " / "
  | aop .mod => " % "
  | aop .mul => " * "
  | aop .sub => " - "
  | bop .and => " AND "
  | bop .or => " OR "
  | uop .add => "+"
  | uop .not => "NOT "
  | uop .sub => "-"

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
  | value (l : Value)
  | field (name : String) (table : String)
  | bin (lhs : Expression) (op : Operator) (rhs : Expression)
  | un (op : Operator) (expr : Expression)
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
    WellFormedExpression Γ (.value v) T
  | field :
    (name, table, T) ∈ Γ ∨ (name, table, T) ∈ Γ →
    ----------------------------------
    WellFormedExpression Γ (.field name table) T
  | not :
    WellFormedExpression Γ e .boolean →
    ----------------------------------
    WellFormedExpression Γ (.un (.uop .not) e) .boolean
  -- Bool not otherwise comparable (see: https://www.postgresql.org/docs/current/functions-logical.html)
  | bcmp :
    WellFormedExpression Γ lhs .boolean →
    WellFormedExpression Γ rhs .boolean →
    ----------------------------------
    WellFormedExpression Γ (.bin lhs (.bop op) rhs) .boolean
  | acmp :
    WellFormedExpression Γ lhs T₁ →
    WellFormedExpression Γ rhs T₂ →
    -- TODO: check whether undocumented comparison/aexpr fails or results in false (if false remove below)
    WellFormedConv T₁ T₂ →
    ----------------------------------
    WellFormedExpression Γ (.bin lhs (.acop op) rhs) .boolean
  | aexpr :
    WellFormedExpression Γ lhs T₁ →
    WellFormedExpression Γ rhs T₂ →
    WellFormedNumConv T₁ T₂ T →
    ----------------------------------
    WellFormedExpression Γ (.bin lhs (.aop op) rhs) T
 | concat :
    -- Inference is not bidirectional (see: https://www.postgresql.org/docs/current/functions-string.html)
    WellFormedExpression Γ lhs .text →
    WellFormedExpression Γ rhs T₂ →
    -- Also must check for non-array (however array not yet supported)
    ----------------------------------
    WellFormedExpression Γ (.bin lhs (.aop .concat) rhs) .text
  | pos :
    WellFormedExpression Γ e T →
    T = .integer ∨ T = .bigInt ∨ T = .double →
    ----------------------------------
    WellFormedExpression Γ (.un (.uop .add) e) T
  | neg :
    WellFormedExpression Γ e T →
    T = .integer ∨ T = .bigInt ∨ T = .double →
    ----------------------------------
    WellFormedExpression Γ (.un (.uop .sub) e) T
  -- Date ops are not symmetrical (see: https://www.postgresql.org/docs/current/functions-datetime.html)
  | dateadd :
    WellFormedExpression Γ lhs .date →
    WellFormedExpression Γ rhs .integer →
    ----------------------------------
    WellFormedExpression Γ (.bin lhs (.aop .add) rhs) .date
  | datesub :
    WellFormedExpression Γ lhs .date →
    WellFormedExpression Γ rhs .integer →
    ----------------------------------
    WellFormedExpression Γ (.bin lhs (.aop .sub) rhs) .date

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
  | col (name : String) (table : String)
  | alias (name : String) (table : String) («alias» : String)
  deriving BEq, DecidableEq

def SelectField.name
  | col n t => s!"{t}.{n}"
  | «alias» _ n t => s!"{t}.{n}"

def SelectField.postfix
  | col s _ => s
  | «alias» _ s _ => s

inductive WellFormedSelectField : RelationType → SelectField → DataType → Prop
  | col :
    (name, table, T) ∈ Γ →
    ----------------------------------
    WellFormedSelectField Γ (.col name table) T
    -- Postgres doesn't support nested aliases such as 'a AS b, b AS c'
  | alias :
    (name, table, T) ∈ Γ →
    ----------------------------------
    WellFormedSelectField Γ (.alias a name table) T

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
  | list : Bool → List SelectField → Select
  | all  : Bool → Select

/-
TODO: support for functions such as count etc.
-/
@[aesop unsafe 100% apply]
inductive WellFormedSelect : RelationType → Select → RelationType → Prop
  | list (ss : List SelectField) :
    Forall (∃t, WellFormedSelectField Γ . t) ss →
    ----------------------------------
    WellFormedSelect Γ (.list b ss) T
  | all (h: ∀ x ∈ T, x ∈ Γ) :
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
  | table (name : String)
  | alias (frm : From) (als : String)
  | join (jOp : Join) (fst : From) (snd : From) (onCond : Expression)
  | implicitJoin (fst : From) (snd : From)
  --| joinUsing (fst : From) (snd : From) (cols : List Expression)
  | nestedJoin (sel : Select) (frm : From) (whr : Expression)

@[aesop unsafe 100% apply]
inductive WellFormedFrom : Schema → From → RelationType → Prop
  | table :
    (name, T) ∈ Γ →
    ----------------------------------
    WellFormedFrom Γ (.table name) T
  -- From aliases override the from table information: https://www.postgresql.org/docs/7.1/queries.html#QUERIES-WHERE
  | alias :
    WellFormedFrom Γ f T →
    ----------------------------------
    WellFormedFrom Γ (.alias f tableAlias) (T.map fun (name, _, ty) => (name, tableAlias, ty))
  | join :
    WellFormedFrom Γ f₁ T₁ →
    WellFormedFrom Γ f₂ T₂ →
    WellFormedExpression (T₁ ++ T₂) e .boolean →
    ----------------------------------
    WellFormedFrom Γ (.join j f₁ f₂ e) (T₁ ++ T₂)
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
    WellFormedFrom Γ (.implicitJoin f₁ f₂) (T₁ ++ T₂)
  | nestedFrom :
    WellFormedSelect Tf s Ts →
    WellFormedFrom Γ f Tf →
    WellFormedExpression Tf e .boolean →
    ----------------------------------
    WellFormedFrom Γ (.nestedJoin s f e) Ts

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

@[aesop unsafe 100% apply]
inductive WellFormedQuery : Schema → Query → RelationType → Prop
  | mk :
    WellFormedSelect Tf s Ts →
    WellFormedFrom Γ f Tf →
    WellFormedExpression Tf e .boolean →
    ----------------------------------
    WellFormedQuery Γ ⟨s, f, e⟩ Ts

def getFromTable (Γ : Schema) : (t : From) → Except String RelationType
  | .table name =>
    let table := Γ.find? fun (n, _) => n == name
    match table with
      | .some (_, t) => .ok t
      | .none => .error s!"Could not find table {name}"
  | .alias frm _ => getFromTable Γ frm
  | .implicitJoin frm₁ frm₂ => do
    let fst ← getFromTable Γ frm₁
    let snd ← getFromTable Γ frm₂
    return fst ++ snd
  | .join _ frm₁ frm₂ _ => do
    let fst ← getFromTable Γ frm₁
    let snd ← getFromTable Γ frm₂
    return fst ++ snd
  | .nestedJoin s f _ => match s with
    | .all _ => getFromTable Γ f
    | .list _ l =>
      return l.filterMap fun (sf : SelectField) =>
        match getFromTable Γ f with
          | .ok rt => match rt.find? (fun (n, _) => n == sf.name) with
            | .some v => .some v
            | .none => none
          | .error _ => .none

@[simp]
def checkSelectField (Γ : RelationType) (s : SelectField) (T : DataType) : Except String (Σ' T, WellFormedSelectField Γ s T) := match s with
  | .col name table => do
    if h : (name, table, T) ∈ Γ then
      pure ⟨T, WellFormedSelectField.col h⟩
    else
      .error s!"Selected field {table}.{name} is not in the current context."
  | .alias a name table =>
    if h : (name, table, T) ∈ Γ then
      pure ⟨T, WellFormedSelectField.alias h⟩
    else
      .error s!"Selected field {table}.{name} as {a} is not in the current context."

-- (Maybe remove dicidable)
instance (Γ : RelationType) (T : DataType) : DecidablePred (fun s : SelectField => (checkSelectField Γ s T).isOk) :=
  fun s =>
    match s with
    | .col name table =>
      if h : (name, table, T) ∈ Γ then
        isTrue (by simp [h]; rfl)
      else
        isFalse (by simp [h]; rfl)
    | .alias a name table =>
      if h : (name, table, T) ∈ Γ then
        isTrue (by simp [h]; rfl)
      else
        isFalse (by simp [h]; rfl)

instance (Γ : RelationType) (s : SelectField) : Decidable (∃T, WellFormedSelectField Γ s T) := match s with
  | .col name table =>
      match hfind : Γ.find? fun (n, t, _) => (n, t) = (name, table) with
        | .some (n, t, T) =>
          isTrue (by
            apply Exists.intro
            have hmem : (name, table, T) ∈ Γ :=
              (by
                simp at hfind
                have h_eq : n = name ∧ t = table := (by
                  have h := List.find?_some hfind
                  have ht_eq : (n, t) = (name, table) :=
                    by simp [eq_true_of_decide h]
                  cases ht_eq
                  apply And.intro
                  . rfl
                  . rfl)
                apply List.mem_of_find?_eq_some
                . exact h_eq.left ▸ h_eq.right ▸ hfind)
            apply WellFormedSelectField.col hmem)
        | .none => isFalse (by
          simp [not_exists]
          intro dt
          simp [*] at *
          have h_neq : (name, table, dt) ∉ Γ  := (by
            simp [List.find?_eq_none] at hfind
            intro hmem
            have hfalse := hfind (name, table, dt) hmem
            rw [Not] at hfalse
            apply hfalse
            . rfl
            . rfl)
          rw [Not] at *
          intro wfsf
          cases wfsf
          apply h_neq
          assumption)
  | .alias a name table =>
      match hfind : Γ.find? fun (n, t, _) => (n, t) = (name, table) with
        | .some (n, t, T) =>
          isTrue (by
            apply Exists.intro
            have hmem : (name, table, T) ∈ Γ :=
              (by
                simp at hfind
                have h_eq : n = name ∧ t = table := (by
                  have h := List.find?_some hfind
                  have ht_eq : (n, t) = (name, table) :=
                    by simp [eq_true_of_decide h]
                  cases ht_eq
                  apply And.intro
                  . rfl
                  . rfl)
                apply List.mem_of_find?_eq_some
                . exact h_eq.left ▸ h_eq.right ▸ hfind)
            apply WellFormedSelectField.alias hmem)
        | .none => isFalse (by
          simp [not_exists]
          intro dt
          simp [*] at *
          have h_neq : (name, table, dt) ∉ Γ  := (by
            simp [List.find?_eq_none] at hfind
            intro hmem
            have hfalse := hfind (name, table, dt) hmem
            rw [Not] at hfalse
            apply hfalse
            . rfl
            . rfl)
          rw [Not] at *
          intro wfsf
          cases wfsf
          apply h_neq
          assumption)

def checkSel (Γ T : RelationType) (s : Select) : Except String (Σ' T, WellFormedSelect Γ s T) := match s with
  | .all _ =>
    if h : ∀ x ∈ T, x ∈ Γ then
      let wsel := WellFormedSelect.all h
      pure ⟨T, wsel⟩
    else
      .error "The type of `SELECT *` must match the FROM clause."
  | .list _ ss => do
    if h: Forall (fun s : SelectField => ∃ T, WellFormedSelectField Γ s T) ss then
      pure ⟨Γ, WellFormedSelect.list ss h⟩
    else
      .error "All fields to be selected must occur in the selected tables."

def checkValue (v : Value) : Except String (Σ' T, WellFormedValue v T) := match v with
  | .null => pure ⟨.null, .null⟩
  | .integer i => do
    if h₁ : i < 2^32 then
      if h₂ : i > -2^32 then
        pure ⟨.integer, .integer h₁ h₂⟩
      else
        .error s!"Integer value of {i} causes an overflow."
    else
      .error s!"Integer value of {i} causes an overflow."
  | .bigInt i => do
    if h₁ : i < 2^64 then
      if h₂ : i > -2^64 then
        pure ⟨.bigInt, .bigInt h₁ h₂⟩
      else
        .error s!"Integer value of {i} causes an overflow."
    else
      .error s!"Integer value of {i} causes an overflow."
  | .bit n ba => if h : ba.size = n then
      pure ⟨.bit, .bit h⟩
    else
      .error s!"ByteStream {ba} must have exactly length {n}"
  | .varbit n ba => if h : ba.size ≤ n then
      pure ⟨.varbit, .varbit h⟩
    else
      .error s!"ByteStream {ba} must not exceed length {n}"
  | .boolean _ => pure ⟨.boolean, .boolean⟩
  | .char n s => if h : s.length = n then
      pure ⟨.char, .char h⟩
    else
      .error s!"String {s} must have exactly length {n}"
  | .varchar n s => if h : s.length ≤ n then
      pure ⟨.varchar, .varchar h⟩
    else
      .error s!"String {s} must not exceed length {n}"
  | .date y m d => if h : m > 0 ∧ d > 0 then
      pure ⟨.date, .date h⟩
    else
      .error s!"Invalid date: {y}-{m}-{d}"
  | .text _ => pure ⟨.text, .text⟩
  | .double _ => pure ⟨.double, .double⟩

def checkNumConv (fst : DataType) (snd : DataType) : Except String (Σ' T, WellFormedNumConv fst snd T) :=
  if hfst : fst = DataType.integer ∨ fst = .bigInt ∨ fst = .double then
    if hsnd : snd = .integer ∨ snd = .bigInt ∨ snd = .double then
      let max := partMoreGeneral fst snd
      pure ⟨max, WellFormedNumConv.numeric hfst hsnd⟩
    else
      .error s!"Types are not comparable"
  else
    .error s!"Types are not comparable"

def checkCharConv (fst : DataType) (snd : DataType) : Except String (Σ' T, WellFormedCharConv fst snd T) :=
  if hfst : fst = DataType.char ∨ fst = .varchar ∨ fst = .text then
    if hsnd : snd = .char ∨ snd = .varchar ∨ snd = .text then
      let max := partMoreGeneral fst snd
      pure ⟨max, WellFormedCharConv.char hfst hsnd⟩
    else
      .error s!"Types are not comparable"
  else
    .error s!"Types are not comparable"

def checkConv (fst : DataType) (snd : DataType) : Except String (PLift <| WellFormedConv fst snd) := do
  let ⟨_, h⟩ ← checkNumConv fst snd
  return PLift.up <| WellFormedConv.numeric h

def checkExpression (Γ : RelationType) (e : Expression) : Except String (Σ' T, WellFormedExpression Γ e T) := match e with
  | .value v => do
    let ⟨T, hv⟩ ← checkValue v
    pure ⟨T, .value v hv⟩
  | .field name table =>
    let field := (Γ.find? fun (n, _) => n == name).orElse fun _ => (Γ.find? fun (n, _) => n == name)
    if let .some (_, _, t) := field then
      if h : (name, table, t) ∈ Γ ∨ (name, table, t) ∈ Γ then
        let waexpr := WellFormedExpression.field
        pure ⟨t, waexpr h⟩
      else
        .error s!"The field {name} is not present in this context."
    else
      .error s!"The field {name} is not present in this context."
  | .un (.uop .not) bexpr => do
    let ⟨T, wbe⟩ ← checkExpression Γ bexpr
    if h : T = .boolean then
      pure ⟨.boolean, .not <| h ▸ wbe⟩
    else
      .error "Only boolean expressions can be negated."
  | .un (.uop op) aexpr => do
    let ⟨T, wae⟩ ← checkExpression Γ aexpr
    if h : T = .integer ∨ T = .bigInt ∨ T = .double then
      match op with
        | .add => pure ⟨T, .pos wae h⟩
        | .sub => pure ⟨T, .neg wae h⟩
        | _ => .error "Only numeric values can have a sign."
    else
      .error "Only numeric values can have a sign."
  | .bin bexpr₁ (.bop op) bexpr₂ => do
    let ⟨T₁, fst⟩ ← checkExpression Γ bexpr₁
    let ⟨T₂, snd⟩ ← checkExpression Γ bexpr₂
    if h₁ : T₁ = .boolean then
      if h₂ : T₂ = .boolean then
          pure ⟨.boolean, .bcmp (h₁ ▸ fst) (h₂ ▸ snd)⟩
      else
        .error s!"Operator {(Operator.bop op)} only supports boolean expressions on rhs."
    else
      .error s!"Operator {(Operator.bop op)} only supports boolean expressions on lhs."
  | .bin aexpr₁ (.acop _) aexpr₂ => do
    let ⟨a₁, fst⟩ ← checkExpression Γ aexpr₁
    let ⟨a₂, snd⟩ ← checkExpression Γ aexpr₂
    let wf ← checkConv a₁ a₂
    return ⟨.boolean, .acmp fst snd wf.down⟩
  | .bin aexpr₁ (.aop op) aexpr₂ => do
    let ⟨a₁, fst⟩ ← checkExpression Γ aexpr₁
    let ⟨a₂, snd⟩ ← checkExpression Γ aexpr₂
    if h : a₁ = .date ∧ a₂ = .integer then
      match op with
        | .add => return ⟨.date, .dateadd (h.left ▸ fst) (h.right ▸ snd)⟩
        | .sub => return ⟨.date, .datesub (h.left ▸ fst) (h.right ▸ snd)⟩
        | _ => .error s!"Invalid operationr {(Operator.aop op)} on type Date."
    else
      let wf ← checkNumConv a₁ a₂
      return ⟨wf.fst, .aexpr fst snd wf.snd⟩
  | _ => .error "Invalid expression."

def checkFrom (Γ : Schema) (T : RelationType) (t : From) : Except String (Σ' T, WellFormedFrom Γ t T) := match t with
  | .table name =>
      if mem : (name, T) ∈ Γ then
        let wfrm := .table mem
        pure ⟨T, wfrm⟩
      else
        .error s!"Table {name} not in Schema."
  | .alias frm a => do
      let ⟨T, wfrm⟩ ← checkFrom Γ T frm
      pure ⟨T.map fun (n, _, ty) => (n, a, ty), .alias wfrm⟩
  | .implicitJoin frm₁ frm₂ => do
    let ⟨T₁, wfrm₁⟩ ← checkFrom Γ T frm₁
    let ⟨T₂, wfrm₂⟩ ← checkFrom Γ T frm₂
    pure ⟨T₁++T₂, .implicitJoin wfrm₁ wfrm₂⟩
  | .join _ frm₁ frm₂ prop => do
    let ⟨T₁, wfrm₁⟩ ← checkFrom Γ T frm₁
    let ⟨T₂, wfrm₂⟩ ← checkFrom Γ T frm₂
    let prp ← checkExpression (T₁ ++ T₂) prop
    let wfrm := WellFormedFrom.join wfrm₁ wfrm₂
    if h : prp.fst = .boolean then
      pure ⟨T₁ ++ T₂, wfrm (h ▸ prp.snd)⟩
    else
      .error "Where clauses can only contain boolean expressions."
  | .nestedJoin sel frm whr => do
    let fromTable ← getFromTable Γ frm
    let ⟨Tf, wfrm⟩ ← checkFrom Γ fromTable frm
    let ⟨Ts, wsel⟩ ← checkSel Tf T sel
    let wwhr ← checkExpression Tf whr
    if heq : Ts = T ∧ wwhr.fst = .boolean then
      return ⟨T, .nestedFrom (heq.left ▸ wsel) wfrm (heq.right ▸ wwhr.snd)⟩
    else
      .error "Query type must match Select type."

def checkQuery (Γ : Schema) : (t : Query) → (T : RelationType) → Except String (PLift (WellFormedQuery Γ t T))
  | ⟨sel, frm, whr⟩, T => do
    let fromTable ← getFromTable Γ frm
    let ⟨Tf, wfrm⟩ ← checkFrom Γ fromTable frm
    let ⟨Ts, wsel⟩ ← checkSel Tf T sel
    let wwhr ← checkExpression Tf whr
    if heq : Ts = T ∧ wwhr.fst = .boolean then
      return PLift.up (.mk (heq.left ▸ wsel) wfrm (heq.right ▸ wwhr.snd))
    else
      .error "Query type must match Select type."

open Lean Elab Meta Term

declare_syntax_cat                 value
syntax num                       : value
syntax "-" noWs num              : value
syntax str                       : value
syntax scientific                : value
syntax "-" noWs scientific       : value
syntax "NULL"                    : value
syntax "(" value ")"             : value

declare_syntax_cat                 aexpr
syntax value                     : aexpr
syntax ident                     : aexpr
syntax "(" aexpr ")"             : aexpr

declare_syntax_cat                 selectField
syntax ident                     : selectField
syntax ident " AS " ident        : selectField

declare_syntax_cat                 sqlSelect
syntax "*"                       : sqlSelect
syntax "DISTINCT " "*"           : sqlSelect
syntax selectField,+             : sqlSelect
syntax "DISTINCT " selectField,+ : sqlSelect

declare_syntax_cat                 propSymbol
syntax " = "                     : propSymbol
syntax " <> "                    : propSymbol
syntax " != "                    : propSymbol
syntax " < "                     : propSymbol
syntax " <= "                    : propSymbol
syntax " > "                     : propSymbol
syntax " >= "                    : propSymbol
syntax " + "                    : propSymbol
syntax " - "                    : propSymbol
syntax " / "                    : propSymbol
syntax " * "                    : propSymbol
syntax " % "                    : propSymbol
syntax " || "                    : propSymbol

declare_syntax_cat                 prop
syntax "TRUE"                    : prop
syntax "FALSE"                   : prop
syntax aexpr propSymbol aexpr    : prop
syntax prop " AND " prop         : prop
syntax prop " OR "  prop         : prop
syntax " NOT " prop              : prop
syntax "(" prop ")"              : prop

declare_syntax_cat                 join
syntax " INNER "                 : join
syntax " LEFT "                  : join
syntax " RIGHT "                 : join
syntax " OUTER "                 : join

declare_syntax_cat                                      sqlFrom
declare_syntax_cat                                      sqlQuery

syntax ident                                          : sqlFrom
syntax sqlFrom ", " sqlFrom                           : sqlFrom
syntax sqlFrom " AS " ident                           : sqlFrom
syntax sqlFrom join " JOIN " sqlFrom " ON " prop      : sqlFrom
syntax sqlFrom join " JOIN " sqlFrom " USING " aexpr  : sqlFrom
syntax "(" sqlFrom ")"                                : sqlFrom
syntax "(" sqlQuery ")"                               : sqlFrom

syntax "SELECT " sqlSelect " FROM " sqlFrom (" WHERE " prop)? : sqlQuery

syntax (name := pgquery) ident " |- " sqlQuery " ∶ " term : term

def mkApp' (name : Name) (e : Expr) : Expr :=
  mkApp (mkConst name) e

def negFloat (f : Float) : Float :=
  -1.0 * f

-- Default typing values for such cases e.G. is 3<3 bigInt or int?
partial def elabValue : TSyntax `value → TermElabM Expr
  | `(value|$v:num)         => do
    -- defaults to integer (see https://www.postgresql.org/docs/7.3/datatype.html)
    mkAppM ``Value.integer #[mkConst ``Bool.true, ← mkAppM ``Fin.ofNat #[mkNatLit 4, mkNatLit v.getNat]]
  | `(value|-$v:num)        => do
    mkAppM ``Value.integer #[mkConst ``Bool.false, ← mkAppM ``Fin.ofNat #[mkNatLit 4, mkNatLit v.getNat]]
  | `(value|$v:scientific)  => do
    mkAppM ``Value.real #[← Term.elabScientificLit v (mkConst `Float)]
  | `(value|-$v:scientific) => do
    let f ← Term.elabScientificLit v (mkConst `Float)
    mkAppM ``Value.real #[mkApp' ``negFloat f]
  | `(value|$v:str)         =>
    -- Defaults to text: (see https://www.postgresql.org/docs/current/datatype-character.html)
    mkAppM ``Value.varchar #[mkNatLit 255, mkStrLit v.getString]
  | `(value|NULL)              => pure <| mkConst ``Value.null
  | `(value|($v:value))        => elabValue v
  | _                          => throwUnsupportedSyntax

-- Pass Option expected value. If not given infer otherwise just check with the .some
partial def elabAExpr : TSyntax `aexpr → TermElabM Expr
  | `(aexpr|$v:value) => do
    mkAppM ``AExpr.value #[← elabValue v]
  | `(aexpr|$id:ident) => do
    mkAppM ``AExpr.field #[mkStrLit id.getId.toString]
  | `(aexpr|($aexpr:aexpr)) => elabAExpr aexpr
  | _ => throwUnsupportedSyntax

def elabPropSymbol (stx : TSyntax `propSymbol) : TermElabM Name :=
  match stx with
  | `(propSymbol|=)  => pure ``Aop.eq
  | `(propSymbol|<>) => pure ``Aop.ne
  | `(propSymbol|!=) => pure ``Aop.ne
  | `(propSymbol|<)  => pure ``Aop.lt
  | `(propSymbol|<=) => pure ``Aop.le
  | `(propSymbol|>)  => pure ``Aop.gt
  | `(propSymbol|>=) => pure ``Aop.ge
  | _                => throwUnsupportedSyntax

partial def elabBExpr : TSyntax `prop → TermElabM Expr
  | `(prop|TRUE) => mkConst ``BExpr.tt
  | `(prop|FALSE) => mkConst ``BExpr.ff
  | `(prop|$ae₁:aexpr $ps:propSymbol $ae₂:aexpr) => do mkAppM ``BExpr.acmp #[← elabAExpr ae₁, ← mkConst <| ← elabPropSymbol ps, ← elabAExpr ae₂]
  | `(prop|$be₁:prop AND $be₂:prop) => do mkAppM ``BExpr.bcmp #[← elabBExpr be₁, mkConst ``Bop.and, ← elabBExpr be₂]
  | `(prop|$be₁:prop OR $be₂:prop) => do mkAppM ``BExpr.bcmp #[← elabBExpr be₁, mkConst ``Bop.or, ← elabBExpr be₂]
  | `(prop|NOT $be:prop) => do mkAppM ``BExpr.not #[← elabBExpr be]
  | `(prop|($be:prop)) => elabBExpr be
  | _ => throwUnsupportedSyntax

def elabSelectField : TSyntax `selectField → TermElabM Expr
  | `(selectField|$id:ident) => do
    mkAppM ``SelectField.col #[mkStrLit id.getId.toString]
  | `(selectField|$id:ident AS $as:ident) => do
    mkAppM ``SelectField.alias #[mkStrLit as.getId.toString, mkStrLit id.getId.toString]
  | _ => throwUnsupportedSyntax

def elabSelect : TSyntax `sqlSelect → TermElabM Expr
  | `(sqlSelect|*)                          => do
    mkAppM ``Select.all #[← mkConst ``Bool.false]
  | `(sqlSelect|DISTINCT *)                 => do
    mkAppM ``Select.all #[← mkConst ``Bool.true]
  | `(sqlSelect|$cs:selectField,*)          => do
    let cols ← mkListLit (mkConst `SQLSelectField) (← cs.getElems.toList.mapM elabSelectField)
    mkAppM ``Select.list #[← mkConst ``Bool.false, cols]
  | `(sqlSelect|DISTINCT $cs:selectField,*) => do
    let cols ← mkListLit (mkConst `SQLSelectField) (← cs.getElems.toList.mapM elabSelectField)
    mkAppM ``Select.list #[← mkConst ``Bool.true, cols]
  | _ => throwUnsupportedSyntax

def elabConst (name : Name) : TermElabM Expr :=
  pure $ mkConst name

def elabJoin : TSyntax `join → TermElabM Expr
  | `(join|INNER) => elabConst `SQLJoin.inner
  | `(join|LEFT)  => elabConst `SQLJoin.left
  | `(join|RIGHT) => elabConst `SQLJoin.right
  | `(join|OUTER) => elabConst `SQLJoin.outer
  | _             => throwUnsupportedSyntax

mutual
partial def elabFrom : TSyntax `sqlFrom → TermElabM Expr
  | `(sqlFrom|$t:ident)               => do
    mkAppM ``From.table #[mkStrLit t.getId.toString]
  | `(sqlFrom|$f:sqlFrom AS $t:ident) => do
    mkAppM ``From.alias #[← elabFrom f, mkStrLit t.getId.toString]
  | `(sqlFrom|$l:sqlFrom, $r:sqlFrom) => do
    mkAppM ``From.implicitJoin #[← elabFrom l, ← elabFrom r]
  | `(sqlFrom|$l:sqlFrom $j:join JOIN $r:sqlFrom ON $p:prop) => do
    mkAppM ``From.join #[← elabJoin j, ← elabFrom l, ← elabFrom r, ← elabBExpr p]
  | `(sqlFrom|$l:sqlFrom $j:join JOIN $r:sqlFrom USING $ae:aexpr) => do
    let eqStx ← `(prop|ae = ae)
    mkAppM ``From.join #[← elabJoin j, ← elabFrom l, ← elabFrom r, ← elabBExpr eqStx]
  | `(sqlFrom|($f:sqlFrom))           => do
    elabFrom f
  | `(sqlFrom| ($query:sqlQuery)) => do
    mkAppM ``From.nestedJoin #[← elabQuery query]
  | _                                 => throwUnsupportedSyntax

partial def elabQuery : TSyntax `sqlQuery → TermElabM Expr
  | `(sqlQuery| SELECT $sel FROM $frm:sqlFrom $[WHERE $prp]?) => do
    let whr ← match prp with
    | none     => mkConst ``BExpr.tt
    | some prp => elabBExpr prp
    mkAppM ``Query.mk #[← elabSelect sel, ← elabFrom frm, whr]
  | _ => throwUnsupportedSyntax
end

elab_rules : term
  | `(pgquery| $id |- $query ∶ $relation) => do
    let env ← getEnv
    if let .some s := env.find? id.getId then
      let query ← elabQuery query
      elabAppArgs (mkConst ``checkQuery) #[] #[Arg.expr s.value!, Arg.expr query, Arg.stx relation] .none (explicit := false) (ellipsis := false)
    else
      throwUnsupportedSyntax

def schema : Schema :=
  [("employee", [("id", .bigInt)]), ("customer", [("id", .bigInt), ("date", .date)])]

def x := schema |- SELECT * FROM employee ∶ [("id", .bigInt)]
#eval match x with
  | Except.ok _ => "Success"
  | .error e => e
