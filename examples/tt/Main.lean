import Lean
#eval Lean.versionString
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
  deriving Repr

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
  | inner | left | right | outer
  deriving Repr

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
  | value (l : Value)
  | field (name : String) (table : String)
  | bin (lhs : Expression) (op : Operator) (rhs : Expression)
  | un (op : UnaryOp) (expr : Expression)
  -- | function (name : String) (params : List Expression)
  deriving Repr

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
    (name, table, T) ∈ Γ →
    ----------------------------------
    WellFormedExpression Γ (.field name table) T
  | fieldPostfix (t : String) :
    Γ.count (name, t, T) = 1 →
    ----------------------------------
    WellFormedExpression Γ (.field name t) T
  | not :
    WellFormedExpression Γ e .boolean →
    ----------------------------------
    WellFormedExpression Γ (.un .not e) .boolean
  -- Bool not otherwise comparable (see: https://www.postgresql.org/docs/current/functions-logical.html)
  | bcmp :
    WellFormedExpression Γ lhs .boolean →
    WellFormedExpression Γ rhs .boolean →
    ----------------------------------
    WellFormedExpression Γ (.bin lhs (.bop op) rhs) .boolean
  | acmp :
    WellFormedExpression Γ lhs T₁ →
    WellFormedExpression Γ rhs T₂ →
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
    WellFormedExpression Γ (.bin lhs (.aop .con) rhs) .text
  | pos :
    WellFormedExpression Γ e T →
    T = .integer ∨ T = .bigInt ∨ T = .double →
    ----------------------------------
    WellFormedExpression Γ (.un .add e) T
  | neg :
    WellFormedExpression Γ e T →
    T = .integer ∨ T = .bigInt ∨ T = .double →
    ----------------------------------
    WellFormedExpression Γ (.un .sub e) T
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
  deriving BEq, DecidableEq, Repr

def SelectField.toString
  | col n t => s!"{n}.{t}"
  | alias n t a => s!"{n}.{t} AS {a}"

def SelectField.name
  | col n t => s!"{t}.{n}"
  | «alias» n t a => s!"{t}.{n}"

instance : ToString SelectField :=
  ⟨SelectField.toString⟩

def SelectField.postfix
  | col s _ => s
  | «alias» s _ _ => s

def SelectField.getTuple (T : RelationType) : SelectField → Option (String × String × DataType)
  | col n t => T.find? fun (name, table, _) => n == name && t == table
  | «alias» n t a => match T.find? fun (name, table, _) => n == name && t == table with
    | .some (_, table, type) => (a, table, type)
    | .none => .none

inductive WellFormedSelectField : RelationType → SelectField → DataType → Prop
  | col :
    (name, table, T) ∈ Γ →
    ----------------------------------
    WellFormedSelectField Γ (.col name table) T
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
  | list : Bool → List SelectField → Select
  | all  : Bool → Select
  deriving Repr

/-
TODO: support for functions such as count etc.
-/
inductive WellFormedSelect : RelationType → Select → RelationType → Prop
  | list (ss : List SelectField) :
    Forall (∃t, WellFormedSelectField Γ . t) ss →
    (T = ss.filterMap fun s => s.getTuple Γ) →
    ----------------------------------
    WellFormedSelect Γ (.list b ss) T
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
  | table (name : String)
  | alias (frm : From) (als : String)
  | join (jOp : Join) (fst : From) (snd : From) (onCond : Expression)
  | implicitJoin (fst : From) (snd : From)
  --| joinUsing (fst : From) (snd : From) (cols : List Expression)
  -- Nested join must have alias (see: https://www.postgresql.org/docs/current/queries-table-expressions.html#QUERIES-SUBQUERIES)
  | nestedJoin (sel : Select) (frm : From) (whr : Expression) (als : String)
  deriving Repr

inductive WellFormedFrom : Schema → From → RelationType → Prop
  | table :
    (name, T) ∈ Γ →
    ----------------------------------
    WellFormedFrom Γ (.table name) T
  -- From aliases override the from table information: https://www.postgresql.org/docs/7.1/queries.html#QUERIES-WHERE
  | alias :
    WellFormedFrom Γ f T →
    u = (T.map fun (name, _, ty) => (name, tableAlias, ty)) →
    ----------------------------------
    WellFormedFrom Γ (.alias f tableAlias) u
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
    -- Nested join must have alias (see: https://www.postgresql.org/docs/current/queries-table-expressions.html#QUERIES-SUBQUERIES)
    u = (Ts.map fun (name, _, ty) => (name, tableAlias, ty)) →
    ----------------------------------
    WellFormedFrom Γ (.nestedJoin s f e tableAlias) u

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
  deriving Repr

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
  | .alias frm _ => do
    let rt ← getFromTable Γ frm
    return rt
  | .implicitJoin frm₁ frm₂ => do
    let fst ← getFromTable Γ frm₁
    let snd ← getFromTable Γ frm₂
    return fst ++ snd
  | .join _ frm₁ frm₂ _ => do
    let fst ← getFromTable Γ frm₁
    let snd ← getFromTable Γ frm₂
    return fst ++ snd
  | .nestedJoin s f _ a => match s with
    | .all _ => getFromTable Γ f
    | .list _ l =>
      let res := l.filterMap fun (sf : SelectField) =>
        match getFromTable Γ f with
          | .ok rt => match sf with
            | .col n t => match rt.find? fun (n', t', _) => n == n' && t == t' with
              | .some v => .some v
              | .none => none
            | .alias n t a => match rt.find? fun (n', t', _) => n == n' && t == t' with
              | .some v => .some {v with fst := a}
              | .none => none
          | .error _ => .none
      return res

@[simp]
def checkSelectField (Γ : RelationType) (s : SelectField) (T : DataType) : Except String (Σ' T, WellFormedSelectField Γ s T) := match s with
  | .col name table => do
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
    | .col name table =>
      if h : (name, table, T) ∈ Γ then
        isTrue (by simp [h]; rfl)
      else
        isFalse (by simp [h]; rfl)
    | .alias name table a =>
      if h : (name, table, T) ∈ Γ then
        isTrue (by simp [h]; rfl)
      else
        isFalse (by simp [h]; rfl)

instance (Γ : RelationType) (s : SelectField) : Decidable (∃T, WellFormedSelectField Γ s T) := match s with
  | .col name table =>
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

def checkSel (Γ T : RelationType) (s : Select) : Except String (Σ' T, WellFormedSelect Γ s T) := match s with
  | .all _ =>
    if h : Γ = T then
      let wsel := WellFormedSelect.all h
      pure ⟨T, wsel⟩
    else
      .error s!"The type of `SELECT *` must match the FROM clause {Γ}."
  | .list _ ss => do
    let T := ss.filterMap fun s => SelectField.getTuple Γ s
    if h : Forall (fun s : SelectField => ∃ t, WellFormedSelectField Γ s t) ss then
      if h' : T = ss.filterMap (fun s => SelectField.getTuple Γ s) then
        pure ⟨T, WellFormedSelect.list ss h h'⟩
      else
        .error s!"Selection Type {T} must have length of selectFields: {ss.length}."
    else
      .error s!"All selected fields {ss} must be well formed in the context {Γ}."

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

def checkExpression (Γ : RelationType) (e : Expression) : Except String (Σ' T, WellFormedExpression Γ e T) := match e with
  | .value v => do
    let ⟨T, hv⟩ ← checkValue v
    pure ⟨T, .value v hv⟩
  | .field name table =>
    let field := (Γ.find? fun (n, _) => n == name).orElse fun _ => (Γ.find? fun (n, _) => n == name)
    if let .some (_, _, t) := field then
      if h : (name, table, t) ∈ Γ then
        let waexpr := WellFormedExpression.field
        pure ⟨t, waexpr h⟩
      else
        .error s!"The field {name} is not present in this context {Γ}."
    else
      .error s!"The field {name} is not present in this context {Γ}."
  | .un .not bexpr => do
    let ⟨T, wbe⟩ ← checkExpression Γ bexpr
    if h : T = .boolean then
      pure ⟨.boolean, .not <| h ▸ wbe⟩
    else
      .error "Only boolean expressions can be negated."
  | .un op aexpr => do
    let ⟨T, wae⟩ ← checkExpression Γ aexpr
    if h : T = .integer ∨ T = .bigInt ∨ T = .double then
      match op with
        | .add => pure ⟨T, .pos wae h⟩
        | .sub => pure ⟨T, .neg wae h⟩
        | _ => .error s!"Only numeric expressions can have a sign. {T} is not numeric."
    else
      .error s!"Only numeric expressions can have a sign. {T} is not numeric."
  | .bin bexpr₁ (.bop op) bexpr₂ => do
    let ⟨T₁, fst⟩ ← checkExpression Γ bexpr₁
    let ⟨T₂, snd⟩ ← checkExpression Γ bexpr₂
    if h₁ : T₁ = .boolean then
      if h₂ : T₂ = .boolean then
          pure ⟨.boolean, .bcmp (h₁ ▸ fst) (h₂ ▸ snd)⟩
      else
        .error s!"Operator{(Operator.bop op)}only supports boolean expressions on rhs: {T₂}."
    else
      .error s!"Operator{(Operator.bop op)}only supports boolean expressions on lhs: {T₁}."
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

def checkFrom (Γ : Schema) (T : RelationType) (t : From) : Except String (Σ' T, WellFormedFrom Γ t T) := match t with
  | .table name =>
    if mem : (name, T) ∈ Γ then
      let wfrm := .table mem
      pure ⟨T, wfrm⟩
    else
      .error s!"Table {name} : {T} not in Schema {Γ}."
  | .alias frm a => do
    let ⟨T, wfrm⟩ ← checkFrom Γ T frm
    pure ⟨T.map fun (n, _, ty) => (n, a, ty), .alias wfrm rfl⟩
  | .implicitJoin frm₁ frm₂ => do
    let ⟨T₁, wfrm₁⟩ ← checkFrom Γ (← getFromTable Γ frm₁) frm₁
    let ⟨T₂, wfrm₂⟩ ← checkFrom Γ (← getFromTable Γ frm₂) frm₂
    pure ⟨T₁++T₂, .implicitJoin wfrm₁ wfrm₂⟩
  | .join _ frm₁ frm₂ prop => do
    let ⟨T₁, wfrm₁⟩ ← checkFrom Γ (← getFromTable Γ frm₁) frm₁
    let ⟨T₂, wfrm₂⟩ ← checkFrom Γ (← getFromTable Γ frm₂) frm₂
    let prp ← checkExpression (T₁ ++ T₂) prop
    let wfrm := WellFormedFrom.join wfrm₁ wfrm₂
    if h : prp.fst = .boolean then
      pure ⟨T₁ ++ T₂, wfrm (h ▸ prp.snd)⟩
    else
      .error "Where clauses can only contain boolean expressions."
  | .nestedJoin sel frm whr a => do
    let fromTable ← getFromTable Γ frm
    let ⟨Tf, wfrm⟩ ← checkFrom Γ fromTable frm
    let ⟨Ts, wsel⟩ ← checkSel Tf T sel
    let wwhr ← checkExpression Tf whr
    if heq : Ts = T ∧ wwhr.fst = .boolean then
      return ⟨T.map fun (n, _, ty) => (n, a, ty), .nestedFrom (heq.left ▸ wsel) wfrm (heq.right ▸ wwhr.snd) rfl⟩
    else
      .error s!"Query type {T} must match Select {Ts} type."

def checkQuery (Γ : Schema) : (t : Query) → (T : RelationType) → Except String (Σ' T, (WellFormedQuery Γ t T))
  | ⟨sel, frm, whr⟩, T => do
    let fromTable ← getFromTable Γ frm
    let ⟨Tf, wfrm⟩ ← checkFrom Γ fromTable frm
    let ⟨Ts, wsel⟩ ← checkSel Tf T sel
    let wwhr ← checkExpression Tf whr
    if heq : Ts = T ∧ wwhr.fst = .boolean then
      return ⟨Ts, (.mk (heq.left ▸ wsel) wfrm (heq.right ▸ wwhr.snd))⟩
    else
      .error s!"Query type {T} must match Select {Ts} type."

open Lean Elab Meta Term

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

syntax (name := pgquery) ident " |- " sqlQuery " ∶ " term : term

def fl : Nat × Bool × Nat → Float
  | (c, b, e) =>
    let sign := if b then -1.0 else 1.0
    let coefficient := Float.ofInt c
    let exponent := Float.pow 10.0 (Float.ofNat e)
    sign * coefficient * exponent

-- Default typing values for such cases e.G. is 3<3 bigInt or int?
partial def elabValue (stx : TSyntax `value) : TermElabM (Expr × Value) := do
  let (expr, val) ← match stx with
    | `(value|$v:num)         =>
      -- defaults to integer (see https://www.postgresql.org/docs/7.3/datatype.html)
      pure (mkApp (mkConst ``Value.integer) (mkApp (mkConst ``Int.ofNat) (mkNatLit v.getNat)), Value.integer v.getNat)
    | `(value|$v:scientific)  => do
      pure (mkApp (mkConst ``Value.double) (← Term.elabScientificLit v (mkConst `Float)), .double (fl v.getScientific))
    | `(value|$v:str)         =>
      -- Defaults to text: (see https://www.postgresql.org/docs/current/datatype-character.html)
      pure (mkApp2 (mkConst ``Value.varchar) (mkNatLit 255) (mkStrLit v.getString), .text v.getString)
    | `(value|NULL)              => pure (Lean.mkConst ``Value.null, .null)
    | `(value|($v:value))        => elabValue v
    | _                          => throwUnsupportedSyntax
    -- TODO: Include remaining types
  match checkValue val with
    | .ok ⟨_T, _p⟩ => pure (expr, val)
    | .error e => throwErrorAt stx e

def elabOp (stx : TSyntax `op) : TermElabM (Expr × Operator) :=
  match stx with
  | `(op|=)  => pure (mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.eq), .acop .eq)
  | `(op|<>) => pure (mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.ne), .acop .ne)
  | `(op|!=) => pure (mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.ne), .acop .ne)
  | `(op|<)  => pure (mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.lt), .acop .lt)
  | `(op|<=) => pure (mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.le), .acop .le)
  | `(op|>)  => pure (mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.gt), .acop .gt)
  | `(op|>=) => pure (mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.ge), .acop .ge)
  | `(op|+) => pure (mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.add), .aop .add)
  | `(op|-) => pure (mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.sub), .aop .sub)
  | `(op|/) => pure (mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.div), .aop .div)
  | `(op|*) => pure (mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.mul), .aop .mul)
  | `(op|%) => pure (mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.mod), .aop .mod)
  | `(op|||) => pure (mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.con), .aop .con)
  | _                => throwUnsupportedSyntax

-- Can be optimized by checking in the branches rather than at the end
partial def elabExpression (T : RelationType) (stx : TSyntax `expr) : TermElabM (Expr × Expression) := do
  let (expr, expression) ← match stx with
    | `(expr|$v:value) =>
      let (vexpr, v) ← elabValue v
      pure (mkApp (mkConst ``Expression.value) vexpr, .value v)
    | `(expr|$id:ident) => do
      match id.getId with
        | .str fst snd => pure (mkApp2 (mkConst ``Expression.field) (mkStrLit snd) (mkStrLit fst.toString), Expression.field snd fst.toString)
        | _ => throwUnsupportedSyntax
    | `(expr|+ $ae:expr) => do
      let (ae, aee) ← elabExpression T ae
      pure (mkApp2 (mkConst ``Expression.un) (mkConst ``UnaryOp.add) ae, .un .add aee)
    | `(expr|- $ae:expr) => do
      let (ae, aee) ← elabExpression T ae
      pure (mkApp2 (mkConst ``Expression.un) (mkConst ``UnaryOp.sub) ae, .un .sub aee)
    | `(expr|$be₁:expr AND $be₂:expr) => do
      let (ae₁, aee₁) ← elabExpression T be₁
      let (ae₂, aee₂) ← elabExpression T be₂
      pure (mkApp3 (mkConst ``Expression.bin) ae₁ (mkApp (mkConst ``Operator.bop) (mkConst ``BoolBinOp.and)) ae₂, .bin aee₁ (.bop .and) aee₂)
    | `(expr|$be₁:expr OR $be₂:expr) => do
      let (ae₁, aee₁) ← elabExpression T be₁
      let (ae₂, aee₂) ← elabExpression T be₂
      pure (mkApp3 (mkConst ``Expression.bin) ae₁ (mkApp (mkConst ``Operator.bop) (mkConst ``BoolBinOp.or)) ae₂, .bin aee₁ (.bop .and) aee₂)
    | `(expr|$ae₁:expr $ps:op $ae₂:expr) => do
      let (ae₁, aee₁) ← elabExpression T ae₁
      let (ae₂, aee₂) ← elabExpression T ae₂
      let (oexpr, op) ← elabOp ps
      pure (mkApp3 (mkConst ``Expression.bin) ae₁ oexpr ae₂, .bin aee₁ op aee₂)
    | `(expr|($be:expr)) => elabExpression T be
    | `(expr|TRUE) => pure (mkApp (mkConst ``Expression.value) (mkApp (mkConst ``Value.boolean) (mkConst ``true)), .value (.boolean true))
    | `(expr|FALSE) => do
      pure (mkApp (mkConst ``Expression.value) (mkApp (mkConst ``Value.boolean) (mkConst ``false)), .value (.boolean false))
    | `(expr|NOT $be:expr) => do
      let (ae, aee) ← elabExpression T be
      pure (mkApp2 (mkConst ``Expression.un) (mkConst ``UnaryOp.not) ae, .un .not aee)
    | s => throwError s
  match checkExpression T expression with
    | .ok ⟨_T, _p⟩ => pure (expr, expression)
    | .error e => throwErrorAt stx e

def elabSelectField (Γ : RelationType) (stx : TSyntax `selectField) : TermElabM (Expr × SelectField) := do
  let (expr, sf) ← match stx with
    | `(selectField|$field:ident) =>
      match field.getId with
        | .str fst snd =>
          pure (mkApp2 (mkConst ``SelectField.col) (mkStrLit snd) (mkStrLit fst.toString), .col snd fst.toString)
        | _ => throwUnsupportedSyntax
    | `(selectField|$field:ident AS $as:ident) => do
      match field.getId with
        | .str fst snd => do
          let fieldName := snd
          let tableName := fst.toString
          let alias := as.getId.toString
          pure (mkApp3 (mkConst ``SelectField.alias) (mkStrLit fieldName) (mkStrLit tableName) (mkStrLit alias), SelectField.alias fieldName tableName alias)
        | _ => throwUnsupportedSyntax
    | _ => throwUnsupportedSyntax
  match (SelectField.getTuple Γ sf) with
    | .some (_, _, T) => match checkSelectField Γ sf T with
      | .ok ⟨_T, _p⟩ => pure (expr, sf)
      | .error e => throwErrorAt stx e
    | .none => throwErrorAt stx "Field {sf} not in Context {Γ}"

def elabSelect (Γ T : RelationType) (stx : TSyntax `sqlSelect) : TermElabM (Expr × Select × RelationType) := do
  let (expr, sel) ← match stx with
    | `(sqlSelect|*)                          => do
      pure (mkApp (mkConst ``Select.all) (mkConst ``Bool.false), .all false)
    | `(sqlSelect|DISTINCT *)                 => do
      pure (mkApp (mkConst ``Select.all) (mkConst ``Bool.true), .all false)
    | `(sqlSelect|$cs:selectField,*)          => do
      let l ← cs.getElems.toList.mapM (elabSelectField Γ)
      let exprs := l.map fun (e, _) => e
      let sfs := l.map fun (_, sf) => sf
      let cols ← mkListLit (mkConst ``SelectField) exprs
      pure (mkApp2 (mkConst ``Select.list) (mkConst ``Bool.false) cols, .list false sfs)
    | `(sqlSelect|DISTINCT $cs:selectField,*) => do
      let sfzip ← cs.getElems.toList.mapM (elabSelectField Γ)
      let exprs := sfzip.map fun (e, _) => e
      let sfs := sfzip.map fun (_, sf) => sf
      let cols ← mkListLit (mkConst ``SelectField) exprs
      pure (mkApp2 (mkConst ``Select.list) (mkConst ``Bool.true) cols, .list false sfs)
    | _ => throwUnsupportedSyntax
  match checkSel Γ T sel with
    | .ok ⟨T, _p⟩ => pure (expr, sel, T)
    | .error e => throwErrorAt stx e

def elabConst (name : Name) : TermElabM Expr :=
  pure $ mkConst name

def elabJoin : TSyntax `join → TermElabM (Expr × Join)
  | `(join|INNER) => do pure (← elabConst `Join.inner, .inner)
  | `(join|LEFT)  => do pure (← elabConst `Join.left, .left)
  | `(join|RIGHT) => do pure (← elabConst `Join.right, .right)
  | `(join|OUTER) => do pure (← elabConst `Join.outer, .outer)
  | _             => throwUnsupportedSyntax

def throwUnsupportedLocalSyntax {α : Type} {stx : Syntax} : TermElabM α :=
  throwErrorAt stx "unexpected syntax\n{stx}"

partial def elabFrom (Γ : Schema) : TSyntax `sqlFrom → TermElabM (Expr × From)
  | `(sqlFrom|$t:ident)               =>
    pure (mkApp (mkConst ``From.table) (mkStrLit t.getId.toString), .table t.getId.toString)
  | `(sqlFrom|$f:sqlFrom AS $t:ident) => do
    let (fre, fr) ← elabFrom Γ f
    pure (mkApp2  (mkConst ``From.alias) fre (mkStrLit t.getId.toString), .alias fr t.getId.toString)
  | `(sqlFrom|$l:sqlFrom, $r:sqlFrom) => do
    let (fre₁, fr₁) ← elabFrom Γ l
    let (fre₂, fr₂) ← elabFrom Γ r
    pure (mkApp2 (mkConst ``From.implicitJoin) fre₁ fre₂, .implicitJoin fr₁ fr₂)
  | `(sqlFrom|$l:sqlFrom $j:join JOIN $r:sqlFrom ON $p:expr) => do
    let (fre₁, fr₁) ← elabFrom Γ l
    let (fre₂, fr₂) ← elabFrom Γ r
    let (joe, jo) ← elabJoin j
    match getFromTable Γ fr₁ with
      | .ok T₁ => match getFromTable Γ fr₂ with
        | .ok T₂ =>
            let (exe, ex) ← elabExpression (T₁++T₂) p
            pure (mkApp4 (mkConst ``From.join) joe fre₁ fre₂ exe, .join jo fr₁ fr₂ ex)
        | .error e => throwErrorAt r e
      | .error e => throwErrorAt l e
  | `(sqlFrom|($f:sqlFrom))           => do
    let (frme, frm) ← elabFrom Γ f
    pure (frme, frm)
  | `(sqlFrom| (SELECT $sel:sqlSelect FROM $frm:sqlFrom $[WHERE $expr]?) AS $id:ident) => do
    let (frme, frm') ← elabFrom Γ frm
    let fromTable := getFromTable Γ frm'
      match fromTable with
        | .ok fromTable =>
          let (whre, whr) ← match expr with
            | none => pure (mkApp (mkConst ``Expression.value) (mkApp (mkConst ``Value.boolean) (mkConst ``true)), Expression.value (.boolean true))
            | some expr => elabExpression fromTable expr
            -- TODO: how to infer inner sel type?
          let (sele, sel, _) ← elabSelect fromTable fromTable sel
          pure (mkApp4 (mkConst ``From.nestedJoin) sele frme whre (mkStrLit id.getId.toString), .nestedJoin sel frm' whr id.getId.toString)
        | .error e => throwErrorAt frm e
    | _ => throwUnsupportedSyntax

def elabCheckedFrom (Γ : Schema) (stx : TSyntax `sqlFrom) : TermElabM (Expr × From × RelationType) := do
  let (expr, frm) ← elabFrom Γ stx
  match getFromTable Γ frm with
    | .ok Tf => do
      match checkFrom Γ Tf frm with
      | .ok ⟨T, _p⟩ => pure (expr, frm, T)
      | .error e => throwErrorAt stx e
    | .error e => throwErrorAt stx e

def elabQuery (Γ : Schema) (T : RelationType) (stx : TSyntax `sqlQuery) : TermElabM Expr := do
  let (expr, query, Ts) ← match stx with
    | `(sqlQuery| SELECT $sel FROM $frm:sqlFrom $[WHERE $expr]?) =>
      let (frme, frm', Tf) ← elabCheckedFrom Γ frm
      let (whre, whr) ← match expr with
        | none     => pure (mkApp (mkConst ``Expression.value) (mkApp (mkConst ``Value.boolean) (mkConst ``true)), .value (.boolean true))
        | some expr => elabExpression Tf expr
      let (sele, sel, Ts) ← elabSelect Tf T sel
      pure (mkApp3 (mkConst ``Query.mk) sele frme whre, Query.mk sel frm' whr, Ts)
    | _ => throwUnsupportedSyntax
  match checkQuery Γ query Ts with
    | .ok ⟨_, _⟩ => pure expr
    | .error e => throwErrorAt stx e

-- TODO add remaining Values
def exprToDataType : Expr → TermElabM DataType
  | .const ``DataType.bigInt _ => pure .bigInt
  | .const ``DataType.integer _ => pure .integer
  | .const ``DataType.date _ => pure .date
  | _ => throwUnsupportedSyntax

def exprToField : Expr → TermElabM (String × String × DataType)
  | .app (.app _ <| .lit <| .strVal n) (.app (.app _ <| .lit <| .strVal t) l) => do
    pure (n, t, (← exprToDataType l))
  | e => throwError "{e}"

def exprToRelationType : Expr → TermElabM RelationType
  | L => do
    if let .some table := L.listLit? then
      table.snd.mapM exprToField
    else
      throwError "{L} is not a valid RelationType."

def exprToTable : Expr → TermElabM (String × RelationType)
  | .app (.app _ <| .lit <| .strVal <| tableName) L => do
    pure (tableName, ← exprToRelationType L)
  | _ => throwUnsupportedSyntax

def exprToSchema : Expr → TermElabM Schema := fun x => do
  if let .some styp := x.listLit? then
    styp.snd.mapM exprToTable
  else
    throwUnsupportedSyntax

def List.id : List α → List α
 | l => l

elab_rules : term
  | `(pgquery| $id |- $query ∶ $relation) => do
    let env ← getEnv
    if let .some s := env.find? id.getId then
      let Γ ← exprToSchema s.value!
      let TExpr ← elabAppArgs (Expr.const ``List.id [0]) #[] #[Arg.stx relation] .none (explicit := false) (ellipsis := false)
      let T ← exprToRelationType (← whnf TExpr)
      let query ← elabQuery Γ T query
      pure query
    else
      throwUnsupportedSyntax

def schema : Schema := [("employee", [("id", "employee", .bigInt)]), ("customer", [("id", "customer", .bigInt), ("date", "customer", .date)])]

-- Should select all ✓
#check schema |- SELECT * FROM employee ∶ [("id", "employee", DataType.bigInt)]
-- Should not select too many ✓
#check schema |- SELECT * FROM employee ∶ [("id", "employee", DataType.bigInt), ("id", "employee", .bigInt)]
-- Should not select too few ✓
#check schema |- SELECT * FROM customer ∶ [("id", "customer", DataType.bigInt)]
-- Should select all joined ✓
#check schema |- SELECT * FROM employee, customer ∶ [("id", "employee", DataType.bigInt), ("id", "customer", DataType.bigInt), ("date", "customer", DataType.date)]
-- Should select some ✓
#check schema |- SELECT customer.date FROM employee, customer ∶ [("date", "customer", DataType.date)]
-- Should fail on ambiguity × (Non prefixed field inference not yet supported)
#check schema |- SELECT id FROM employee, customer ∶ [("date", "customer", DataType.date)]
-- Should select only corresponding id ✓
#check schema |- SELECT customer.id FROM employee, customer ∶ [("id", "customer", DataType.bigInt)]
#check schema |- SELECT employee.id FROM employee, customer ∶ [("id", "employee", DataType.bigInt)]
-- Should fail on outdated select field ✓
#check schema |- SELECT employee.id FROM employee AS b, customer ∶ [("id", "b", DataType.bigInt)]
-- Should succeed with table alias ✓
#check schema |- SELECT b.id FROM employee AS b, customer ∶ [("id", "b", DataType.bigInt)]
-- Should succeed with field alias ✓
#check schema |- SELECT employee.id AS fakeID FROM employee ∶ [("fakeID", "employee", DataType.bigInt)]
-- Should only allow nesting with alias ✓
#check schema |- SELECT a.id FROM (SELECT * FROM customer) AS a ∶ [("id", "a", DataType.bigInt)]
#check schema |- SELECT a.id FROM (SELECT * FROM customer) ∶ [("id", "a", .bigInt)]
-- Should succeed on correct expr ✓ × (TODO: check date)
#check schema |- SELECT customer.id FROM customer WHERE +(customer.id / 2) = (-1 + 0.0) AND TRUE ∶ [("id", "customer", DataType.bigInt)]
#check schema |- SELECT customer.id FROM customer WHERE (customer.date + 8) > customer.date ∶ [("id", "customer", DataType.bigInt)]
-- Should fail on wrong value
#check schema |- SELECT * FROM employee WHERE 9999999999 > 0 ∶ [("id", "employee", DataType.bigInt)]
-- Should fail on wrong expr
#check schema |- SELECT customer.id FROM customer WHERE 9 AND TRUE ∶ [("id", "customer", DataType.bigInt)]
#check schema |- SELECT customer.id FROM customer WHERE TRUE + 8 ∶ [("id", "customer", DataType.bigInt)]
#check schema |- SELECT customer.id FROM customer WHERE (8 + customer.date) > customer.date ∶ [("id", "customer", DataType.bigInt)]
-- Should succeed on double dot alias ✓
#check schema |- SELECT a.a.a FROM (SELECT customer.id AS a FROM customer) AS a.a ∶ [("a", "a.a", DataType.bigInt)]
-- Should nest deeply × (TODO: how to infer inner sel type?)
#check schema |- SELECT a.id FROM (SELECT b.id FROM (SELECT customer.id FROM customer) AS b) AS a ∶ [("id", "a", DataType.bigInt)]
