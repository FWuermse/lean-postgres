import Aesop

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
inductive Typ
  | integer
  | bigInt
  | bit
  | varbit
  | boolean
  | char
  | varchar
  | date
  | real
  | double
  deriving BEq, DecidableEq

  instance : LawfulBEq Typ where
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

abbrev RelationType := List (String × Typ)

abbrev Schema := List (String × RelationType)

inductive Value
  | integer : Fin 4 → Value
  | bigInt  : Fin 8 → Value
  | bit  : Nat → Array Bool → Value
  | varbit : Nat → Array Bool → Value
  | boolean : Bool → Value
  | char : Nat → String → Value
  | varchar : Nat → String → Value
  | date : Nat → Fin 13 → Fin 32 → Value
  | real : Float → Value
  | double : Float → Value -- TODO: alternatives?

inductive WellFormedValue : Value → Typ → Prop
  | integer : WellFormedValue (.integer i) .integer
  | bigInt : WellFormedValue (.bigInt i) .bigInt
  | bit : b.size = n → WellFormedValue (.bit n b) .bit
  | bitVarying : b.size ≤ n → WellFormedValue (.varbit n b) .varbit
  | boolean : WellFormedValue (.boolean b) .boolean
  | char : s.length = n → WellFormedValue (.char n s) .char
  | charVarying : s.length ≤ n → WellFormedValue (.varchar n s) .varchar
  | date : m > 0 ∧ d > 0 → WellFormedValue (.date y m d) .date
  | real : WellFormedValue (.real f) .real
  | double : WellFormedValue (.double f) .double

inductive Join
  | inner | left | right | outer

def Join.toString : Join → String
  | inner => "INNER"
  | left  => "LEFT"
  | right => "RIGHT"
  | outer => "OUTER"

instance : ToString Join := ⟨Join.toString⟩

/-
# Aexpr

## Type T
Typ

## Context Ctx
RelationType × RelationType (contents of From/Select clauses or both tables in case of joins)

## Predicates
value: WellFormedValue for type T
field: (name, T) ∈ Ctx.fst ∨ (name, T) ∈ Ctx.snd
-/
inductive Aexpr
  | value : Value → Aexpr
  | field : String → Aexpr

@[aesop unsafe 100% apply]
inductive WellFormedAexpr : RelationType × RelationType → Aexpr → Typ → Prop
  | value v :
    WellFormedValue v T →
    ----------------------------------
    WellFormedAexpr Γ (.value v) T
  | field :
    (s, T) ∈ Γ.fst ∨ (s, T) ∈ Γ.snd →
    ----------------------------------
    WellFormedAexpr Γ (.field s) T

inductive Aop
  | eq
  | ne
  | lt
  | le
  | gt
  | ge

inductive Bop
  | and
  | or

/-
# Bexpr

## Type T
Bool (implicit)

## Context Ctx
RelationType × RelationType (contents of From/Select clauses or both tables in case of joins)

## Predicates
not: WellFormedBexpr
acmp: WellFormedAexpr₁ ∧ WellFormedAexpr₂ ∧ Type(WellFormedAexpr₁) = Type(WellFormedAexpr₂)
bcmp: WellFormedBexpr₁ ∧ WellFormedBexpr₂
-/
inductive Bexpr
  | tt
  | ff
  | not  : Bexpr → Bexpr
  | bcmp : Bexpr → Bop → Bexpr → Bexpr
  | acmp : Aexpr → Aop → Aexpr → Bexpr

@[aesop unsafe 100% apply]
inductive WellFormedBexpr : (RelationType × RelationType) → Bexpr → Prop
  | tt : WellFormedBexpr Γ .tt
  | ff : WellFormedBexpr Γ .ff
  | not :
    WellFormedBexpr Γ b →
    ----------------------------------
    WellFormedBexpr Γ (.not b)
  | bcmp :
    WellFormedBexpr Γ b₁ →
    WellFormedBexpr Γ b₂ →
    ----------------------------------
    WellFormedBexpr Γ (.bcmp b₁ op b₂)
  | acmp :
    WellFormedAexpr Γ a₁ T →
    WellFormedAexpr Γ a₂ T →
    ----------------------------------
    WellFormedBexpr Γ (.acmp a₁ op a₂)

/-
# SelectField

## Type T
Typ

## Context Ctx
RelationType

## Predicates
(name, _) ∈ Ctx
-/
inductive SelectField
  | col   : String → SelectField
  | alias : String → String         → SelectField
  deriving BEq, DecidableEq

def SelectField.name
  | col s => s
  | «alias» _ s => s

inductive WellFormedSelectField : RelationType → SelectField → Typ → Prop
  | col (n : String) :
    (n, T) ∈ Γ →
    WellFormedSelectField Γ (.col n) T
  | alias (n : String) :
    (n, T) ∈ Γ →
    WellFormedSelectField Γ (.alias a n) T

/-
# Select

## Type T
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
    Forall (WellFormedSelectField Γ . _) ss →
    ----------------------------------
    WellFormedSelect Γ (.list _ ss) T
  | all (h: ∀ x ∈ T, x ∈ Γ) :
    ----------------------------------
    WellFormedSelect Γ t T

mutual
/-
# From

## Type T
RelationType

## Context Ctx
Schema

## Predicates
table: (name, T) ∈ Ctx
alias: WellFormedFrom ∧ (alias, _) ∉ Ctx (maybe?)
join/implicitJoin: WellFormedFrom₁ ∧ WellFormedFrom₂ ∧ T = a ++ b ∧ WellFormedProp
nestedJoin: WellFormedQuery q
-/
inductive From where
  | table        : (name : String) → From
  | alias        : From → (as : String) → From
  | join         : Join → From → From → Bexpr → From
  | implicitJoin : From → From → From
  | nestedJoin   : Query → From

/-
# Query

## Type T
RelationType

## Context Ctx
Schema

## Predicates
WellTyped Select in ctx
WellTyped From in ctx
WellTyped Where in ctx
-/
inductive Query where
  | mk : Select → From → Bexpr → Query
end

mutual
@[aesop unsafe 100% apply]
inductive WellFormedFrom : Schema → From → RelationType → Prop
  | table (n : String) :
    (n, T) ∈ Γ →
    ----------------------------------
    WellFormedFrom Γ (.table n) T
  | alias :
    WellFormedFrom Γ f T →
    ----------------------------------
    WellFormedFrom Γ (.alias f s) T
  | join :
    WellFormedFrom Γ f₁ T₁ →
    WellFormedFrom Γ f₂ T₂ →
    WellFormedBexpr (T₁, T₂) p →
    ----------------------------------
    WellFormedFrom Γ (.join j f₁ f₂ p) (T₁ ++ T₂)
  | implicitJoin :
    WellFormedFrom Γ f₁ T₁ →
    WellFormedFrom Γ f₂ T₂ →
    ----------------------------------
    WellFormedFrom Γ (.implicitJoin f₁ f₂) (T₁ ++ T₂)
  | nestedFrom :
    WellFormedQuery Γ q T →
    ----------------------------------
    WellFormedFrom Γ (.nestedJoin q) T

@[aesop unsafe 100% apply]
inductive WellFormedQuery : Schema → Query → RelationType → Prop
  | mk :
    WellFormedSelect Tf s Ts →
    WellFormedFrom Γ f Tf →
    WellFormedBexpr (Ts, Tf) w →
    ----------------------------------
    WellFormedQuery Γ ⟨s, f, w⟩ Ts
end

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
  | .nestedJoin (.mk s f _) => match s with
    | .all _ => getFromTable Γ f
    | .list _ l =>
      return l.filterMap fun (sf : SelectField) =>
        match getFromTable Γ f with
          | .ok rt => match rt.find? (fun (n, _) => n == sf.name) with
            | .some v => .some v
            | .none => none
          | .error _ => .none

@[simp]
def checkSelectField (Γ : RelationType) (s : SelectField) (T : Typ) : Except String (Σ' T, WellFormedSelectField Γ s T) := match s with
  | .col s => do
    if h : (s, T) ∈ Γ then
      pure ⟨T, WellFormedSelectField.col s h⟩
    else
      .error s!"Selected field {s} is not in the current context."
  | .alias a s =>
    if h : (s, T) ∈ Γ then
      pure ⟨T, WellFormedSelectField.alias s h⟩
    else
      .error s!"Selected field {s} as {a} is not in the current context."

instance (Γ : RelationType) (T : Typ) : DecidablePred (fun s : SelectField => (checkSelectField Γ s T).isOk) :=
  fun s =>
    match s with
    | .col name =>
      if h : (name, T) ∈ Γ then
        isTrue (by simp [h]; rfl)
      else
        isFalse (by simp [h]; rfl)
    | .alias a name =>
      if h : (name, T) ∈ Γ then
        isTrue (by simp [h]; rfl)
      else
        isFalse (by simp [h]; rfl)

instance (Γ : RelationType) (s : SelectField) (T : Typ) : Decidable (WellFormedSelectField Γ s T) := match s with
  | .col name =>
    if h : (name, T) ∈ Γ then
      isTrue (WellFormedSelectField.col name h)
    else
      isFalse (fun hWf => match hWf with
        | WellFormedSelectField.col _ h' => by contradiction)
  | .alias a name =>
    if h : (name, T) ∈ Γ then
      isTrue (WellFormedSelectField.alias name h)
    else
      isFalse (fun hWf => match hWf with
        | WellFormedSelectField.alias _ h' => by contradiction)

def checkSel (Γ T : RelationType) (s : Select) : Except String (Σ' T, WellFormedSelect Γ s T) := match s with
  | .all _ =>
    if h : ∀ x ∈ T, x ∈ Γ then
      let wsel := WellFormedSelect.all h
      pure ⟨T, wsel⟩
    else
      .error "The type of `SELECT *` must match the FROM clause."
  | .list _ ss =>
    let T : Typ := Typ.bigInt
    if h : Forall (fun s : SelectField => WellFormedSelectField Γ s T) ss then
      pure ⟨Γ, WellFormedSelect.list ss h⟩
    else
      .error "All fields to be selected must occur in the selected tables."

def checkValue (v : Value) : Except String (Σ' T, WellFormedValue v T) := match v with
  | .integer _ => pure ⟨.integer, .integer⟩
  | .bigInt _ => pure ⟨.bigInt, .bigInt⟩
  | .bit n ba => if h : ba.size = n then
      pure ⟨.bit, .bit h⟩
    else
      .error s!"ByteStream {ba} must have exactly length {n}"
  | .varbit n ba => if h : ba.size ≤ n then
      pure ⟨.varbit, .bitVarying h⟩
    else
      .error s!"ByteStream {ba} must not exceed length {n}"
  | .boolean _ => pure ⟨.boolean, .boolean⟩
  | .char n s => if h : s.length = n then
      pure ⟨.char, .char h⟩
    else
      .error s!"String {s} must have exactly length {n}"
  | .varchar n s => if h : s.length ≤ n then
      pure ⟨.varchar, .charVarying h⟩
    else
      .error s!"String {s} must not exceed length {n}"
  | .date y m d => if h : m > 0 ∧ d > 0 then
      pure ⟨.date, .date h⟩
    else
      .error s!"Invalid date: {y}-{m}-{d}"
  | .real _ => pure ⟨.real, .real⟩
  | .double _ => pure ⟨.double, .double⟩

def checkAexpr (Γ : RelationType × RelationType) (a : Aexpr) : Except String (Σ' T, WellFormedAexpr Γ a T) := match a with
  | .field name =>
    let field := (Γ.fst.find? fun (n, _) => n == name).orElse fun _ => (Γ.snd.find? fun (n, _) => n == name)
    if let .some (_, t) := field then
      if h : (name, t) ∈ Γ.fst ∨ (name, t) ∈ Γ.snd then
        let waexpr := WellFormedAexpr.field
        pure ⟨t, waexpr h⟩
      else
        .error s!"The field {name} is not present in this context."
    else
      .error s!"The field {name} is not present in this context."
  | .value v => do
    let ⟨T, hv⟩ ← checkValue v
    pure ⟨T, .value v hv⟩

def checkWhere (Γ : RelationType × RelationType) (w : Bexpr) : Except String (PLift $ WellFormedBexpr Γ w) :=
match w with
  | .tt => return PLift.up .tt
  | .ff => return PLift.up .ff
  | .not bexpr => do
    let b ←  checkWhere Γ bexpr
    return PLift.up <| .not b.down
  | .bcmp bexpr₁ _ bexpr₂ => do
    let fst ← checkWhere Γ bexpr₁
    let snd ← checkWhere Γ bexpr₂
    return PLift.up (.bcmp fst.down snd.down)
  | .acmp aexpr₁ _ aexpr₂ => do
    let ⟨a₁, fst⟩ ← checkAexpr Γ aexpr₁
    let ⟨a₂, snd⟩ ← checkAexpr Γ aexpr₂
    if h : a₂ = a₁ then
      return PLift.up (.acmp fst (h ▸ snd))
    else
      .error "Only expressions of the same type can be compared."

mutual
def checkFrom (Γ : Schema) (T : RelationType) (t : From) : Except String (Σ' T, WellFormedFrom Γ t T) := match t with
  | .table name =>
      if mem : (name, T) ∈ Γ then
        let wfrm := .table name mem
        pure ⟨T, wfrm⟩
      else
        .error s!"Table {name} not in Schema."
  | .alias frm as => do
      let ⟨T, wfrm⟩ ← checkFrom Γ T frm
      pure ⟨T, .alias wfrm⟩
  | .implicitJoin frm₁ frm₂ => do
    let ⟨T₁, wfrm₁⟩ ← checkFrom Γ T frm₁
    let ⟨T₂, wfrm₂⟩ ← checkFrom Γ T frm₂
    pure ⟨T₁++T₂, .implicitJoin wfrm₁ wfrm₂⟩
  | .join _ frm₁ frm₂ prop => do
    let ⟨T₁, wfrm₁⟩ ← checkFrom Γ T frm₁
    let ⟨T₂, wfrm₂⟩ ← checkFrom Γ T frm₂
    let prp ← checkWhere (T₁, T₂) prop
    let wfrm := WellFormedFrom.join wfrm₁ wfrm₂
    pure ⟨_, wfrm prp.down⟩
  | .nestedJoin q => do
    let wqry ← check Γ q T
    pure ⟨T, .nestedFrom wqry.down⟩

def check (Γ : Schema) : (t : Query) → (T : RelationType) → Except String (PLift (WellFormedQuery Γ t T))
  | ⟨sel, frm, whr⟩, T => do
    let fromTable ← getFromTable Γ frm
    let ⟨Tf, wfrm⟩ ← checkFrom Γ fromTable frm
    let ⟨Ts, wsel⟩ ← checkSel Tf T sel
    let wwhr ← checkWhere (T, Tf) whr
    if heq : Ts = T then
      return PLift.up (.mk (heq ▸ wsel) wfrm wwhr.down)
    else
      .error "Query type must match Select type."
end
