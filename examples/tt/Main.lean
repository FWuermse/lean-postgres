import Aesop

-- instance LawfulBEq
inductive Typ
  | bigInt
  | bit
  | bitVarying
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
    cases a <;>
    cases b <;>
    rw [BEq.beq] at hab <;>
    try contradiction <;>
    rfl
    repeat rfl
  rfl := by
    intro h
    . rw [BEq.beq]
      cases h <;> rfl

abbrev RelationType := List (String × Typ)

abbrev Schema := List (String × RelationType)

inductive Join
  | inner | left | right | outer

/-
# Aexpr

## Type T
Typ

## Context Ctx
RelationType × RelationType
Ctx.fst represents the projections aka aliasing, Ctx.snd the result of a from clause

## Predicates
field: name ∈ Ctx.fst ∨ name ∈ Ctx.snd
-/
inductive Aexpr
  | value : Typ → Aexpr
  | field : String × Typ → Aexpr

@[aesop unsafe 100% apply]
inductive WellFormedAexpr : RelationType × RelationType → Aexpr → Type → Prop
  | value :
    ----------------------------------
    WellFormedAexpr Γ (.value v) Typ
  | field : field ∈ Γ.fst ∨ field ∈ Γ.snd →
    ----------------------------------
    WellFormedAexpr Γ (.field n) Typ

inductive Aop
  | eq
  | ne
  | lt
  | le
  | gt
  | ge

def Aop.aop {α : Type} [DecidableEq α] [LT α] [LE α] : Aop → (α → α → Bool)
  | Aop.eq => (. == .)
  | Aop.ne => (. != .)
  | _ => sorry

inductive Bop
  | and
  | or

def Bop.bop
  | and => Bool.and
  | or => Bool.or

/-
# Bexpr

## Type T
Bool

## Context Ctx
(RelationType) × (RelationType)

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

-- TODO: is it better for Type to be a Bool or Prop?
@[aesop unsafe 100% apply]
inductive WellFormedBexpr : (RelationType × RelationType) → Bexpr → Bool → Prop
  | tt : WellFormedBexpr Γ .tt true
  | ff : WellFormedBexpr Γ .ff false
  | not :
    WellFormedBexpr Γ b T →
    ----------------------------------
    WellFormedBexpr Γ (.not b) T
  | bcmp :
    WellFormedBexpr Γ b₁ T₁ →
    WellFormedBexpr Γ b₂ T₂ →
    ----------------------------------
    WellFormedBexpr Γ (.bcmp b₁ op b₂) T₃
  | acmp :
    WellFormedAexpr Γ a₁ T₁ →
    WellFormedAexpr Γ a₂ T₂ →
    ----------------------------------
    WellFormedBexpr Γ (.acmp a₁ op a₂) T₃
  -- TODO: case split over op in order to determine T₃ in relation to T₁, T₂?

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
nestedJoin: (_, Query) ∈ Ctx ∧ WellTypedQuery
-/
inductive From where
  | table        : (name : String) → From
  | alias        : From → (as : String) → From
  | join         : Join → From → From → Bexpr → From
  | implicitJoin : From → From → From
  -- | nestedJoin   : Query → From

@[aesop unsafe 100% apply]
inductive WellFormedFrom : Schema → From → RelationType → Prop
  | table (n : String) :
    (n, T) ∈ Γ →
    WellFormedFrom Γ (.table n) T
  | alias :
    a → WellFormedFrom Γ f T →
    WellFormedFrom Γ f' T
  | join :
    WellFormedFrom Γ f₁ T₁ →
    WellFormedFrom Γ f₂ T₂ →
    WellFormedBexpr (T₁, T₂) p _ →
    WellFormedFrom Γ (.join j f₁ f₂ p) (T₁ ++ T₂)
  | implicitJoin :
    WellFormedFrom Γ f₁ T₁ →
    WellFormedFrom Γ f₂ T₂ →
    WellFormedFrom Γ (.implicitJoin f₁ f₂) (T₁ ++ T₂)

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

/-
# Select

## Type T
RelationType

## Context Ctx
RelationType

## Predicates
list: distrinct → ∀ s ∈ List SelectFields, WellFormedSelectField
all: (_, T) ∈ Ctx
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
structure Query where
  select   : Select
  «from»   : From
  «where»  : Bexpr

@[aesop unsafe 100% apply]
inductive WellFormedQuery : Schema → Query → RelationType → Prop
  | mk : WellFormedSelect Tf s Ts → WellFormedFrom Γ f Tf → WellFormedBexpr (Ts, Tf) b Tb → WellFormedQuery Γ ⟨s, f, b⟩ Ts


example : WellFormedQuery [("myTable", [("MyField", .bigInt)])] ⟨.all false, .table "myTable", .tt⟩ [("MyField", Typ.bigInt)] := by
  apply WellFormedQuery.mk
  . apply WellFormedSelect.all
    . simp
      have h : ("MyField", .bigInt) ∈ [("MyField", Typ.bigInt)] := by simp
      apply h
  . apply WellFormedFrom.table "myTable"
    . aesop
  . apply WellFormedBexpr.tt

def getFromTable (Γ : Schema) : (t : From) → Option RelationType
  | .table name =>
    let table := Γ.find? fun (n, _) => n == name
    table.map fun (_, T) => T
  | .alias frm _ => getFromTable Γ frm
  | .implicitJoin frm₁ frm₂ => do
    let fst ← getFromTable Γ frm₁
    let snd ← getFromTable Γ frm₂
    fst ++ snd
  | .join _ frm₁ frm₂ _ => do
    let fst ← getFromTable Γ frm₁
    let snd ← getFromTable Γ frm₂
    fst ++ snd

def checkSelectField (Γ : RelationType) (s : SelectField) (T : Typ) : Option (Σ' T, WellFormedSelectField Γ s T) := match s with
  | .col s => do
    if h : (s, T) ∈ Γ then
      pure ⟨T, WellFormedSelectField.col s h⟩
    else
      .none
  | .alias _ s =>
    if h : (s, T) ∈ Γ then
      pure ⟨T, WellFormedSelectField.alias s h⟩
    else
      .none

instance (Γ : RelationType) (T : Typ) : DecidablePred (fun s : SelectField => (checkSelectField Γ s T).isSome) :=
  fun s =>
    match s with
    | .col name =>
      if h : (name, T) ∈ Γ then
        isTrue (by simp [checkSelectField, h])
      else
        isFalse (by simp [checkSelectField, h])
    | .alias a name =>
      if h : (name, T) ∈ Γ then
        isTrue (by simp [checkSelectField, h])
      else
        isFalse (by simp [checkSelectField, h])

instance (Γ : RelationType) (s : SelectField) (T : Typ) : Decidable (WellFormedSelectField Γ s T) :=
  match s with
  | .col name =>
    if h : (name, T) ∈ Γ then
      isTrue (WellFormedSelectField.col name h)
    else
      isFalse (fun hWf =>
        match hWf with
        | WellFormedSelectField.col _ h' => by contradiction)
  | .alias a name =>
    if h : (name, T) ∈ Γ then
      isTrue (WellFormedSelectField.alias name h)
    else
      isFalse (fun hWf => match hWf with
        | WellFormedSelectField.alias _ h' => by contradiction)

def checkSel (Γ T : RelationType) (s : Select) : Option (Σ' T, WellFormedSelect Γ s T) := match s with
  | .all _ =>
    if h : ∀ x ∈ T, x ∈ Γ then
      let wsel := WellFormedSelect.all h
      pure ⟨T, wsel⟩
    else
      .none
  | .list _ ss =>
    let T : Typ := Typ.bigInt
    if h : Forall (fun s : SelectField => WellFormedSelectField Γ s T) ss then
      pure ⟨Γ, WellFormedSelect.list ss h⟩
    else
      .none

def checkAexpr (Γ : RelationType × RelationType) (a : Aexpr) : Option (Σ' T, WellFormedAexpr Γ a T) := match a with
  | .field (name, typ) =>
    if h : (name, typ) ∈ Γ.fst ∨ (name, typ) ∈ Γ.snd then
      let waexpr := WellFormedAexpr.field
      pure ⟨_, waexpr h⟩
    else
      .none
  | .value v => pure ⟨_, @WellFormedAexpr.value Γ v⟩

def checkWhere (Γ : RelationType × RelationType) (w : Bexpr) : Option (Σ' T, WellFormedBexpr Γ w T) :=
match w with
  | .tt => pure ⟨_, WellFormedBexpr.tt⟩
  | .ff => pure ⟨_, WellFormedBexpr.ff⟩
  | .not bexpr => (checkWhere Γ bexpr).map fun ⟨_, e⟩ => ⟨_, WellFormedBexpr.not e⟩
  | .bcmp bexpr₁ bop bexpr₂ => do
    let ⟨b₁, fst⟩ ← checkWhere Γ bexpr₁
    let ⟨b₂, snd⟩ ← checkWhere Γ bexpr₂
    pure ⟨bop.bop b₁ b₂, @WellFormedBexpr.bcmp Γ bexpr₁ b₁ bexpr₂ b₂ bop _ fst snd⟩
  | .acmp aexpr₁ aop aexpr₂ => do
    if let .some ⟨a₁, fst⟩ := checkAexpr Γ aexpr₁ then
      if let .some ⟨a₂, snd⟩ := checkAexpr Γ aexpr₂ then
        pure ⟨true, @WellFormedBexpr.acmp Γ aexpr₁ a₁ aexpr₂ a₂ aop _ fst snd⟩ -- TODO: replace true with actual comparison (if it's even required)
      else
        .none
    else
      .none

def checkFrom (Γ : Schema) (T : RelationType) (t : From) : Option (Σ' T, WellFormedFrom Γ t T) := match t with
  | .table name =>
      if mem : (name, T) ∈ Γ then
        let wfrm := WellFormedFrom.table name mem
        pure ⟨T, wfrm⟩
      else
        .none
  | .alias frm as =>
    if let .some ⟨T, wfrm⟩ := checkFrom Γ T frm then
      let wfrm := WellFormedFrom.alias as wfrm
      pure ⟨T, wfrm⟩
    else
      .none
  | .implicitJoin frm₁ frm₂ =>
    if let .some ⟨T₁, wfrm₁⟩ := checkFrom Γ T frm₁ then
      if let .some ⟨T₂, wfrm₂⟩ := checkFrom Γ T frm₂ then
        let wfrm := WellFormedFrom.implicitJoin wfrm₁ wfrm₂
        pure ⟨T₁++T₂, wfrm⟩
      else
        .none
    else
      .none
  | .join _ frm₁ frm₂ prop =>
    if let .some ⟨T₁, wfrm₁⟩ := checkFrom Γ T frm₁ then
      if let .some ⟨T₂, wfrm₂⟩ := checkFrom Γ T frm₂ then
        if let .some ⟨_, prp⟩ := checkWhere (T₁, T₂) prop then
          let wfrm := @WellFormedFrom.join _ Γ frm₁ T₁ frm₂ T₂ prop _ wfrm₁ wfrm₂
          pure ⟨_, wfrm prp⟩
        else
          .none
      else
        .none
    else
      .none

-- Error monad (error, PLift..)
-- Lean error location at actual location (withRef combinators as part of AST Nodes)
def check (Γ : Schema) : (t : Query) → (T : RelationType) → Option (PLift (WellFormedQuery Γ t T))
  | ⟨sel, frm, whr⟩, Ts => do
    if let .some fromTable := getFromTable Γ frm then
      if let .some ⟨Tf, wfrm⟩ := checkFrom Γ fromTable frm then
        if let .some ⟨Ts', wsel⟩ := checkSel Tf Ts sel then
          if heq : Ts' = Ts then
            if let .some ⟨_, wwhr⟩ := checkWhere (Ts, Tf) whr then
              return PLift.up (.mk (Eq.subst heq wsel) wfrm wwhr)
            else
              .none
          else
            .none
        else
          .none
      else
        .none
    else
      .none
