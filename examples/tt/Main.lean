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

def Aop.aop {α : Type} [DecidableEq α] [LT α] [DecidableRel (@LT.lt α _)] [LE α] [DecidableRel (@LE.le α _)] : Aop → (α → α → Bool)
  | Aop.eq => (. == .)
  | Aop.ne => (. != .)
  | Aop.le => (. ≤ .)
  | Aop.lt => (. < .)
  | Aop.ge => (. ≥ .)
  | Aop.gt => (. > .)

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

def From.toString
  | table n => n
  | «alias» f _ => f.toString
  | join j f₁ f₂ _ => s!"{f₁.toString} {j} {f₂.toString}"
  | implicitJoin f₁ f₂ => s!"{f₁.toString}, {f₂.toString}"

instance : ToString From := ⟨From.toString⟩

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
    . rw [List.mem_singleton]
  . apply WellFormedBexpr.tt

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

@[simp]
def checkSelectField (Γ : RelationType) (s : SelectField) (T : Typ) : Except String (Σ' T, WellFormedSelectField Γ s T) := match s with
  | .col s => do
    if h : (s, T) ∈ Γ then
      pure ⟨T, WellFormedSelectField.col s h⟩
    else
      .error s!"\t\t\tSelected field {s} is not in the current context."
  | .alias a s =>
    if h : (s, T) ∈ Γ then
      pure ⟨T, WellFormedSelectField.alias s h⟩
    else
      .error s!"\t\t\tSelected field {s} as {a} is not in the current context."

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
      .error "\tSelectError:\n\t\tThe type of 'SELECT * ' must match the FROM clause."
  | .list _ ss =>
    let T : Typ := Typ.bigInt
    if h : Forall (fun s : SelectField => WellFormedSelectField Γ s T) ss then
      pure ⟨Γ, WellFormedSelect.list ss h⟩
    else
      .error "\tSelectError:\n\t\tll fields to be selected must occur in the selected tables."

def checkAexpr (Γ : RelationType × RelationType) (a : Aexpr) : Except String (Σ' T, WellFormedAexpr Γ a T) := match a with
  | .field (name, typ) =>
    if h : (name, typ) ∈ Γ.fst ∨ (name, typ) ∈ Γ.snd then
      let waexpr := WellFormedAexpr.field
      pure ⟨_, waexpr h⟩
    else
      .error s!"\t\tAExprError:\n\t\t\tThe field {name} is not present in this context."
  | .value v => pure ⟨_, @WellFormedAexpr.value Γ v⟩

def checkWhere (Γ : RelationType × RelationType) (w : Bexpr) : Except String (Σ' T, WellFormedBexpr Γ w T) :=
match w with
  | .tt => pure ⟨_, WellFormedBexpr.tt⟩
  | .ff => pure ⟨_, WellFormedBexpr.ff⟩
  | .not bexpr => (checkWhere Γ bexpr).map fun ⟨_, e⟩ => ⟨_, WellFormedBexpr.not e⟩
  | .bcmp bexpr₁ bop bexpr₂ => do
    let ⟨b₁, fst⟩ ← checkWhere Γ bexpr₁
    let ⟨b₂, snd⟩ ← checkWhere Γ bexpr₂
    pure ⟨bop.bop b₁ b₂, @WellFormedBexpr.bcmp Γ bexpr₁ b₁ bexpr₂ b₂ bop _ fst snd⟩
  | .acmp aexpr₁ aop aexpr₂ => match checkAexpr Γ aexpr₁ with
    | .ok ⟨a₁, fst⟩ => match checkAexpr Γ aexpr₂ with
      | .ok ⟨a₂, snd⟩ => pure ⟨true, @WellFormedBexpr.acmp Γ aexpr₁ a₁ aexpr₂ a₂ aop _ fst snd⟩ -- TODO: replace true with actual comparison (if it's even required)
      | .error e => .error s!"\tWhereError:\n{e}"
    | .error e => .error s!"\tWhereError:\n{e}"

def checkFrom (Γ : Schema) (T : RelationType) (t : From) : Except String (Σ' T, WellFormedFrom Γ t T) := match t with
  | .table name =>
      if mem : (name, T) ∈ Γ then
        let wfrm := WellFormedFrom.table name mem
        pure ⟨T, wfrm⟩
      else
        .error s!"\tFromError:\n\t\table {name} not in Schema."
  | .alias frm as =>
    match checkFrom Γ T frm with
      | .ok ⟨T, wfrm⟩ => pure ⟨T, WellFormedFrom.alias as wfrm⟩
      | .error e => .error s!"\tFromError:\n{e}"
  | .implicitJoin frm₁ frm₂ => match checkFrom Γ T frm₁ with
      | .ok ⟨T₁, wfrm₁⟩ => match checkFrom Γ T frm₂ with
        | .ok ⟨T₂, wfrm₂⟩ => .ok ⟨T₁++T₂, WellFormedFrom.implicitJoin wfrm₁ wfrm₂⟩
        | .error e => .error s!"\tFromError:\n{e}"
      | .error e => .error s!"\tFromError:\n{e}"
  | .join _ frm₁ frm₂ prop => match checkFrom Γ T frm₁ with
    | .ok ⟨T₁, wfrm₁⟩ => match checkFrom Γ T frm₂ with
      | .ok ⟨T₂, wfrm₂⟩ => match checkWhere (T₁, T₂) prop with
        | .ok ⟨_, prp⟩ =>
            let wfrm := @WellFormedFrom.join _ Γ frm₁ T₁ frm₂ T₂ prop _ wfrm₁ wfrm₂
            pure ⟨_, wfrm prp⟩
        | .error e => .error s!"\tFromError:\n{e}"
      | .error e => .error s!"\tFromError:\n{e}"
    | .error e => .error s!"\tFromError:\n{e}"

-- Lean error location at actual location (withRef combinators as part of AST Nodes)
def check (Γ : Schema) : (t : Query) → (T : RelationType) → Except String (PLift (WellFormedQuery Γ t T))
  | ⟨sel, frm, whr⟩, T =>
    match getFromTable Γ frm with
      | .ok fromTable => match checkFrom Γ fromTable frm with
        | .ok ⟨Tf, wfrm⟩ => match checkSel Tf T sel with
          | .ok ⟨Ts, wsel⟩ => match checkWhere (T, Tf) whr with
            | .ok ⟨_, wwhr⟩ => do
              if heq : Ts = T then
                return PLift.up (.mk (Eq.subst heq wsel) wfrm wwhr)
              else
                .error s!"QueryError: Query type must match Select type."
            | .error e => .error s!"QueryError:\n{e}"
          | .error e => .error s!"QueryError:\n{e}"
        | .error e => .error s!"QueryError:\n{e}"
      | .error e => .error s!"QueryError:\n{e}"
