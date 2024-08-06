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
  | field : name ∈ Γ.fst ∨ name ∈ Γ.snd → WellFormedAexpr Γ (.field n) Typ

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
inductive WellFormedBexpr : RelationType × RelationType → Bexpr → Bool → Prop
  | tt : WellFormedBexpr Γ .tt true
  | ff : WellFormedBexpr Γ .tt false
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
    WellFormedAexpr Γ b₁ T₁ →
    WellFormedAexpr Γ b₂ T₂ →
    ----------------------------------
    WellFormedBexpr Γ (.acmp b₁ op b₂) T₃
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
  | join         : Join → From → From → SQLProp → From
  | implicitJoin : From → From → From
  -- | nestedJoin   : Query → From

@[aesop unsafe 100% apply]
inductive WellFormedFrom : Schema → From → RelationType → Prop
  | table (n : String) : (n, T) ∈ Γ → WellFormedFrom Γ (.table n) T
  | alias : a → WellFormedFrom Γ f T → WellFormedFrom Γ f' T
  | join : WellFormedFrom Γ f₁ _ → WellFormedFrom Γ f₂ _ → WellFormedFrom Γ (.join j f₁ f₂ p) T
  | implicitJoin : WellFormedFrom Γ f₁ _ → WellFormedFrom Γ f₂ _ → WellFormedFrom Γ (.implicitJoin f₁ f₂) T

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

inductive WellFormedSelectField : RelationType → SelectField → Typ → Prop
  | col (n : String) : (n, T) ∈ Γ → WellFormedSelectField Γ (.col n) T

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
  --| list d (ss : List SelectField) : ∀ sel : SelectField, ∀ sp : String × Typ, sel ∈ ss ∧ sp ∈ T → WellFormedSelectField tT sel sp.snd → (d = true → ss.eraseDups = ss) → WellFormedSelect Γ select T
  | list d (ss : List SelectField) (sel : SelectField) (sp : String × Typ) :
    sel ∈ ss ∧ sp ∈ T →
    WellFormedSelectField tT sel sp.snd →
    (d = true → ss.eraseDups = ss) →
    ----------------------------------
    WellFormedSelect Γ select T
  | all d e :
    (d = false → e ∈ T → (_, e.snd) ∈ Γ) →
    (d = true → e ∈ T.eraseDups →
    (_, e.snd) ∈ Γ) →
    ----------------------------------
    WellFormedSelect Γ s T

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
    . intro _ c
      replace c : ("MyField", .bigInt) ∈ [("MyField", Typ.bigInt)] := by apply c
      apply c
    . intro _ c
      exact c
    . exact false
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

def checkFrom (Γ : Schema) (T : RelationType) : From → Option (Σ' T, WellFormedFrom Γ t T)
  | .table name =>
      if mem : (name, T) ∈ Γ then
        let wfrm := WellFormedFrom.table name mem
        pure ⟨T, wfrm⟩
      else
        .none
  | .alias frm as =>
    if let .some wfrm := checkFrom Γ T frm then
      let wfrm := WellFormedFrom.alias as wfrm.snd
      pure <| ⟨T, wfrm⟩
    else
      .none
  | .implicitJoin frm₁ frm₂ =>
    if let .some wfrm₁ := checkFrom Γ T frm₁ then
      if let .some wfrm₂ := checkFrom Γ T frm₂ then
        let wfrm := WellFormedFrom.implicitJoin wfrm₁.snd wfrm₂.snd
        pure <| ⟨T, wfrm⟩
      else
        .none
    else
      .none
  | .join j frm₁ frm₂ prop =>
    if let .some wfrm₁ := checkFrom Γ T frm₁ then
      if let .some wfrm₂ := checkFrom Γ T frm₂ then
        sorry
      else
        .none
    else
      .none

def checkSel (Γ : RelationType) (T : RelationType) : (s : Select) → Option (PLift (WellFormedSelect Γ s T))
  | .all d =>
    sorry
  | .list d ss =>
    sorry


-- Error monad (error, PLift..)
-- Lean error location at actual location (withRef combinators as part of AST Nodes)
def check (Γ : Schema) : (t : Query) → (T : RelationType) → Option (PLift (WellFormedQuery Γ t T))
  | .mk sel frm whr, T => do
    if let .some fromTable := getFromTable Γ frm then
      if let .some wfrm := checkFrom Γ fromTable frm then
        let wfrm := wfrm.snd
        if let .some wsel := checkSel T sorry sel then
          return PLift.up (.mk sorry wfrm sorry)
        else
          .none
      else
        .none
    else
      .none
