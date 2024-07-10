/-
Which types does the AST consist of?
What are the predicates of a type?
What is the context of a type?
-/

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
  deriving BEq

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
inductive WellFormedBexpr : RelationType × RelationType → Bexpr → Bool → Prop
  | not : WellFormedBexpr Γ b T → WellFormedBexpr Γ (.not b) T
  | bcmp : WellFormedBexpr Γ b₁ T₁ → WellFormedBexpr Γ b₂ T₂ → WellFormedBexpr Γ (.bcmp b₁ op b₂) T₃
  | acmp : WellFormedAexpr Γ b₁ T₁ → WellFormedAexpr Γ b₂ T₂ → WellFormedBexpr Γ (.acmp b₁ op b₂) T₃
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
  | alias        : From → (alias : String) → From
  | join         : Join → From → From → SQLProp → From
  | implicitJoin : From → From → From
  -- | nestedJoin   : Query → From

inductive WellFormedFrom : Schema → From → RelationType → Prop
  | table : (n : String) → (n, T) ∈ Γ → WellFormedFrom Γ (.table n) T
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
  deriving BEq

inductive WellFormedSelectField : RelationType → SelectField → Typ → Prop
  | col : (n : String) → (n, T) ∈ Γ → WellFormedSelectField Γ (.col n) T

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
inductive WellFormedSelect : RelationType → Select → RelationType → Prop
  | list d (ss : List SelectField) : ∀ sel : SelectField, ∀ sp : String × Typ, sel ∈ ss ∧ sp ∈ T → WellFormedSelectField tT sel sp.snd → (d = true → ss.eraseDups = ss) → WellFormedSelect Γ select T
  | all d : (d = false → ∀ e, e ∈ T → (_, e.snd) ∈ Γ) → (d = true → ∀ e, e ∈ T.eraseDups → (_, e.snd) ∈ Γ) → WellFormedSelect Γ s T

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

inductive WellFormedQuery : Schema → Query → RelationType → Prop
  | mk : WellFormedSelect Tf s Ts → WellFormedFrom Γ f Tf → WellFormedBexpr (Ts, Tf) b Tb → WellFormedQuery Γ ⟨s, f, b⟩ Ts
