/-
Which types has the AST?
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

inductive Join
  | inner | left | right | outer

/-
# Aexpr

## Type T
Typ

## Context Ctx
(List (String × Typ)) × (List (String × Typ))
Ctx.fst represents the projections aka aliasing, Ctx.snd the result of a from clause

## Predicates
field: name ∈ Ctx.fst ∨ name ∈ Ctx.snd
-/
inductive Aexpr
  | value : Typ → Aexpr
  | field : (name: String) × Typ → Aexpr

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
(List (String × Typ)) × (List (String × Typ))

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

/-
# From

## Type T
List (String × Typ)

## Context Ctx
List (String × List (String × Typ))

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
  | nestedJoin   : Query → From

/-
# SelectField

## Type T
Typ

## Context Ctx
List (String × Typ)

## Predicates
(name, _) ∈ Ctx
-/
inductive SelectField
  | col   : (name : String) → SelectField
  | alias : (name : String) → String         → SelectField

/-
# Select

## Type T
List (String × Typ)

## Context Ctx
List (String × List (String × Typ))

## Predicates
list: distrinct → ∀ s ∈ List SelectFields, WellFormedSelectField
all: (_, T) ∈ Ctx
-/
inductive Select
  | list : (distinct: Bool) → List SelectField → Select
  | all  : (distinct: Bool) → Select

/-
# Query

## Type T
List (String × Typ)

## Context Ctx
List (String × List (String × Typ))

## Predicates
WellTyped Select in ctx
WellTyped From in ctx
WellTyped Where in ctx
-/
structure Query where
  select   : Select
  «from»   : From
  «where»  : Bexpr
