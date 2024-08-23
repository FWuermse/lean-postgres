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
  deriving BEq, DecidableEq

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

abbrev RelationDataTypee := List (String × DataType)

abbrev Schema := List (String × RelationDataTypee)

/-
# Value

Following https://www.postgresql.org/docs/current/datatype.html
-/
inductive Value
  | null
  | integer (i : Int)
  | bigInt (i : Int)
  | bit (len : Nat) (stream : Array Bool)
  | varbit (len : Nat) (stream : Array Bool)
  | boolean (b : Bool)
  | char (len : Nat) (string : String)
  | varchar (len : Nat) (string : String)
  | date (year : Nat) (month : Fin 13) (year : Fin 32)
  | text (value : String)
  | double (d : Float)

inductive WellFormedValue : Value → DataType → Prop
  | null : WellFormedValue (.null) .null
  | integer : i < Int.ofNat 2^32 → i > -Int.ofNat 2^32 → WellFormedValue (.integer i) .integer
  | bigInt : i < Int.ofNat 2^64 → i > -Int.ofNat 2^64 → WellFormedValue (.bigInt i) .bigInt
  | bit : b.size = n → WellFormedValue (.bit n b) .bit
  | varbit : b.size ≤ n → WellFormedValue (.varbit n b) .varbit
  | boolean : WellFormedValue (.boolean b) .boolean
  | char : s.length = n → WellFormedValue (.char n s) .char
  | varchar : s.length ≤ n → WellFormedValue (.varchar n s) .varchar
  | date : m > 0 ∧ d > 0 → WellFormedValue (.date y m d) .date
  | text : WellFormedValue (.text s) .text
  | double : WellFormedValue (.double f) .double

/-
Following the conversion of:
  https://www.postgresql.org/docs/current/functions-math.html
  https://www.postgresql.org/docs/current/datatype-character.html
-/
inductive WellFormedNumConv : DataType → DataType → Prop
  | numeric :
    fst = .integer ∨ fst = .bigInt ∨ fst = .double →
    snd = .integer ∨ snd = .bigInt ∨ snd = .double →
    ----------------------------------
    WellFormedNumConv fst snd

inductive WellFormedCharConv : DataType → DataType → Prop
  | char :
    fst = .char ∨ fst = .varchar ∨ fst = .text →
    snd = .char ∨ snd = .varchar ∨ snd = .text →
    ----------------------------------
    WellFormedCharConv fst snd

inductive WellFormedIntConv : DataType → DataType → Prop
  | integral :
    fst = .integer ∨ fst = .bigInt →
    snd = .integer ∨ snd = .bigInt →
    ----------------------------------
    WellFormedIntConv fst snd

inductive WellFormedConv : DataType → DataType → Prop
  | numeric :
    WellFormedNumConv T₁ T₂ →
    WellFormedConv T₁ T₂
  | char :
    WellFormedCharConv T₁ T₂ →
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
  | bop .and => " AND "
  | bop .or => " OR "
  | acop .eq => " = "
  | acop .ne => " <> "
  | acop .lt => " < "
  | acop .le => " <= "
  | acop .ge => " > "
  | acop .gt => " >= "
  | aop .add => " + "
  | aop .sub => " - "
  | aop .div => " / "
  | aop .mul => " * "
  | aop .mod => " % "
  | uop .not => "NOT "
  | uop .add => "+"
  | uop .sub => "-"

instance : ToString Operator :=
  ⟨Operator.toString⟩

/-
# Value Expression

Following the grammar of https://www.postgresql.org/docs/current/sql-expressions.html

## DataTypee T
DataType

## Context Ctx
RelationDataTypee × RelationDataTypee (contents of From/Select clauses or both tables in case of joins)
-/
inductive Expression
  | value (l : Value)
  -- Skipping Column Ref (would compare a whole column on in comb with subscript)
  -- Skipping Positional Params
  -- Skipping subscripts (array access)
  | field (name : String)
  | cmp (lhs : Expression) (op : Operator) (rhs : Expression)
  | un (op : Operator) (expr : Expression)
  -- | function (name : String) (params : List Expression)

/-
# Expression Typing judgements
Following the comparison from:
  https://www.postgresql.org/docs/current/functions-comparison.html
  https://www.postgresql.org/docs/current/functions-datetime.html
-/
inductive WellFormedExpression : RelationDataTypee × RelationDataTypee → Expression → DataType → Prop
  | value v :
    WellFormedValue v T →
    ----------------------------------
    WellFormedExpression Γ (.value v) T
  | field :
    (s, T) ∈ Γ.fst ∨ (s, T) ∈ Γ.snd →
    ----------------------------------
    WellFormedExpression Γ (.field s) T
  -- Omitting aliasses like "on", "yes", "1"
  | tt : WellFormedExpression Γ (.value <| .boolean true) .boolean
  | ff : WellFormedExpression Γ (.value <| .boolean false) .boolean
  | not :
    WellFormedExpression Γ e .boolean →
    ----------------------------------
    WellFormedExpression Γ (.un (.uop .not) e) .boolean
  -- Bool not otherwise comparable (see: https://www.postgresql.org/docs/current/functions-logical.html)
  | bcmp :
    WellFormedExpression Γ lhs .boolean →
    WellFormedExpression Γ rhs .boolean →
    ----------------------------------
    WellFormedExpression Γ (.cmp lhs (.bop op) rhs) .boolean
  | acmp :
    WellFormedExpression Γ lhs T₁ →
    WellFormedExpression Γ rhs T₂ →
    WellFormedConv T₁ T₂ →
    ----------------------------------
    WellFormedExpression Γ (.cmp lhs (.acop op) rhs) .boolean
  | aexpr :
    WellFormedExpression Γ lhs T₁ →
    WellFormedExpression Γ rhs T₂ →
    WellFormedNumConv T₁ T₂ →
    ----------------------------------
    WellFormedExpression Γ (.cmp lhs (.aop op) rhs) .boolean
  | addSign :
    WellFormedExpression Γ e T →
    T = .integer ∨ T = .bigInt ∨ T = .double →
    ----------------------------------
    WellFormedExpression Γ (.un (.uop .add) e) .boolean
  | subSign :
    WellFormedExpression Γ e T₁ →
    WellFormedNumConv T₁ T₂ →
    ----------------------------------
    WellFormedExpression Γ (.un (.uop .sub) e) T₂
  -- Date ops are not symmetrical (see: https://www.postgresql.org/docs/current/functions-datetime.html)
  | dateadd :
    WellFormedExpression Γ lhs .date →
    WellFormedExpression Γ rhs T →
    T = .integer ∨ T = .bigInt ∨ T = .double →
    ----------------------------------
    WellFormedExpression Γ (.cmp lhs (.aop .add) rhs) .date
  | datesub :
    WellFormedExpression Γ lhs .date →
    WellFormedExpression Γ rhs T →
    T = .integer ∨ T = .bigInt ∨ T = .double →
    ----------------------------------
    WellFormedExpression Γ (.cmp lhs (.aop .sub) rhs) .date

/-
# SelectField

## DataTypee T
DataType

## Context Ctx
RelationDataTypee

## Predicates
(name, _) ∈ Ctx
-/
inductive SelectField
  | col   : String → SelectField
  | alias : String → String         → SelectField
  deriving BEq, DecidableEq
  -- SELECT f1, f1 as f1 from t WHERE f1 > 0
  -- f1 : Int
  -- f2 : String

def SelectField.name
  | col s => s
  | «alias» _ s => s

inductive WellFormedSelectField : RelationDataTypee → SelectField → DataType → Prop
  | col (n : String) :
    (n, T) ∈ Γ →
    WellFormedSelectField Γ (.col n) T
  | alias (n : String) :
    (n, T) ∈ Γ →
    WellFormedSelectField Γ (.alias a n) T

/-
# Select

## DataTypee T
RelationDataTypee

## Context Ctx
RelationDataTypee

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
inductive WellFormedSelect : RelationDataTypee → Select → RelationDataTypee → Prop
  | list (ss : List SelectField) :
    Forall (∃t, WellFormedSelectField Γ . t) ss →
    ----------------------------------
    WellFormedSelect Γ (.list b ss) T
  | all (h: ∀ x ∈ T, x ∈ Γ) :
    ----------------------------------
    WellFormedSelect Γ t T

mutual
/-
# From

## DataTypee T
RelationDataTypee

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
  | table        : (name : String) → From
  | alias        : From → (as : String) → From
  | join         : Join → From → From → BExpr → From
  | implicitJoin : From → From → From
  | nestedJoin   : Select → From → Where → From

/-
# Query

## DataTypee T
RelationDataTypee

## Context Ctx
Schema

## Predicates
WellDataTypeed Select in ctx
WellDataTypeed From in ctx
WellDataTypeed Where in ctx
-/
inductive Query where
  | mk : Select → From → BExpr → Query
end

@[aesop unsafe 100% apply]
inductive WellFormedFrom : Schema → From → RelationDataTypee → Prop
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
    WellFormedExpression (T₁, T₂) e .boolean →
    ----------------------------------
    WellFormedFrom Γ (.join j f₁ f₂ p) (T₁ ++ T₂)
  | implicitJoin :
    WellFormedFrom Γ f₁ T₁ →
    WellFormedFrom Γ f₂ T₂ →
    ----------------------------------
    WellFormedFrom Γ (.implicitJoin f₁ f₂) (T₁ ++ T₂)
  | nestedFrom :
    WellFormedSelect Tf s Ts →
    WellFormedFrom Γ f Tf →
    WellFormedExpression (Ts, Tf) e .boolean →
    ----------------------------------
    WellFormedFrom Γ (.nestedJoin s f e) Ts

@[aesop unsafe 100% apply]
inductive WellFormedQuery : Schema → Query → RelationDataTypee → Prop
  | mk :
    WellFormedSelect Tf s Ts →
    WellFormedFrom Γ f Tf →
    WellFormedExpression (Ts, Tf) e .boolean →
    ----------------------------------
    WellFormedQuery Γ ⟨s, f, w⟩ Ts

def getFromTable (Γ : Schema) : (t : From) → Except String RelationDataTypee
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
def checkSelectField (Γ : RelationDataTypee) (s : SelectField) (T : DataType) : Except String (Σ' T, WellFormedSelectField Γ s T) := match s with
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

-- (Maybe remove dicidable)
instance (Γ : RelationDataTypee) (T : DataType) : DecidablePred (fun s : SelectField => (checkSelectField Γ s T).isOk) :=
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

instance (Γ : RelationDataTypee) (s : SelectField) (T : DataType) : Decidable (∃T, WellFormedSelectField Γ s T) := match s with
  | .col name =>
    if h : (name, T) ∈ Γ then
      isTrue (by apply Exists.intro; apply WellFormedSelectField.col name h)
    else
      isFalse (sorry)
  | .alias a name =>
    if h : (name, T) ∈ Γ then
      isTrue (by apply Exists.intro; apply WellFormedSelectField.alias name h)
    else
      isFalse (sorry)

def checkSel (Γ T : RelationDataTypee) (s : Select) : Except String (Σ' T, WellFormedSelect Γ s T) := match s with
  | .all _ =>
    if h : ∀ x ∈ T, x ∈ Γ then
      let wsel := WellFormedSelect.all h
      pure ⟨T, wsel⟩
    else
      .error "The type of `SELECT *` must match the FROM clause."
  | .list _ ss =>
    if h : Forall (fun s : SelectField => ∃T, WellFormedSelectField Γ s T) ss then
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

def checkNumConv (fst : DataType) (snd : DataType) : Except String (Σ' T, WellFormedNumConv fst snd) :=
  if hfst : fst = DataType.integer ∨ fst = .bigInt ∨ fst = .double then
    if hsnd : snd = .integer ∨ snd = .bigInt ∨ snd = .double then
      pure ⟨.double, WellFormedNumConv.numeric hfst hsnd⟩
    else
      .error s!"Types are not comparable"
  else
    .error s!"Types are not comparable"

def checkExpression (Γ : RelationDataTypee × RelationDataTypee) (e : Expression) : Except String (Σ' T, WellFormedExpression Γ e T) := match e with
  | .value <| .boolean true => pure ⟨.boolean, .tt⟩
  | .value <| .boolean false => pure ⟨.boolean, .ff⟩
  | .value v => do
    let ⟨T, hv⟩ ← checkValue v
    pure ⟨T, .value v hv⟩
  | .field name =>
    let field := (Γ.fst.find? fun (n, _) => n == name).orElse fun _ => (Γ.snd.find? fun (n, _) => n == name)
    if let .some (_, t) := field then
      if h : (name, t) ∈ Γ.fst ∨ (name, t) ∈ Γ.snd then
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
  | .cmp bexpr₁ (.bop op) bexpr₂ => do
    let ⟨T₁, fst⟩ ← checkExpression Γ bexpr₁
    let ⟨T₂, snd⟩ ← checkExpression Γ bexpr₂
    if h₁ : T₁ = .boolean then
      if h₂ : T₂ = .boolean then
          pure ⟨.boolean, .bcmp (h₁ ▸ fst) (h₂ ▸ snd)⟩
      else
        .error s!"Operator {(Operator.bop op)} only supports boolean expressions on rhs."
    else
      .error s!"Operator {(Operator.bop op)} only supports boolean expressions on lhs."
  | .cmp aexpr₁ (.acop op) aexpr₂ => do
    let ⟨a₁, fst⟩ ← checkExpression Γ aexpr₁
    let ⟨a₂, snd⟩ ← checkExpression Γ aexpr₂
    if h : a₂ = a₁ then
      return ⟨.integer, .acmp fst (h ▸ snd)⟩
    else
      .error "Only expressions of a comparable type can be compared."

mutual
def checkFrom (Γ : Schema) (T : RelationDataTypee) (t : From) : Except String (Σ' T, WellFormedFrom Γ t T) := match t with
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
    let wqry ← checkQuery Γ q T
    pure ⟨T, .nestedFrom wqry.down⟩

def checkQuery (Γ : Schema) : (t : Query) → (T : RelationDataTypee) → Except String (PLift (WellFormedQuery Γ t T))
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
