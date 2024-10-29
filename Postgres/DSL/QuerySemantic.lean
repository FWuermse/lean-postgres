import Lean
import Postgres.DSL.QueryAST

open QueryAST Lean Lean.Syntax

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

-- TODO: replace with original count once Alloy is updated.
@[inline] def countP (p : α → Bool) (l : List α) : Nat := go l 0 where
  /-- Auxiliary for `countP`: `countP.go p l acc = countP p l + acc`. -/
  @[specialize] go : List α → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => bif p x then go xs (acc + 1) else go xs acc

/-! ### count -/

/-- `count a l` is the number of occurrences of `a` in `l`. -/
@[inline] def count [BEq α] (a : α) : List α → Nat := countP (· == a)

namespace QuerySemantic

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
    count (name, t, T) Γ = 1 →
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
    WellFormedExpression Γ rhs T →
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

inductive WellFormedSelectField : RelationType → SelectField → DataType → Prop
  | col :
    WellFormedExpression Γ e T →
    ----------------------------------
    WellFormedSelectField Γ (.col e stx) T
    -- Postgres doesn't support nested aliases such as 'a AS b, b AS c'
  | alias :
    WellFormedExpression Γ e T →
    ----------------------------------
    WellFormedSelectField Γ (.alias e a) T

inductive WellFormedSelect : RelationType → Select → RelationType → Prop
  | list (ss : List SelectField) :
    Forall (∃t, WellFormedSelectField Γ . t) ss →
    (T = ss.filterMap fun s => s.getTuple Γ) →
    ----------------------------------
    WellFormedSelect Γ (.list b ss stx) T
  | all :
    Γ = T →
    ----------------------------------
    WellFormedSelect Γ (.all b stx) T

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

@[simp]
def checkSelectField (Γ : RelationType) (s : SelectField) : Except (String × Syntax) (Σ' T, WellFormedSelectField Γ s T) := do
  match s with
  | .col e _ =>
    let ⟨T, h⟩ ← checkExpression Γ e
    pure ⟨T, WellFormedSelectField.col h⟩
  | .alias e _ =>
    let ⟨T, h⟩ ← checkExpression Γ e
    pure ⟨T, WellFormedSelectField.alias h⟩

def checkSel (Γ T : RelationType) (s : Select) : Except (String × Syntax) (Σ' T, WellFormedSelect Γ s T) :=
  match s with
  | .all _ stx =>
    if h : Γ = T then
      let wsel := WellFormedSelect.all h
      pure ⟨T, wsel⟩
    else
      .error (s!"The type T: {T} of `SELECT *` must match the FROM clause {Γ}.", stx)
  | .list _ ss stx => do
    let mut proofs := []
    for s in ss do
      if let .ok p := checkSelectField Γ s then
        proofs.insert p
      else
        .error ("", stx)

    sorry

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

end QuerySemantic
