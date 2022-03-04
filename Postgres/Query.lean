import Socket
import Lean
import Postgres.Postgres

open Socket Connect Lean Lean.Elab.Term

namespace Query

inductive Col where
  | as : String → String → Col
  | col : String → Col

instance : ToString Col where
  toString col := match col with
    | Col.col str => str
    | Col.as s1 s2 => s1 ++ " AS " ++ s2

inductive Tbl where
  | alias : String → String → Tbl
  | tbl : String → Tbl

instance : ToString Tbl where
  toString col := match col with
    | Tbl.tbl str => str
    | Tbl.alias s1 s2 => s1 ++ " " ++ s2

inductive FieldDesc where
  | distinct : List Col → FieldDesc
  | on : List Col → FieldDesc

def foldToString {α : Type u} [ToString α] : α → String → String
  | y, "" => toString y
  | y, x => x ++ ", " ++ toString y

instance : ToString FieldDesc where
  toString fieldDesc := match fieldDesc with
    | FieldDesc.distinct cols => "DISTINCT " ++ List.foldr foldToString "" cols
    | FieldDesc.on cols => List.foldr foldToString "" cols

inductive Select where
  | all
  | cols : FieldDesc → Select

instance : ToString Select where
  toString select := match select with
    | Select.all => "*"
    | Select.cols fd => toString fd

inductive BinOp where
  | and
  | or

instance : ToString BinOp where
  toString binOp := match binOp with
    | BinOp.and => "AND"
    | BinOp.or => "OR"

structure Expres where
  bool : Bool

instance : ToString Expres where
  toString expres := toString expres.bool

inductive Pred where
  | expr : Expres → Pred
  | binOp : Expres → BinOp → Pred

instance : ToString Pred where
  toString pred := match pred with
    | Pred.expr e => toString e
    | Pred.binOp e b => toString e ++ toString b

structure Whr where
  pred : Pred

instance : ToString Whr where
  toString whr := toString whr.pred

structure Query where
  select : Select
  frm : List Tbl
  /--
  TODO:
  whr : Option Whr := none
  groupBy : Option String := none
  having : Option String := none
  limit : Option String := none -/

instance : ToString Query where
  toString q := s!"SELECT {q.select} FROM {List.foldr foldToString "" q.frm};"

declare_syntax_cat col
syntax str : col
syntax str "AS" str : col

declare_syntax_cat tbl
syntax str : tbl
syntax str str : tbl

declare_syntax_cat field_desc
syntax "DISTINCT"? (col),+ : field_desc
syntax (col),+ : field_desc

declare_syntax_cat select
syntax "*" : select
syntax field_desc : select

declare_syntax_cat bin_op
syntax "AND" : bin_op
syntax "OR" : bin_op

declare_syntax_cat expr
syntax "TRUE" : expr
syntax "FALSE" : expr

declare_syntax_cat frm
syntax (tbl),+ : frm

declare_syntax_cat pred
syntax expr : pred
syntax expr bin_op : pred

declare_syntax_cat whr
syntax pred : whr

declare_syntax_cat query
syntax "SELECT" select "FROM" frm ("WHERE" whr)? : query

syntax (name := sql) query ";" : term

def synToString (stx : Syntax) : String :=
  match stx.getSubstring? with
  -- TODO: Address error case
    | none => "ERROR Processing Query!!! Alarm"
    | some x => (toString x).replace "\"" ""

def toCol (stx : Syntax) : Expr :=
  match stx.asNode.getKind with
    | `Query.col_AS_ => mkApp2 (mkConst `Query.Col.as) (mkStrLit $ synToString stx[0][0]) (mkStrLit $ synToString stx[2][0])
    | `Query.col_ => mkApp (mkConst `Query.Col.col) (mkStrLit $ synToString stx[0][0])
    | _ => mkStrLit ""

def toTbl (stx : Syntax) : Expr :=
  match stx.asNode.getKind with
    | `Query.tbl__ => mkApp2 (mkConst `Query.Tbl.alias) (mkStrLit $ synToString stx[0][0]) (mkStrLit $ synToString stx[1][0])
    | `Query.tbl_ => mkApp (mkConst `Query.Tbl.tbl) (mkStrLit $ synToString stx[0][0])
    | _ => mkStrLit ""

def filterArg (s : Syntax) : Bool :=
  match synToString s with
    | ", " => false
    | "" => false
    | _ => true

def mkExprList (stx : Syntax) (transform : Syntax → Expr) (type : Expr) : MetaM Expr := do
  let s := stx.asNode.getArgs.filter filterArg
  -- map columns to Expr
  let cols := Array.toList $ s.map transform
  -- transform List Expr into Expr
  Meta.mkListLit type cols

def mkSelect (stx : Syntax) : MetaM Expr := do
  do match stx.asNode.getKind with
    | `Query.«select*» => pure $ mkConst `Query.Select.all
    | `Query.select_ => match stx[0].asNode.getKind with
      | `Query.field_descDISTINCT_ => pure $ mkApp (Lean.mkConst `Query.Select.cols) $ mkApp (Lean.mkConst `Query.FieldDesc.distinct) (← mkExprList stx[0][1] toCol (mkConst `Query.Col))
      | `Query.field_desc_ => pure $ mkApp (Lean.mkConst `Query.Select.cols) $ mkApp (mkConst `Query.FieldDesc.on) (← mkExprList stx[0][0] toCol (mkConst `Query.Col))
      | _ => throwError "Failed to parse Select paramseters"
    | _ => pure $ mkStrLit "Failed to parse Select"

def mkFrm (stx : Syntax) : MetaM Expr :=
  mkExprList stx[0] toTbl (mkConst `Query.Tbl)

@[termElab sql] def queryImpl : TermElab := λ stx expectedType? => do
  do match stx.asNode.getArgs with
    | #[q, _] => match q.asNode.getArgs with
      | #[_, s, _, f, w?] => match w?.getHead? with
        | none => pure $ mkApp2 (mkConst `Query.Query.mk) (← mkSelect s) (← mkFrm f)
        | some w => mkSelect s
      | _ => throwError "Failed to parse Query"
    | _ => throwError "Failed to parse"

def sendQuery (socket : Socket) (query : Query) : IO ByteArray := do
  let req ← socket.send $ toByteArray $ RegularMessage.mk 'Q' (toString query)
  let x ← socket.recv 5
  -- TODO: parse response
  pure $ ← socket.recv 1000

end Query
