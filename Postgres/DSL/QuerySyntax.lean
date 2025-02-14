import Lean
import Postgres.DSL.QueryAST
import Postgres.DSL.QuerySemantic

open Lean Elab Meta Term QueryAST QuerySemantic

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

syntax (name := pgquery) "pquery(" ident " |- " sqlQuery (" ∶ " term)? ")" : term

partial def elabValue (stx : TSyntax `value) : TermElabM Expr := do
  let expr := match stx with
    -- defaults to integer (see https://www.postgresql.org/docs/7.3/datatype.html)
  | `(value|$v:num) => return mkApp2 (mkConst ``Value.integer) (mkApp (mkConst ``Int.ofNat) (mkNatLit v.getNat)) (← quoteAutoTactic stx)
  | `(value|$v:scientific) => return mkApp2 (mkConst ``Value.double) (← Term.elabScientificLit v (mkConst `Float)) (← quoteAutoTactic stx)
    -- Defaults to text: (see https://www.postgresql.org/docs/current/datatype-character.html)
  | `(value|$v:str) => return mkApp3 (mkConst ``Value.varchar) (mkNatLit 255) (mkStrLit v.getString) (← quoteAutoTactic stx)
  | `(value|NULL) => return mkApp (Lean.mkConst ``Value.null) (← quoteAutoTactic stx)
  | `(value|($v:value)) => elabValue v
  | _ => throwUnsupportedSyntax
  -- TODO: Include remaining types
  expr

def elabOp : TSyntax `op → TermElabM Expr
  | `(op|=)  => return mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.eq)
  | `(op|<>) => return mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.ne)
  | `(op|!=) => return mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.ne)
  | `(op|<)  => return mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.lt)
  | `(op|<=) => return mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.le)
  | `(op|>)  => return mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.gt)
  | `(op|>=) => return mkApp (mkConst ``Operator.acop) (mkConst ``AExprCmpOp.ge)
  | `(op|+) => return mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.add)
  | `(op|-) => return mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.sub)
  | `(op|/) => return mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.div)
  | `(op|*) => return mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.mul)
  | `(op|%) => return mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.mod)
  | `(op|||) => return mkApp (mkConst ``Operator.aop) (mkConst ``AExprOp.con)
  | _                => throwUnsupportedSyntax

-- Can be optimized by checking in the branches rather than at the end
partial def elabExpression (stx : TSyntax `expr) : TermElabM Expr := do
  let sExpr ← quoteAutoTactic stx
  match stx with
  | `(expr|$v:value) => return mkApp2 (mkConst ``Expression.value) (← elabValue v) sExpr
  | `(expr|$id:ident) =>
    match id.getId with
    | .str fst snd => return mkApp3 (mkConst ``Expression.field) (mkStrLit snd) (mkStrLit fst.toString) sExpr
    | _ => throwUnsupportedSyntax
  | `(expr|+ $ae:expr) => return mkApp3 (mkConst ``Expression.un) (mkConst ``UnaryOp.add) (← elabExpression ae) sExpr
  | `(expr|- $ae:expr) => return mkApp3 (mkConst ``Expression.un) (mkConst ``UnaryOp.sub) (← elabExpression ae) sExpr
  | `(expr|$be₁:expr AND $be₂:expr) => do
    let be₁ ← elabExpression be₁
    let be₂ ← elabExpression be₂
    return mkApp4 (mkConst ``Expression.bin) be₁ (mkApp (mkConst ``Operator.bop) (mkConst ``BoolBinOp.and)) be₂ sExpr
  | `(expr|$be₁:expr OR $be₂:expr) => do
    let be₁ ← elabExpression be₁
    let be₂ ← elabExpression be₂
    return mkApp4 (mkConst ``Expression.bin) be₁ (mkApp (mkConst ``Operator.bop) (mkConst ``BoolBinOp.or)) be₂ sExpr
  | `(expr|$ae₁:expr $ps:op $ae₂:expr) => do
    let ae₁ ← elabExpression ae₁
    let ae₂ ← elabExpression ae₂
    let op ← elabOp ps
    let stx ← quoteAutoTactic stx
    return mkApp4 (mkConst ``Expression.bin) ae₁ op ae₂ stx
  | `(expr|($be:expr)) => elabExpression be
  | `(expr|TRUE) => return mkApp2 (mkConst ``Expression.value) (mkApp2 (mkConst ``Value.boolean) (mkConst ``true) sExpr) sExpr
  | `(expr|FALSE) => return mkApp2 (mkConst ``Expression.value) (mkApp2 (mkConst ``Value.boolean) (mkConst ``false) sExpr) sExpr
  | `(expr|NOT $be:expr) => return mkApp3 (mkConst ``Expression.un) (mkConst ``UnaryOp.not) (← elabExpression be) sExpr
  | s => throwError s

def elabSelectField (stx : TSyntax `selectField) : TermElabM Expr :=
  match stx with
  | `(selectField|$field:ident) =>
    match field.getId with
    | .str fst snd => do
      let sExpr ← quoteAutoTactic stx
      return mkApp3 (mkConst ``SelectField.col) (mkStrLit snd) (mkStrLit fst.toString) sExpr
    | _ => throwUnsupportedSyntax
  | `(selectField|$field:ident AS $as:ident) =>
    match field.getId with
    | .str fst snd =>
      let fieldName := snd
      let tableName := fst.toString
      let «alias» := as.getId.toString
      return mkApp3 (mkConst ``SelectField.alias) (mkStrLit fieldName) (mkStrLit tableName) (mkStrLit «alias»)
    | _ => throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

def elabSelect (stx : TSyntax `sqlSelect) : TermElabM Expr := do
  let sExpr ← quoteAutoTactic stx
  match stx with
  | `(sqlSelect|*) => return mkApp2 (mkConst ``Select.all) (mkConst ``Bool.false) sExpr
  | `(sqlSelect|DISTINCT *) => return mkApp2 (mkConst ``Select.all) (mkConst ``Bool.true) sExpr
  | `(sqlSelect|$cs:selectField,*) => do
    let exprs ← cs.getElems.toList.mapM elabSelectField
    let cols ← mkListLit (mkConst ``SelectField) exprs
    return mkApp3 (mkConst ``Select.list) (mkConst ``Bool.false) cols sExpr
  | `(sqlSelect|DISTINCT $cs:selectField,*) => do
    let exprs ← cs.getElems.toList.mapM elabSelectField
    let cols ← mkListLit (mkConst ``SelectField) exprs
    return mkApp3 (mkConst ``Select.list) (mkConst ``Bool.true) cols sExpr
  | _ => throwUnsupportedSyntax

def elabJoin (stx : TSyntax `join) : TermElabM Expr := do
  let sExpr ← quoteAutoTactic stx
  match stx with
  | `(join|INNER) => return mkApp (mkConst ``Join.inner) sExpr
  | `(join|LEFT)  => return mkApp (mkConst ``Join.left) sExpr
  | `(join|RIGHT) => return mkApp (mkConst ``Join.right) sExpr
  | `(join|OUTER) => return mkApp (mkConst ``Join.outer) sExpr
  | _             => throwUnsupportedSyntax

partial def elabFrom (stx : TSyntax `sqlFrom) : TermElabM Expr := do
  let sExpr ← quoteAutoTactic stx
  match stx with
  | `(sqlFrom|$t:ident) => return mkApp2 (mkConst ``From.table) (mkStrLit t.getId.toString) sExpr
  | `(sqlFrom|$f:sqlFrom AS $t:ident) =>
    return mkApp3  (mkConst ``From.alias) (← elabFrom f) (mkStrLit t.getId.toString) sExpr
  | `(sqlFrom|$l:sqlFrom, $r:sqlFrom) => do
    let l ← elabFrom l
    let r ← elabFrom r
    return mkApp3 (mkConst ``From.implicitJoin) l r sExpr
  | `(sqlFrom|$l:sqlFrom $j:join JOIN $r:sqlFrom ON $p:expr) => do
    let l ← elabFrom l
    let r ← elabFrom r
    let j ← elabJoin j
    let p ← elabExpression p
    return mkApp5 (mkConst ``From.join) j l r p sExpr
  | `(sqlFrom|($f:sqlFrom))           => elabFrom f
  | `(sqlFrom| (SELECT $sel:sqlSelect FROM $frm:sqlFrom $[WHERE $expr]?) AS $id:ident) => do
    let sel ← elabSelect sel
    let frm ← elabFrom frm
    let whr ← match expr with
    | none => pure <| mkApp2 (mkConst ``Expression.value) (mkApp2 (mkConst ``Value.boolean) (mkConst ``true) sExpr) sExpr
    | some expr => elabExpression expr
    let al := id.getId.toString
    return mkApp5 (mkConst ``From.nestedJoin) sel frm whr (mkStrLit al) sExpr
  | _ => throwUnsupportedSyntax

def elabQuery (stx : TSyntax `sqlQuery) : TermElabM Expr := do
  let sExpr ← quoteAutoTactic stx
  match stx with
  | `(sqlQuery| SELECT $sel FROM $frm:sqlFrom $[WHERE $expr]?) => do
    let frm ← elabFrom frm
    let whr ← match expr with
    | none => pure <| mkApp2  (mkConst ``Expression.value) (mkApp2 (mkConst ``Value.boolean) (mkConst ``true) sExpr) sExpr
    | some expr => elabExpression expr
    let sel ← elabSelect sel
    return mkApp4 (mkConst ``Query.mk) sel frm whr sExpr
  | _ => throwUnsupportedSyntax

def checkQuery! (Γ : Schema) (t : Query) (T : RelationType) : Except (String × Syntax) RelationType :=
  match checkQuery Γ t T with
  | .ok rt => .ok rt.fst
  | .error e => .error e

def checkQueryInf! (Γ : Schema) (t : Query) : Except (String × Syntax) RelationType :=
  match checkQuery Γ t .none with
  | .ok rt => .ok rt.fst
  | .error e => .error e

namespace QuerySyntax

elab_rules : term
  | `(pgquery| pquery( $id |- $query ∶ $relation )) => do
    let env ← getEnv
    if let .some s := env.find? id.getId then
      let query ← elabQuery query
      let checked ← elabAppArgs (mkConst ``checkQuery!) #[] #[Arg.expr s.value!, Arg.expr query, Arg.stx relation] .none (explicit := false) (ellipsis := false)
      let qAST ← unsafe evalExpr (Except (String × Syntax) RelationType) (.app (.app (.const `Except [0, 0]) (.app (.app (.const `Prod [0, 0]) (.const `String [])) (.const `Lean.Syntax []))) (.const ``QueryAST.RelationType [])) checked
      let stx ← getRef
      match qAST with
      | .ok _ => pure query
      | .error (e, estx) =>
        match stx.find? (. == estx) with
        | .some estx => throwErrorAt estx e
        | .none => throwError "Error location Syntax {estx} in AST not in currently elaborated Syntax {stx}."
    else
      throwUnsupportedSyntax
  | `(pgquery| pquery( $id |- $query )) => do
    let env ← getEnv
    if let .some s := env.find? id.getId then
      let query ← elabQuery query
      let checked ← elabAppArgs (mkConst ``checkQueryInf!) #[] #[Arg.expr s.value!, Arg.expr query] .none (explicit := false) (ellipsis := false)
      let qAST ← unsafe evalExpr (Except (String × Syntax) RelationType) (.app (.app (.const `Except [0, 0]) (.app (.app (.const `Prod [0, 0]) (.const `String [])) (.const `Lean.Syntax []))) (.const ``QueryAST.RelationType [])) checked
      let stx ← getRef
      match qAST with
      | .ok _ => pure query
      | .error (e, estx) =>
        match stx.find? (. == estx) with
        | .some estx => throwErrorAt estx e
        | .none => throwError "Error location Syntax {estx} in AST not in currently elaborated Syntax {stx}."
    else
      throwUnsupportedSyntax

end QuerySyntax
