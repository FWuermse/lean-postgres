import Postgres.Syntax.InsertDSL
import Postgres.Syntax.SchemaDSL
import Lean

open InsertDSL
open SchemaDSL
open Lean Elab Meta

namespace SchemaSyntax

declare_syntax_cat                  createScope
syntax "LOCAL"                    : createScope
syntax "GLOBAL"                   : createScope

declare_syntax_cat                  notExistsClause
syntax "IF NOT EXISTS"            : notExistsClause

declare_syntax_cat                  insertType
syntax "Char"                     : insertType
syntax "Num"                      : insertType
syntax "Varchar(" num ")"         : insertType
syntax "Date"                     : insertType

declare_syntax_cat                  fieldDesc
syntax "(" (ident insertType),+ ")" :  fieldDesc

syntax (name := create) "CREATE " (createScope)? " TABLE " (notExistsClause)? ident fieldDesc : term

def mkStrOfIdent (id : Syntax) : Expr :=
  mkStrLit id.getId.toString

def elabCreateScope : TSyntax `createScope → TermElabM Expr
  | `(createScope|LOCAL) => pure <| mkConst ``CreateScope.local
  | `(createScope|GLOBAL) => pure <| mkConst ``CreateScope.global
  | _ => throwUnsupportedSyntax

def elabSQLType : TSyntax `insertType → TermElabM Expr
  | `(insertType|Char) => pure <| mkConst ``Univ.char
  | `(insertType|Num) => pure <| mkConst ``Univ.nat
  | `(insertType|Varchar($n:num)) => pure <| mkApp (mkConst ``Univ.varchar) (mkNatLit n.getNat)
  | `(insertType|Date) => pure <| mkConst ``Univ.date
  | _ => throwUnsupportedSyntax

def mkProd := (mkApp2 (mkConst ``Prod [0, 0]) (mkConst `String) (mkConst `Univ))

def elabFieldDesc : TSyntax `fieldDesc → TermElabM Expr
  | `(fieldDesc|($[$id:ident $typ:insertType],*)) => do
    let ids := id.map (mkStrOfIdent .)
    let typs ← typ.mapM (elabSQLType .)
    let zipped := Array.zip ids typs
    let prod := zipped.map (fun (x, y) => mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``Univ) x y)
    let list := prod.foldl (fun init x => (mkApp2 (mkApp (mkConst ``List.cons [0]) mkProd) x init)) (mkApp (mkConst `List.nil [0]) mkProd)
    pure <| mkApp (mkConst ``CreateFields.mk) list
  | _ => throwUnsupportedSyntax

@[term_elab create] def elabQuery : Term.TermElab := fun stx _ =>
  match stx with
  | `(create| CREATE TABLE $id:ident $fd:fieldDesc) => do
    pure <| mkApp4 (mkConst ``SQLCreate.mk) (mkConst ``CreateScope.global) (mkConst ``NotExistsClause.empty) (mkStrOfIdent id) (← elabFieldDesc fd)
  | `(create| CREATE $scope:createScope TABLE $id:ident $fd:fieldDesc) => do
    pure <| mkApp4 (mkConst ``SQLCreate.mk) (← elabCreateScope scope) (mkConst ``NotExistsClause.empty) (mkStrOfIdent id) (← elabFieldDesc fd)
  | `(create| CREATE TABLE $_:notExistsClause $id:ident $fd:fieldDesc) => do
    pure <| mkApp4 (mkConst ``SQLCreate.mk) (mkConst ``CreateScope.global) (mkConst ``NotExistsClause.notExists) (mkStrOfIdent id) (← elabFieldDesc fd)
  | `(create| CREATE $scope:createScope TABLE $_:notExistsClause $id:ident $fd:fieldDesc) => do
    pure <| mkApp4 (mkConst ``SQLCreate.mk) (← elabCreateScope scope) (mkConst ``NotExistsClause.notExists) (mkStrOfIdent id) (← elabFieldDesc fd)
  | _ => throwUnsupportedSyntax
