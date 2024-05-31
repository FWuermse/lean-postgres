import Postgres.Schema.DeleteDSL
import Postgres.Schema.QuerySyntax

open DeleteDSL
open QuerySyntax

open Lean Elab Meta

namespace DeleteSyntax

declare_syntax_cat          deleteFrom
syntax ident              : deleteFrom
syntax ident " AS " ident : deleteFrom

syntax (name := delete) "DELETE FROM " deleteFrom (" WHERE " prop)? : term

def mkStrOfIdent (id : Syntax) : Expr :=
  mkStrLit id.getId.toString

def elabDeleteFrom : TSyntax `deleteFrom → TermElabM Expr
  | `(deleteFrom|$id:ident) => pure <| mkApp (mkConst ``DeleteFrom.table) (mkStrOfIdent id)
  | `(deleteFrom|$id:ident AS $tag:ident) => pure <|mkApp2 (mkConst ``DeleteFrom.alias) (mkStrOfIdent id) (mkStrOfIdent tag)
  | _ => throwUnsupportedSyntax

@[term_elab delete] def deleteQuery : Term.TermElab := fun stx _ =>
  match stx with
  | `(delete|DELETE FROM $df:deleteFrom WHERE $p:prop) => do
    pure <| mkApp2 (mkConst ``SQLDelete.mk) (← elabDeleteFrom df) (← elabProp p)
  | `(delete|DELETE FROM $df:deleteFrom) => do
    pure <| mkApp2 (mkConst ``SQLDelete.mk) (← elabDeleteFrom df) (mkConst ``SQLProp.tt)
  | _ => throwUnsupportedSyntax
