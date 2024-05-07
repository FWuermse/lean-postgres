import Postgres.Syntax.InsertDSL
import Postgres.Syntax.InsertSyntax

namespace SchemaDSL

inductive CreateScope where
  | default
  | local
  | global

inductive NotExistsClause where
  | notExists : NotExistsClause
  | empty : NotExistsClause

inductive CreateFields where
  | mk : List (String × Univ) → CreateFields

inductive SQLCreate where
  | mk : CreateScope → NotExistsClause → String → CreateFields → SQLCreate

def CreateScope.toString : CreateScope → String
  | .default => ""
  | .local => "LOCAL"
  | .global => "GOBAL"

instance : ToString CreateScope := ⟨CreateScope.toString⟩

def NotExistsClause.toString : NotExistsClause → String
  | notExists => "IF NOT EXISTS"
  | empty => ""

instance : ToString NotExistsClause :=
   ⟨NotExistsClause.toString⟩

def CreateFields.toString : CreateFields → String
  | mk l =>
    "(" ++ (", ".intercalate <| l.map (λ (lhs, rhs) => s!"{lhs} {rhs}")) ++ ")"

instance : ToString CreateFields :=
  ⟨CreateFields.toString⟩

def SQLCreate.toString : SQLCreate → String
  | mk scope notExistClause name fields => s!"CREATE {scope} TABLE {notExistClause} {name} {fields}"

instance : ToString SQLCreate :=
  ⟨SQLCreate.toString⟩

def x := toString <| SQLCreate.mk (CreateScope.default) .empty "myTable" (.mk [("test", Univ.char), ("id", Univ.nat)])
