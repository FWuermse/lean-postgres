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

inductive ExistsClause where
  | exists : ExistsClause
  | empty : ExistsClause

inductive CreateFields where
  | mk : List (String × Univ) → CreateFields

inductive SQLCreate where
  | mk : CreateScope → NotExistsClause → String → CreateFields → SQLCreate

inductive SQLDrop where
  | mk : ExistsClause → List String → SQLDrop

def CreateScope.toString : CreateScope → String
  | .default => ""
  | .local => "LOCAL"
  | .global => "GOBAL"

instance : ToString CreateScope := ⟨CreateScope.toString⟩

def NotExistsClause.toString : NotExistsClause → String
  | .notExists => "IF NOT EXISTS"
  | .empty => ""

def ExistsClause.toString : ExistsClause → String
  | .exists => "IF EXISTS"
  | .empty => ""

instance : ToString NotExistsClause :=
  ⟨NotExistsClause.toString⟩

instance : ToString ExistsClause :=
  ⟨ExistsClause.toString⟩

def CreateFields.toString : CreateFields → String
  | mk l =>
    "(" ++ (", ".intercalate <| l.map (λ (lhs, rhs) => s!"{lhs} {rhs}")) ++ ")"

instance : ToString CreateFields :=
  ⟨CreateFields.toString⟩

def SQLCreate.toString : SQLCreate → String
  | mk scope notExistClause name fields => s!"CREATE {scope} TABLE {notExistClause} {name} {fields}"

instance : ToString SQLCreate :=
  ⟨SQLCreate.toString⟩
