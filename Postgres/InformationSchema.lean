import Postgres.DSL.QueryAST

open QueryAST

namespace InformationSchema


def Schema.mk : List (String × List (String × DataType)) → Schema
  | l => l.map fun (name, l) => (name, l.map fun (id, t) => (id, name, t))

def schema : Schema :=
  Schema.mk [
    ("information_schema.tables", [
      ("table_catalog", .text),
      ("table_schema", .text),
      ("table_name", .text),
      ("table_name", .text),
    ])
  ]

end InformationSchema
