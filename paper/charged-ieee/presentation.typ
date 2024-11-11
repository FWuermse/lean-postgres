#import "@preview/polylux:0.3.1": *
#import "theme.typ" : *
#import "./template.typ": *
#import "./typing-judgements.typ": *
#import "./ast.typ": *

#show: lmu-theme.with()

#set text(font: "Fira Sans", weight: "light", size: 20pt)
#set par(justify: true)

#title-slide(
  author: [Florian Würmseer],
  title: "Formal Schema-Based SQL Embedding",
  date: datetime.today().display(),
  extra: "Praktikum Presentation",
)

#slide(title: "Table of contents")[
  #lmu-outline
]

#new-section-slide("Introduction")
#slide(title: [Concept of "Einzelpraktikum"])[
  - Initiated by student
  - Module P1 or P2 in current SPO
  - 6 - 12 ECTS
  #pause
  - Regular practical tasks
  - Presentation
  - Short paper
]

#slide(title: "Research Objective and Scope")[
  - Identify a formal embedding of PostgreSQL
  - Compare two approaches of embedding semantics considering schema
    - Proofs as constructor arguments
    - SQL as TT
  - Ability to interact with running Postgres DB instances
  - SQL syntax embedding in Leans Elaborator
  #pause
  - Only 11 DataTypes supported
  - Support for SQL functions and array operators excluded
  - Undefined behaviour e.G.: ```sql TRUE < TRUE OR TRUE``` not allowed
]

#new-section-slide("Design")

#slide(title: "AST-Structure")[
  #align([
    #box(proof-tree(dataType))
    #box(proof-tree(value))
    #box(proof-tree(joinType))
    #box(proof-tree(boolBinOp))
  ])
]

#slide(title: "AST-Structure")[
  #align([
    #box(proof-tree(aExprCmpOp))
    #box(proof-tree(aExprOp))
    #box(proof-tree(unaryOp))
    #box(proof-tree(operator))
    #box(proof-tree(expression))
  ])
]

#slide(title: "AST-Structure")[
  #align([
    #box(proof-tree(selectField))
    #box(proof-tree(select))
    #box(proof-tree(from))
    #box(proof-tree(query))
  ])
]

#slide(title: "Contexts and Types")[
  #align(box(inset: 15%, [RelationType := List (String $times$ String $times$ DataType)]), center)
  #align(box(inset: 15%, [Schema := List (String $times$ RelationType)]), center)
  #align(center)[
    #box(table(
      columns: (auto, auto, auto),
      align: horizon,
      table.header([*ADT-Reference*], [*Context*], [*Type*]),
      [Value], [reuse Leans context (shallow embedding)], [DataType],
      [Expr], [RelationType of FROM clause], [DataType],
      [SelectField], [RelationType of FROM clause], [DataType],
      [Select], [RelationType of FROM clause], [RelationType],
      [From], [Schema], [RelationType],
      [Query], [Schema], [RelationType],
    ))
  ]
]

#slide(title: "Type System")[
#align(
  [
    #box(inset: 15%, proof-tree(tj-varchar))
    #box(inset: 15%, proof-tree(tj-boolean))
    #box(inset: 15%, proof-tree(tj-integer))
    #box(inset: 15%, proof-tree(tj-bit))
  ],
  center
) #align(center)[$dots$]
]

#slide(title: "Type System")[
#align(
  [
    #box(inset: 15%, proof-tree(tj-intbigint))
    #box(inset: 15%, proof-tree(tj-bigintdouble))
    #box(inset: 15%, proof-tree(tj-intdouble))
    #box(inset: 15%, proof-tree(tj-eqd))
    #box(inset: 15%, proof-tree(tj-symmd))
  ],
  center
) #align(center)[$dots$]
]

#slide(title: "Type System")[
#align(
  [
    #box(inset: 8%, proof-tree(tj-value))
    #box(inset: 8%, proof-tree(tj-field))
    #box(inset: 8%, proof-tree(tj-bcmp))
    #box(inset: 8%, proof-tree(tj-aexpr))
  ],
  center
) #align(center)[$dots$]
]

#slide(title: "Type System")[
#align(box(inset: 8%, [toTuple : RelationType $->$ SelectField $->$ String $times$ String $times$ DataType]), center)
#align(
  [
    #box(inset: 15%, proof-tree(tj-col))
    #box(inset: 15%, proof-tree(tj-alias))
    #box(inset: 15%, proof-tree(tj-list))
    #box(inset: 15%, proof-tree(tj-all))
  ],
  center
)
]

#slide(title: "Type System")[
#align(
  [
    #box(inset: 15%, proof-tree(tj-table))
    #box(inset: 15%, proof-tree(tj-aliass))
    #box(inset: 15%, proof-tree(tj-join))
    #box(inset: 15%, proof-tree(tj-implicitjoin))
    #box(inset: 15%, proof-tree(tj-nestedjoin))
    #box(inset: 15%, proof-tree(tj-query))
  ],
  center
)
]

#new-section-slide("Implementation")

#slide(title: "Extended AST approach")[
  ```lean
inductive From : RelationType → Type
  | table (Γ) : 
    (name : String) →
    (h: (name, α) ∈ Γ := by decide) →
    From α
  | join :
    SQLJoin →
    From α →
    From β → Expr T →
    (h: γ = α ++ β ∧ T = boolean := by simp) →
    From γ
  ```
]

#slide(title: "Type checker approach")[
  #align(center)[
    #box(inset: 15%,
```lean
inductive From
  | table → String → From
  | join : Join → From → From → Expr → From
```
    )
    #box(inset: 15%,
```lean
inductive WFFrom : Schema → From → RelationType → Prop
  | table : (name, T) ∈ Γ → WFFrom Γ (.table name stx) T
  | join : WFFrom Γ f₁ T₁ →
    WFFrom Γ f₂ T₂ →
    WFExpression (T₁ ++ T₂) e .boolean →
    WFFrom Γ (.join j f₁ f₂ e stx) (T₁ ++ T₂)
```
    )
    #box(
      ```lean
      def checkFrom (Γ : Schema) (T : RelationType) (t : From) :
        Except (String × Syntax) (Σ' T, WellFormedFrom Γ t T)
      ```
    )
  ]
]

#slide(title: "FFIs")[
  $dots$
  ```C
  const int *paramLengths = lean_sarray_cptr(parameterLengths);
  const int *paramFormats = lean_sarray_cptr(parameterLengths);
  printf("number; %d\n", nParams);
  char **values = malloc(sizeof(void*)*nParams);
  for (int i = 0; i < nParams; i++) {
    char* current = lean_string_cstr(objects[i]);
    values[i] = current;
    printf("%s\n", current);
  }
  res = PQexecParams(conn, qry, nParams, *type, values, *len, *format, resultFormat);
  free(values);
  return lean_io_result_mk_ok(to_lean<Result>(res));
  ```
]

#slide(title: "Challenges")[
  - Translation from Lean to C types in FFIs
  - Invokation of type checker in Lean `TermElabM`
  - Error highlighting location in Queries such as:

    ```sql SELECT``` #underline(stroke: (paint: red, thickness: 2pt, dash: "densely-dashed"), offset: 2pt, [```sql employee.id```],)
    ```sql FROM employee ```
    ```sql AS b, customer ```
]


#new-section-slide("Conclusion")
#slide(title: "Conclusion")[
  - Embedding possible, scope can easily be extended
  - Type theory approach more scalable
  - Sticking closely with dialect and documentation is important
]

#slide(title: "Personal Learning and Impression")[
  - Deeper understanding of the purpose of inductive predicates in Lean
  - Clearer picture of Lean metaprogramming (TermElab, Lean AST, Env...)
  - Understanding the importance of interactive proofs
  - Deepening of most concepts from ITP
  - FUN! (not fun)
]