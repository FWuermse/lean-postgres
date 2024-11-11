#import "./template.typ": *
#import "./theme.typ": *
#import "./ast.typ": *
#import "./typing-judgements.typ": *
#import "@preview/dashy-todo:0.0.1": todo
#import "@preview/glossarium:0.5.1": make-glossary, register-glossary, print-glossary, gls, glspl
#show: make-glossary
#let entry-list = (
  (
    key: "bnf",
    short: "BNF",
    long: "Backus-Naur form",
    description: "A notation used to describe the syntax of programming languages or other formal languages."
  ),
  (
    key: "adt",
    short: "ADT",
    long: "Algebraic data type",
    description: "A kind of composite type, i.e., a type formed by combining other types."
  ),
  (
    key: "sql",
    short: "SQL",
    long: "Structured Query Language",
    description: "A domain-specific language used to manage data, especially in a relational database management system (RDBMS)."
  ),
  (
    key: "ast",
    short: "AST",
    long: "Abstract Syntax Tree",
    description: "An abstract syntax tree (AST) is a data structure used in computer science to represent the structure of a program or code snippet."
  ),
  (
    key: "ffi",
    short: "FFI",
    long: "Foreign Function Interface",
    description: "A foreign function interface is a mechanism by which a program written in one programming language can call routines or make use of services written or compiled in another one."
  ),
  (
    key: "dsl",
    short: "DSL",
    long: "domain-specific language",
    description: "A domain-specific language is a computer language specialized to a particular application domain."
  ),
  (
    key: "orm",
    short: "ORM",
    long: "Object-relational mapping",
    description: "Object-relational mapping in computer science is a programming technique for converting data between a relational database and the memory (usually the heap) of an object-oriented programming language."
  )
  // Add more terms
)
#register-glossary(entry-list)

#let title = "A Type-Safe Deep Embedding of SQL in Lean"
#let author = "Florian Würmseer"

#show: official.with(
  title: title,
  author: author,
  thesis-type: "Master Praktikum",
  submission_date: datetime.today().display(),
  matriculation: "12760815",
  advisor: "Jannis Limperg",
  supervisor: "Prof. Dr. Jasmin Blanchette"
)

#set page(numbering : "1")

#counter(page).update(1)
= Introduction <Introduction>

The integration of #gls("sql") into programming languages has been a long-standing
challenge in both industry and academia due to the inherent differences between
set-based, declarative query languages like #gls("sql") and imperative, object-oriented
programming languages. Despite #gls("sql")'s dominance in interacting with relational
databases, the way developers interact with it in most applications can be
inefficient, error-prone, and cumbersome @sql-errors. This is primarily due to way #gls("sql") as a #gls("dsl") is represented in general-purpose programming languages and how it is passed to the database. Representing queries as a plain string and passing it to a database directly is dangerous because it can lead to #gls("sql") injection attacks @sqlinject.

More sophisticated approaches like #glspl("orm") require users to write classes for every table in a database schema and produce an excessive amount of boilerplate code to link tables and generate methods for all possible queries  @ormpaper. Both approaches do not detect incorrect queries such as invalid type conversion from text to integer at compile-time. The error in this query ```sql SELECT * FROM myTable WHERE "1" < 3``` for instance will only be detected after it is already sent to the database in existing #gls("orm") libraries. Another challenge with #gls("sql") embeddings in most general-purpose programming languages is the limited support for injecting custom syntax. Java for instance only uses strings or query-like syntax to mimic the #gls("dsl") e.g.: ```Java findUserByStatusAndName(...)``` instead of ```sql SELECT * FROM User WHERE User.status = ... AND User.name = ...``` @ormpaper.

Currently, there is no support for #gls("sql") query generation and validation in Lean 4 with respect to the database schema used. We want to drive the forefront of Lean's general-purpose programming with a strong link to Lean's type system and proof assistant capabilities. Our goal is to express, validate, and execute a query of the PostgreSQL dialect in Lean 4.

The below example query represents a valid query that returns all names aliased as `nickname` from a customer table where the condition matches, i.e. the id of a customer equals one and the field `birthdate` is before January 1 2000. This query is valid under the assumption that the database schema we operate on contains a table named `customer` with the fields `id`, `name`, and `birthdate` of the types `integer`, `varchar 255`, and `date`. Our library should accept such a query (using the original #gls("sql") query syntax) and provide a formal proof that this query is correct according to our embedding at compile-time.

#align(center)[#box(```sql
SELECT customer.name AS nickname, customer.birthdate
FROM customer
WHERE customer.id = 1 AND customer.birthdate < 2000-01-01
```)]

The second example below represents an invalid query that is inconsistent with our embedding regarding  the same schema as the first example. The fields we selected below (`mame` and `birthday`) are misspelled and thus do not occur in the customer table in our schema and the comparison of the `name` (which has type `varchar 255` in our schema) is invalid for a right-hand side of type `date`. Such mistakes should be rejected by our implementation and marked as invalid so that they cannot be sent to a database until they are corrected and a proof of correctness is generated. To give users more information about the reason and location of an error in a query we want to mark the syntax red and provide meaningful error messages upon hovering over the marked location. 

#let uwt(myText) = {
    underline(stroke: (paint: red, thickness: 1pt, dash: "densely-dashed"), offset: 1pt, [
        #myText
    ],)
}

#align(center)[#box(
align(left)[```sql SELECT``` #uwt(```sql customer.mame```) ```sql AS nickname,``` #uwt(```sql customer.birthday```) #linebreak()
```sql FROM customer ```#linebreak()
```sql WHERE customer.id = 1 AND customer.name``` #uwt(```sql <```) ```sql 2000-01-01```
])
]

As a theoretical foundation for a successful implementation, we propose a design that lets us deeply embed a fraction of the syntax and semantics of PostgreSQL queries into Lean 4 as a way to generate #gls("sql") queries and correctness proofs only if the query is valid for a given database schema description. Our design proposal is based on our interpretation of the official Postgres documentation and source code @pq @pqgh but is not peer-reviewed or extensively tested.

This paper only considers the current Postgres version 17 and is limited to the most relevant eleven of the 43 data types (`null`, `integer`, `bigInt`, `bit`, `varbit`, `boolean`, `char`, `varchar`, `date`, `text`, `double`). The remaining excluded types mostly relate to geometric structures and nested #glspl("dsl") such as XML or JSON. Furthermore, we only support a subset of operators in expressions (logical operators, comparison operators, mathematical operators, string operators). Functions and array operators are excluded. Lastly, the `SELECT` clause only consists of fields and aliases and does not support arbitrary expressions. This means that we support queries selecting fields (e.g.: ```sql SELECT a, b, c, ...```), aliases (e.g.: ```sql SELECT a AS A, b AS B, c AS C, ...```), and (```sql SELECT * ...```) but no arbitrary expressions (e.g.: ```sql SELECT 1 + 2/1 < 4 ...```)

With this implementation, we extend the existing Lean 4 Postgres library and thus commit to the PostgreSQL dialect @psql. Before this effort, the library consisted of a toy implementation of the Postgres protocol for connecting to the database leveraging sockets. The library did not support typed queries prior to this paper.

= Design <Design>

We needed three components to deeply embed the PostgreSQL #gls("dsl") efficiently  and accurately in Lean (other than just using plain Strings). The first component is the syntax itself in the form of Lean 4 syntax categories which we could directly use from the Postgres documentation @pq. The second component was a data structure (#gls("ast")) which holds the information of a query in a way that is more convenient than reiterating over Lean `Syntax` objects in every function. Finally, we needed a hierarchy of rules in the form of propositions that reference our generated #gls("ast"). Those propositions are important for generating proofs and validating the abstract syntax. Without those proofs and propositions, we would allow invalid queries, that are possible in the syntax from Postgres' documentation and our unrestricted #gls("ast"). For instance, a query that selects fields from a table that is not in the schema or not even in a `FROM` clause (e.g.: ```sql SELECT y.name FROM x```).

Our procedure for fully embedding a query and proving its correctness during compile-time starts with a Lean 4 elaborator that parses the syntax into our #gls("ast"). Before this syntax is accepted and handed over to the Lean compiler we run a function to check whether the given parsed query is well-formed in respect to its schema. To determine whether a query is well-formed we will define a type system that represents a query and its type in the context of a database schema.

#pagebreak()

The well-formed query ```sql SELECT * FROM customer``` of a given type T and a given Schema $Gamma$ for instance, will be treated the following by the procedure:
+ Parse query into an internal representation (`{select: all, from: (table "customer"), expr: (value (boolean TRUE))}`) 
+ Invoke `check` function with query representation, T, and $Gamma$
+ `check` generates a formal proof of the correct representation
+ Query is fully elaborated
+ Elaborated query type checks and can be used in the library and sent to a database

The following subsections reveal our approach to typing a query, explain the #gls("ast") we designed, and introduce a type system that we can reason about.

== Typing an SQL Query <Typing>

We must define a type T and context $Gamma$ for queries as the basis for the type system we present. This is important because a query can have different types depending on the schema. For instance the query ```sql SELECT a.b FROM a``` could return numbers in a schema where the field `a` is an integer, strings when it ss a `varchar` or even fail if the schema has no table called `b` and field `a`. Before we define the type of an entire query however, we have to break it down into its `SELECT`, `FROM`, and `WHERE` clauses representing the according parts in a query (```sql SELECT ... FROM ... WHERE ...```). Those sub-parts of a query depend on each other and shape the type we expect an entire query to have. Our approach to typing follows the related literature closely @paper4 @pq @pqgh @psql.

We typed expressions of a `WHERE` clause in the context of the corresponding `FROM` clause because it can reference fields from within the `FROM` clause. An expression ```sql WHERE customer.id = 1``` requires the information about whether a customer table is in the scope of a query, has a field `id`, and that the `id`s type is something that compares with `1`. We will continue referring to this type as relation type because it describes the signature of a relation in a relational database. Expressions in Postgres are flexible #todo[Duplicate with section in Design type system (CAST)] so that even expressions of type `boolean` can be transformed back to numbers and used in further comparisons or arithmetics. So giving an expression the type `boolean` is not sufficient. Instead, the type of an expression must be an arbitrary data type.

The type of a `FROM` clause must represent what tables are selected and which fields are available for an expression. Thus, we typed `FROM` clauses with a relation type. The context of the `FROM` clause is the database schema consisting of all available tables, the individual table names, and their fields. In our Lean implementation, this type is represented by a list of tuples (string $times$ relation type).

Similar to expressions, the `SELECT` clause of a query must also have the context of its `FROM` clause and the type is also a relation type. The query itself has the entire schema as context and the same relation type as its `SELECT` clause. @typetable summarizes the types and contexts for a query and its components. Let's consider a minimal example with a schema consisting of only one table called `a` with one field `id` of type integer. When we break down a query (```sql SELECT a.id AS ID FROM a WHERE a.id = 1```) into its components we end up with the following contexts and types denoted as `<context>` $tack$ `<term>` $:$ `<type>`:

```lean4
[("a", [("id", integer)])] ⊢ SELECT a.id AS ID FROM a WHERE a.id = 1 : [("ID", integer)]
[("a", [("id", integer)])] ⊢ FROM a                                  : [("id", integer)]
[("id", integer)]           ⊢ SELECT a.id AS A                       : [("ID", integer)]
[("id", integer)]           ⊢ WHERE a.id = 1                         :            boolean
```

#align(center)[
    #figure(box(table(
      columns: (auto, auto, auto),
      align: horizon,
      table.header([*Term*], [*Context*], [*Type*]),
      [`WHERE`], [relation type of `FROM` clause], [data type],
      [`SELECT`], [relation type of `FROM` clause], [relation type],
      [`FROM`], [database schema], [relation type],
      [Query], [database schema], [relation type],
    )), caption: [Types and contexts of a query.]) <typetable>
  ]

== AST <AST>

The official Postgres documentation @pq yields a basic structure of the abstract syntax for the Postgres #gls("sql") dialect. We designed the Lean data types closely aligned to the documentation, omitting some features (see @Introduction). @primitive, @operators, and @query-structure represent the #gls("ast") used in this library as #glspl("adt"). All types supported in this library shown in @primitive follow the PSQL specification @pq[pp. 148-221]. The official Postgres documentation separates operators only by boolean and non-boolean operators @pq[pp. 221-244]. To allow for more efficient pattern matching and simpler code, we decided to group the operators further into the categories unary, arithmetic, and comparison shown in @operators.

The category `DataType` is simply an enumeration of our supported types. The `Value` category represents values in an expression e.g. a boolean of `FALSE` (```sql SELECT ... WHERE FALSE```). The `Join` category represents the different join operators when we want to select from multiple tables (e.g. ```sql SELECT * FROM table_a INNER JOIN table_b```). All other operators can only appear in expressions of a `WHERE` clause or nested `FROM` (e.g. ```sql SELECT ... WHERE NOT 1 + 2 < 3 AND -(1 - 2) = 1```). Expressions can be values, field references or operators on other expressions. The `SelectField` can be a column reference of a table or an aliased column reference. The first string refers to the name of a column and the second of the table in the current context. The third argument of `alias` is the alternative name. The `Select` type can be all (`SELECT * ...`) or an arbitrary selection of fields. The `Bool` argument represents the `DISTINCT` keyword in #gls("sql") stating whether duplicate rows should be eliminated in a query result. The `From` type holds information about what tables are referenced and how they are joined. The `Query` type consists of a `Select`, `From`, and `Expr` type. 

#figure(
  grid(
    columns: 2,
    gutter: 5mm,
    dataType,
    value),
  kind: image,
  caption: [DataType and Value.]) <primitive>

#figure(
  grid(
    columns: 3,
    gutter: 5mm,
    joinType,
    boolBinOp,
    aExprCmpOp,
    aExprOp,
    unaryOp,
    operator),
  kind: image,
  caption: [Operators]) <operators>

#figure(grid(columns: 2, gutter: 5mm, expression, selectField, select, from, query),
  kind: image, caption: [Query structure.]) <query-structure>

== Type System <Semantic>

As for the #gls("ast"), the semantics of the Postgres #gls("sql") could be extracted from official documentation and C implementation @pq @pqgh. To ensure precise and correct typing, we aligned the contexts and types mentioned in @Typing with the #gls("ast"). Thus, the `SELECT` clause is represented by the well-formed `Select` and well-formed `SelectField` predicates. Furthermore, we need a separate set of rules for well-formed type conversions according to the documentation @pq.

We defined a typing judgement for values of each of the supported data types (see @Introduction) in @value-type. All terms in those rules (structure `<term> : <type>`) refer to a `Value` constructor of our #gls("ast"). Each judgment consists of a conclusion and may contain a condition on the value range. Integers for instance are limited to the range of values they support which is $-2^32$ until $2^32$ for 32-bit integers. Its context only holds the name of a value and its type, which is a shallow embedding of common types in functional and dependently typed programming languages e.g.: $NN$, Fin, String. The #smallcaps[Date] rule consists of restrictions for the day and month to be non-negative Fin types and could be further restricted to match the days available for each individual month @calendar. Most other types are just restricted by their size specified in the documentation @pq[pp. 148-221]. 

#figure(
  align(center)[
    #box(inset: 8%, proof-tree(tj-bigint))
    #box(inset: 8%, proof-tree(tj-bit))
    #box(inset: 8%, proof-tree(tj-boolean))
    #box(inset: 8%, proof-tree(tj-char))
    #box(inset: 8%, proof-tree(tj-date))
    #box(inset: 8%, proof-tree(tj-double))
    #box(inset: 8%, proof-tree(tj-integer))
    #box(inset: 8%, proof-tree(tj-null))
    #box(inset: 8%, proof-tree(tj-text))
    #box(inset: 8%, proof-tree(tj-varbit))
    #box(inset: 8%, proof-tree(tj-varchar))
    #block()
  ],
  kind: image,
  caption: [Typing judgments for Values.]) <value-type>

The second set of rules represents the type conversions as specified in the documentation #cite(<pq>, supplement: [pp. 156-157]) #cite(<pq>, supplement: [pp. 226-282]). Those rules require no context and the type T represents a data type. The documentation also mentions default types for constants and coercion #cite(<pq>, supplement: "pp. 39-40"). With the limited types supported, it was feasible to specify all conversions for instance: integer $->$ bigInt, bigInt $->$ double and integer $->$ double and a symmetry rule in @type-conv. Upon supporting more data types, the integer $->$ double rule shall be replaced by a rule for transitive transitions. Similar to the operator grouping in @AST, the separation of numeric, character, and date conversions simplifies further rules for expressions. The date rules are special in Postgres as they allow for addition and subtraction with integers. This operation only works with integers and is not symmetric @pq[p. 227]. Therefore, both are represented as separate judgments. Similarly, string concatenation can only infer the left-hand side argument @pq[p. 234].

#figure(
  align(center)[
    #box(inset: 8%, proof-tree(tj-eqd))
    #box(inset: 8%, proof-tree(tj-intbigint))
    #box(inset: 8%, proof-tree(tj-bigintdouble))
    #box(inset: 8%, proof-tree(tj-intdouble))
    #box(inset: 8%, proof-tree(tj-symmd))
    #box(inset: 8%, proof-tree(tj-charc))
    #box(inset: 8%, proof-tree(tj-cvc))
    #box(inset: 8%, proof-tree(tj-vctx))
    #box(inset: 8%, proof-tree(tj-ctx))
    #box(inset: 8%, proof-tree(tj-symmc))
    #box(inset: 8%, proof-tree(tj-numeric))
    #box(inset: 8%, proof-tree(tj-charcc))
    #box(inset: 8%, proof-tree(tj-eqc))
    #block()
  ],
  kind: image,
  caption: [Typing judgments for type conversions.]
) <type-conv>

We decided not to differentiate between arithmetic and boolean expressions for a more extensible set of rules considering functions we want to support in the future such as the `CAST()` function that can convert between boolean and number types. 

@expression contains our typing rules for expressions mentioned in Postgres' documentation @pq[pp. 222-248] @pq[pp. 277-294]. Each expression is of a data type T and is defined in a context $Gamma$ that represents a relation type. The terms (`<context> ⊢ <term> : <type>`) in the expression rules (if not explicitly annotated like Value v) refer to an `Expr` constructor seen of our #gls("ast"). $Gamma$ can be a table in the database schema or a modified table that arises from joining or aliasing tables. The most basic rules are `VALUE` and `FIELD`. The `VALUE` rule only requires any well-formed value from @value-type. The `FIELD` rule is well-formed with type T under the condition that a field with that type exists in the context. The three supported unary operators `NOT`, `+`, and `-` require a compatible well-formed expression. Binary expressions including boolean or arithmetic comparisons and arithmetic expressions require two well-formed expressions of matching type. If the type of the two expressions in the premise is not specified we require a well-formed type conversion @type-conv.

#figure(
  align(center)[
    #box(inset: 8%, proof-tree(tj-field))
    #box(inset: 8%, proof-tree(tj-value))
    #box(inset: 8%, proof-tree(tj-not))
    #box(inset: 8%, proof-tree(tj-bcmp))
    #box(inset: 8%, proof-tree(tj-acmp))
    #box(inset: 8%, proof-tree(tj-aexpr))
    #box(inset: 8%, proof-tree(tj-concat))
    #box(inset: 8%, proof-tree(tj-pos))
    #box(inset: 8%, proof-tree(tj-neg))
    #box(inset: 8%, proof-tree(tj-dateadd))
    #box(inset: 8%, proof-tree(tj-datesub))
    #block()
  ],
  kind: image,
  caption: [Typing judgments for expression.]
) <expression>

A `SELECT` clause may either mirror the current context (relation type of its `FROM` clause) in which case it is well-formed if T matches $Gamma$ or consists of references of fields in the `FROM` clause. The term (`<context> ⊢ <term> : <type>`) in the #smallcaps[Col] and #smallcaps[Alias] rules refers to a `SelectField` constructor in our #gls("ast") and the term in the #smallcaps[List] and #smallcaps[All] rules to a `Select` constructor. The boolean b of the #smallcaps[All] rule in @select can be chosen arbitrarily between `True` and `False` in our embedding as it limits the results of a query and not its type (see ```sql DISTINCT``` in @AST).

#figure(
  align(center)[
    #box(inset: 8%, proof-tree(tj-col))
    #box(inset: 8%, proof-tree(tj-alias))
    #box(inset: 8%, proof-tree(tj-list))
    #box(inset: 8%, proof-tree(tj-all))
    #block()
  ],
  kind: image,
  caption: [Typing judgments for select.]
) <select>

All rules for a well-formed `FROM` clause in @from operate directly on the database schema $Gamma$ and build the basis for the `SELECT` and `WHERE` clauses of a query. The terms (`<context> ⊢ <term> : <type>`) in the `From` rules (if not explicitly annotated like `Expr e`) refer to a `From` constructor in the #gls("ast"). The simplest rule is #smallcaps[Table] which merely requires the table to exist in a list. The rules #smallcaps[Alias], #smallcaps[Join], #smallcaps[Implicitjoin], and #smallcaps[Nestedjoin] require a previous well-formed `FROM` clauses and therefore always extend/modify the relation type of a table that is defined in the current database schema. The #smallcaps[Nestedjoin] rule repeats the requirements for a `SELECT`, `FROM`, and `WHERE` clause instead of leveraging the #smallcaps[Query] rule in @query. We made this design choice to avoid cyclic dependencies between the definitions of the `From` and `Query` types and thus, work around mutual inductive types in our implementation. In essence, mutual inductive types are supported by Lean 4 but they currently have some restrictions. 

#figure(
  align(center)[
    #box(inset: 8%, proof-tree(tj-table))
    #box(inset: 8%, proof-tree(tj-aliass))
    #box(inset: 8%, proof-tree(tj-join))
    #box(inset: 8%, proof-tree(tj-implicitjoin))
    #box(inset: 8%, proof-tree(tj-nestedjoin))
    #block()
  ],
  kind: image,
  caption: [Typing judgments for `FROM`.]
) <from>

The last typing judgement is the #smallcaps[Query] rule in @query. It requires that all parts of an SQL query are well-formed individually and links the according contexts and types. It is important to note that the context of the `SELECT` clause is the type of the `FROM` clause of a query. The context of the `FROM` clause represents the schema and is also the context of the entire query. The type of the `SELECT` clause is also the type of the entire query. The term `s f e` refers to the only constructor available for the `Query` type in our #gls("ast").

#figure(proof-tree(tj-query), kind: image, caption: [Typing judgement for query.]) <query>

= Implementation

With the extensive support for inductive types and the elaborator that extends Lean's syntax during compile-time by providing a parser framework, we could easily embed the SQL syntax by just stating the PostgreSQL grammar rules as syntax categories. For the deep embedding of our type system, we used the concept of inductive predicates in Lean that allowed us to translate the typing rules easily. To prove that the query and its parts are well-formed, we implemented a type checker that generates proofs for a given term (the inductive types seen in @AST) and its type in the context of a schema.

For better maintainability, we delegated type-checking from the elaborator to a separate function. This causes the separation of the error location and syntax. To attach error messages to the correct location in the elaborated syntax (e.g. the outdated table reference employee that was replaced by the alias AS in ```sql SELECT``` #underline(stroke: (paint: red, thickness: 1pt, dash: "densely-dashed"), offset: 2pt, [```sql employee.id```],) ```sql FROM employee ``` ```sql AS b, customer ```), we extended the #gls("ast") by a parsed Lean Syntax reference (one extra field of type Syntax per constructor). We retrieved this information again from the AST upon hitting type-checking errors. @ex1 demonstrates a small subset of our implementation based on the #gls("ast") and typing rules below:

#pagebreak()
#align(center)[
  #box(inset: 8%, proof-tree(tj-table))
  #box(inset: 8%, proof-tree(tj-join))
]

The inductive type `From` in the code represents a fraction of the #gls("ast") from @AST and the inductive predicate `WFFrom`, the two predicates defined in @Semantic. The `checkFrom` is invoked by the `check` function mentioned in @Introduction and makes recursive calls where necessary. Both proofs returned in `checkFrom` can be produced by applying the typing rules and the hypothesis created by the if statements. The propositions `h` and `(name, T) ∈ Γ` implement the Lean type class `Decidable` and can therefore be proven by the `decide` tactic. Upon failure of the check, we return an error and do not attempt to prove that a query is invalid. The return type of the `checkFrom` function includes Lean's type of dependent pairs and can return a proof for a proposition as well as an argument used in this proof.

#example([type checker for `From`])[
  #align(left)[
```lean
inductive From
  | table : String → From
  | join : Join → From → From → Expr → From
  ...
```
```lean
inductive WFFrom : Schema → From → RelationType → Prop
  | table : (name, T) ∈ Γ → WFFrom Γ (.table name stx) T
  | join : WFFrom Γ f₁ T₁ →
    WFFrom Γ f₂ T₂ →
    WFExpression (T₁ ++ T₂) e .boolean →
    WFFrom Γ (.join j f₁ f₂ e stx) (T₁ ++ T₂)
  ...
```
```lean
def checkFrom (Γ : Schema) (T : RelationType) (t : From) : Except (String × Syntax) (Σ' T, WellFormedFrom Γ t T) :=
  match t with
  | .table name stx =>
    if mem : (name, T) ∈ Γ then
      let wfrm := .table mem
      pure ⟨T, wfrm⟩
    else
      .error (s!"Table {name} : {T} not in Schema {Γ}.", stx)
  | .join _ frm₁ frm₂ e stx => do
    let ⟨T₁, wfrm₁⟩ ← checkFrom Γ (← getFromTable Γ frm₁) frm₁
    let ⟨T₂, wfrm₂⟩ ← checkFrom Γ (← getFromTable Γ frm₂) frm₂
    let expr ← checkExpression (T₁ ++ T₂) e
    let wfrm := WellFormedFrom.join wfrm₁ wfrm₂
    if h : expr.fst = .boolean then
      pure ⟨T₁ ++ T₂, wfrm (h ▸ expr.snd)⟩
    else
      .error ("Where clauses can only contain boolean expressions.", stx)
  ...
```
]] <ex2>

In addition to designing and implementing the deep embedding of the fraction of PostgreSQL, we also implemented an interface to interact with actual Postgres database instances in Lean. There are two feasible ways of connecting to databases in Lean 4. The first option is to use a socket library to send TCP packages to the database following the Postgres protocol. This is currently very limited though because cryptographic libraries are still immature in Lean 4. The other option is to use a #gls("ffi"). Following the #gls("ffi") approach we were able to interface with the C library `libPQ` and translate between Lean and C objects. This allowed us to leverage more of the essential features of Postgres e.g. password encryption using scram-sha-256 or advanced options in prepared statements.

= Related Work

As #gls("sql") is considered the most widely used database description language for relational databases @sql-widely-used, most programming libraries and papers that introduce a formal embedding of query languages focus on the general #gls("sql") language and cover the basic operations that work across all dialects @chai @paper1 @paper3. Other papers focus on formalizing relational algebra @paper2 @paper4 and provide a translation to #gls("sql"). While those libraries do not support the same features, they offered valuable core ideas on typing queries in relation to a database schema @paper2 @paper1 @paper3 in @Design.

Before designing the type-checking procedure for our library, we attempted a different approach by embedding the typing rules into an intrinsically typed #gls("ast"). @ex2 shows an example of this previous approach in contrast to @ex1. The #gls("ast") in @ex2 depends on a relation type and carries the proof `h` with a so-called auto param. Auto params are default values for arguments in Lean constructors that can be overwritten when invoking the constructor. Because the type of the constructor arguments named `h` are propositions, the value satisfying it must be a proof. The first proposition can be proven by the `decide` tactic and the other by the `simp` tactic. Note that even other #gls("ast")-elements such as the expression have to be dependently typed in this approach.

Those arguments are a substantial part of their polymorphic and dependent types and will remain during computation, allocating more memory for the entire #gls("ast"). @ex2 does not store extra arguments on the #gls("ast") type (`From`) but comes with an inductive predicate of the form `Schema → From → RelationType → Prop`. Propositions live in Sort 0 in the Lean type system and are thus stripped off after type-checking. This means that the schema overhead is removed during run time and unlike the first approach, will not require additional memory. The other reason we did not proceed with the intrinsically typed #gls("ast") is that it introduced more complexity to the elaborator functions and was less modular. Separating the proof (in the `check` function), #gls("ast"), and error-message-generation kept the code more structured and made changes and new features easier to implement.

#figure([
  ```lean
  inductive From : RelationType → Type
    | table (Γ) : (name : String) → (h: (name, α) ∈ Γ := by decide) → From α
    | join : SQLJoin → From α → From β → Expr T → (h: γ = α ++ β ∧ T = boolean := by simp) → From γ
    ...
  ```
]) <ex1>

= Conclusion

We proposed a new way to statically validate SQL queries against a database schema and embed the #gls("dsl") directly in the syntax of Lean 4. We stated a deep embedding of a query regarding its schema and stated typing rules reflecting the type system used in the Postgres documentation and implementation @pq @pqgh. To address the limitations of the scope set in @Introduction, future research should focus on supporting arbitrary expressions in the `SelectField` clauses, full type inference for the type checker such that types do not have to be provided for a top-level query, and support for all functions such as `count()`, `abs()`, `ceil()` @pq[pp. 221-435] etc. Arbitrary expressions in a select field can be trivially achieved by modifying the typing rules COL and ALIAS in @select and the according fields `col` and `alias` in the #gls("ast") by using an expression instead of name and table. The proofs in the type checker however will become more verbose due to the need from rule induction over well-formed expressions. 

#pagebreak()

#bibliography("refs.bib", full: true, title: "References")

#print-glossary(
  entry-list,
)