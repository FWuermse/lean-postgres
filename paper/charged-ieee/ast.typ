#import "@preview/simplebnf:0.1.1": *
#let dataType = bnf(
  Prod(
    $"d"$,
    delim: $=$,
    annot: $sans("DataType")$,
    {
      Or[null][]
      Or[integer][]
      Or[bigInt][]
      Or[bit][]
      Or[varbit][]
      Or[boolean][]
      Or[char][]
      Or[varchar][]
      Or[date][]
      Or[text][]
      Or[double][]
    },
  ),
)

#let value = bnf(
  Prod(
    $"v"$,
    delim: $=$,
    annot: $sans("Value")$,
    {
      Or[null][]
      Or[integer][Int]
      Or[bigInt][Int]
      Or[bit][Nat (Array Bool)]
      Or[varbit][Nat (Array Bool)]
      Or[boolean][Bool]
      Or[char][Char]
      Or[varchar][Nat String]
      Or[date][Nat (Fin 13) (Fin 32)]
      Or[text][String]
      Or[double][Float]
    },
  ),
)

#let joinType = bnf(
  Prod(
    $"j"$,
    delim: $=$,
    annot: $sans("Join")$,
    {
      Or[inner][]
      Or[left][]
      Or[right][]
      Or[outer][]
    },
  ),
)

#let boolBinOp = bnf(
  Prod(
    $"bop"$,
    delim: $=$,
    annot: $sans("BoolBinOp")$,
    {
      Or[and][]
      Or[or][]
    },
  ),
)

#let aExprCmpOp = bnf(
  Prod(
    $"cmp"$,
    delim: $=$,
    annot: $sans("AExprCmpOp")$,
    {
      Or[eq][]
      Or[ne][]
      Or[lt][]
      Or[le][]
      Or[gt][]
      Or[ge][]
    },
  ),
)

#let aExprOp = bnf(
  Prod(
    $"aop"$,
    delim: $=$,
    annot: $sans("AExprOp")$,
    {
      Or[add][]
      Or[sub][]
      Or[mul][]
      Or[div][]
      Or[mod][]
      Or[con][]
    },
  ),
)

#let unaryOp = bnf(
  Prod(
    $"uop"$,
    delim: $=$,
    annot: $sans("UnaryOp")$,
    {
      Or[add][]
      Or[sub][]
      Or[not][]
    },
  ),
)

#let operator = bnf(
  Prod(
    $"op"$,
    delim: $=$,
    annot: $sans("Op")$,
    {
      Or[acop][AExprCmpOp]
      Or[aop][AExprOp]
      Or[bop][BoolBinOp]
    },
  ),
)

#let expression = bnf(
  Prod(
    $"e"$,
    delim: $=$,
    annot: $sans("Expr")$,
    {
      Or[value][Value]
      Or[field][String String]
      Or[bin][Expr Op Expr]
      Or[un][UnaryOp Expr]
    },
  ),
)

#let selectField = bnf(
  Prod(
    $"sf"$,
    delim: $=$,
    annot: $sans("SelectField")$,
    {
      Or[col][String String]
      Or[alias][String String String]
    },
  ),
)

#let select = bnf(
  Prod(
    $"s"$,
    delim: $=$,
    annot: $sans("Select")$,
    {
      Or[list][Bool (List SelectField)]
      Or[all][Bool]
    },
  ),
)

#let from = bnf(
  Prod(
    $"f"$,
    delim: $=$,
    annot: $sans("From")$,
    {
      Or[table][String]
      Or[alias][From String]
      Or[join][Join From From Expr]
      Or[implicitJoin][From From]
      Or[nestedJoin][Select From Expr String]
    },
  ),
)

#let query = bnf(
  Prod(
    $"q"$,
    delim: $=$,
    annot: $sans("Query")$,
    {
      Or[][Select From Expr]
    },
  ),
)