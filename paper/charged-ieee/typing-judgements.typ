#import "@preview/curryst:0.3.0"
// inductive WFValue : Value → DataType → Prop
#let rule = curryst.rule

#let proof-tree = curryst.proof-tree


#let tj-bigint = rule(
  label: [],
  name: [#smallcaps[Bigint]],
  [bigInt i : bigInt],
  [$i : ZZ$],
  [$-2#super[64] < i < 2#super[64]$]
)

 #let tj-bit = rule(
  label: [],
  name: [#smallcaps[Bit]],
  [bit n b : bit],
  [$n : NN$],
  [$b : {0,1}#super[n]$],
)

 #let tj-boolean = rule(
  label: [],
  name: [#smallcaps[Boolean]],
  [boolean b : boolean],
  [$b : {0, 1}#super[1]$],
)

 #let tj-char = rule(
  label: [],
  name: [#smallcaps[Char]],
  [char n s : char],
  [$n : NN$],
  [$s : "String"$],
  [$|s| = n$],
)

 #let tj-date = rule(
  label: [],
  name: [#smallcaps[Date]],
  [date y m d : date],
  [$y : NN$],
  [$m : "Fin" 13$],
  [$d : "Fin" 31$],
  [$m > 0 ∧ d > 0$],
)

 #let tj-double = rule(
  label: [],
  name: [#smallcaps[Double]],
  [double d : boolean],
  [$d : "FP64"$],
)

#let tj-integer = rule(
  label: [],
  name: [#smallcaps[Integer]],
  [integer i : integer],
  [$i : ZZ$],
  [$-2#super[32] < i < 2#super[32]$],
)

 #let tj-null = rule(label: [], name: [#smallcaps[Null]], [null], [])

 #let tj-text = rule(label: [], name: [#smallcaps[Text]], [text s : text], [$s : "String"$],
)

 #let tj-varbit = rule(
  label: [],
  name: [#smallcaps[Varbit]],
  [varbit n b : varbit],
  [$n : NN$],
  [$b: {0,1}#super[n]$],
  [$|b| <= n$],
)

#let tj-varchar = rule(
  label: [],
  name: [#smallcaps[Varchar]],
  [varchar n s : varchar],
  [$n : NN$],
  [$s : "String" tack$],
  [$|s| <= n$],
)

//inductive WFNumConv : DataType → DataType → DataType → Prop

#let tj-eqd = rule(label: [], name: [#smallcaps[Eq]], [$tack$ NumConv a a : $alpha$], [$a : alpha$], [$alpha = "integer" or alpha = "bigInt" or alpha = "double"$])
#let tj-intbigint = rule(label: [], name: [#smallcaps[Intbigint]],
[$tack$ NumConv a b : bigInt],
[a : integer],
[b : bigInt],
)

#let tj-bigintdouble = rule(label: [], name: [#smallcaps[Bigintdouble]], [$tack$ WFNumConv a b = double], [a : bigInt], [b : double])
#let tj-intdouble = rule(label: [], name: [#smallcaps[Intdouble]], [$tack$ NumConv a b : double], [a : integer], [b : double])
#let tj-symmd = rule(
  label: [],
  name: [#smallcaps[Symm]],
  [$tack$ NumConv b a : T],
  [$tack$ NumConv a b : T],
)

// inductive WFCharConv : DataType → DataType → DataType → Prop

#let tj-charc = rule(label: [], name: [#smallcaps[Eq]], [$tack$ CharConv a a : $alpha$], [$a : alpha$], [$alpha = "char" or alpha = "varchar" or alpha = "text"$])

#let tj-cvc = rule(
  label: [],
  name: [#smallcaps[Cvc]],
  [$tack$ CharConv a b : varchar],
  [b : varchar],
  [a : char],
)

#let tj-vctx = rule(
  label: [],
  name: [#smallcaps[Vctx]],
  [$tack$ CharConv a b : text],
  [a : varchar],
  [b : text]
)

#let tj-ctx = rule(
  label: [],
  name: [#smallcaps[Ctx]],
  [$tack$ CharConv a b : text],
  [a : char],
  [b : text],
)

#let tj-symmc = rule(
  label: [],
  name: [#smallcaps[Symm]],
  [$tack$ CharConv b a : T],
  [$tack$ CharConv a b : T],
)

//inductive WFConv : DataType → DataType → Prop

#let tj-numeric = rule(
  label: [],
  name: [#smallcaps[Numeric]],
  [$tack$ Conv T₁ T₂],
  [$tack$ NumConv T₁ T₂ : T₃],
)
#let tj-charcc = rule(
  label: [],
  name: [#smallcaps[Character]],
  [$tack$ Conv T₁ T₂],
  [$tack$ CharConv T₁ T₂ : T₃],
)
#let tj-eqc = rule(label: [], name: [#smallcaps[Eq]], [$tack$ Conv T T], [])

//inductive WFExpr : RelationType → Expr → DataType → Prop

#let tj-value = rule(
  label: [],
  name: [#smallcaps[Value]],
  [$Gamma tack$ v : T],
  [$Gamma tack$ Value v : T],
)

#let tj-field = rule(
  label: [],
  name: [#smallcaps[Field]],
  [$Gamma tack$ field name table : T],
  [(name, table, T) $in Gamma$],
)

#let tj-not = rule(
  label: [],
  name: [#smallcaps[Not]],
  [$Gamma tack$ un not e : boolean],
  [$Gamma tack$ e : boolean],
)

#let tj-bcmp = rule(
  label: [],
  name: [#smallcaps[Bcmp]],
  [$Gamma tack$ bin lhs (bop op) rhs : boolean],
  [$Gamma tack$ lhs : boolean],
  [$Gamma tack$ rhs : boolean],
)

#let tj-acmp = rule(
  label: [],
  name: [#smallcaps[Acmp]],
  [$Gamma tack$ bin lhs (acop op) rhs : boolean],
  [$Gamma tack$ lhs : T₁],
  [$Gamma tack$ rhs : T₂],
  [Conv T₁ T₂],
)

#let tj-aexpr = rule(
  label: [],
  name: [#smallcaps[Aexpr]],
  [$Gamma tack$ bin lhs (aop op) rhs : T],
  [$Gamma tack$ lhs : T₁],
  [$Gamma tack$ rhs : T₂],
  [NumConv lhs rhs : T],
)

#let tj-concat = rule(
  label: [],
  name: [#smallcaps[Concat]],
  [$Gamma tack$ bin lhs (aop con) rhs : text],
  [$Gamma tack$ lhs : text],
  [$Gamma tack$ rhs : T],
)

#let tj-pos = rule(label: [], name: [#smallcaps[Pos]], [$Gamma tack$ un add e : T], [$Gamma tack$ e : T],
[T = integer ∨ T = bigInt ∨ T = double]
)

#let tj-neg = rule(label: [], name: [#smallcaps[Neg]], [$Gamma tack$ un sub e : T], [$Gamma tack$ Expr e : T],
[T = integer ∨ T = bigInt ∨ T = double]
)

#let tj-dateadd = rule(
  label: [],
  name: [#smallcaps[Dateadd]],
  [$Gamma tack$ bin lhs (aop add) rhs : date],
  [$Gamma tack$ rhs : integer],
  [$Gamma tack$ lhs : date],
)

#let tj-datesub = rule(
  label: [],
  name: [#smallcaps[Datesub]],
  [$Gamma tack$ bin lhs (aop sub) rhs : date],
  [$Gamma tack$ rhs : integer],
  [$Gamma tack$ lhs : date],
)

//inductive WFSelectField : RelationType → SelectField → DataType → Prop

#let tj-col = rule(
  label: [],
  name: [#smallcaps[Col]],
  [$Gamma tack$ col name tableName : T],
  [(name, tableName, T) $in Gamma$],
)

#let tj-alias = rule(
  label: [],
  name: [#smallcaps[Alias]],
  [$Gamma tack$ alias name tableName a : T],
  [(name, tableName, T) $in Gamma$],
)

//inductive WFSelect : RelationType → Select → RelationType → Prop

#let tj-list = rule(
  label: [],
  name: [#smallcaps[List]],
  [$Gamma tack$ list b sfs : {toTuple s | s in sfs}],
  [$forall "sf" in "sfs", exists "t", Gamma tack "sf t"$]
)

#let tj-all = rule(label: [], name: [#smallcaps[All]], [$Gamma tack$ all b : T], [$Gamma =$ T])

//inductive WFFrom : Schema → From → RelationType → Prop

#let tj-table = rule(
  label: [],
  name: [#smallcaps[Table]],
  [$Gamma tack$ table name : T],
  [(name, T) $in Gamma$],
)

#let tj-aliass = rule(
  label: [],
  name: [#smallcaps[Alias]],
  [$Gamma tack$ alias f a : ${(n, a, T') | (n, t, T') in T}$],
  [$Gamma tack$ f : T],
)

#let tj-join = rule(
  label: [],
  name: [#smallcaps[Join]],
  [$Gamma tack$ join j f₁ f₂ e : T₁ ++ T₂],
  [$Gamma tack$ f₁ : T₁],
  [$Gamma tack$ f₂ : T₂],
  [T₁ ++ T₂ $tack$ Expr e : boolean],
)

#let tj-implicitjoin = rule(
  label: [],
  name: [#smallcaps[Implicitjoin]],
  [$Gamma tack$ implicitJoin f₁ f₂ : T₁ ++ T₂],
  [$Gamma tack$ f₂ : T₂],
  [$Gamma tack$ f₁ : T₁],
)

#let tj-nestedjoin = rule(
  label: [],
  name: [#smallcaps[Nestedjoin]],
  [$Gamma tack$ nestedJoin s f e a stx : ${(n, t, T') | (n, a, T') in "Ts"}$],
  [$Gamma tack$ f : Tf],
  [Tf $tack$ Select s : Ts],
  [Tf $tack$ Expr e : boolean],
)

//inductive WFQuery : Schema → Query → RelationType → Prop

#let tj-query = rule(
  label: [],
  name: [#smallcaps[Query]],
  [$Gamma tack$ s f e : Ts],
  [$Gamma tack$ From f : Tf],
  [Tf $tack$ Select s : Ts],
  [Tf $tack$ Expr e : boolean],
)