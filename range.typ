#import "@preview/curryst:0.5.1": prooftree, rule
#import "@preview/lovelace:0.3.0": pseudocode-list
#set text(size: 14pt)
= Grammar
== Base Type
$tau ::= sigma bar r$

$sigma ::= #[float] bar sigma times sigma bar eta dot sigma$
== Natural Numbers
$eta ::= 0 bar 1 bar ...$
== Range
$r::= eta..eta bar "empty"$
= Term
$t ::= "fl" bar eta bar p bar "for" i : r "in" t bar "let" x := t "in" t bar (t,t) bar "if" t subset.eq t "then" t "else" t bar t + t bar t * t bar t - t bar t \/t$

- $i$ and $x$ are identifiers.
== Literal
$"fl" ::= 0.0 bar -4.21 bar 523.215 bar ...$

== Place Expression
$p::= x bar p[t] bar p."fst" bar p."snd"$


= Environment
== Type Environment
$Gamma ::= bullet bar Gamma,(x:tau)$

= Typing Rules
// Utility for declarative premise stacking
#let push-premises(premises: array) = {
  grid(
    columns: premises.len(),
    column-gutter: 1em,
    row-gutter: .5em,
    align: center,
    inset: (x: 2pt),
    ..premises
  )
}

#let stack-premises(premises: array, height_diff: 0pt) = {
  let grid-cell(premise) = {
    if type(premise) == array {
      push-premises(premises: premise)
    } else {
      grid.cell(
        premise,
      )
    }
  }
  let stacked = premises.map(grid-cell)
  grid(
    align: center,
    row-gutter: .5em,
    inset: (y: height_diff),
    ..stacked,
  )
}
#set align(center)

// T-ARITH
#{
  let premises = (
    $Gamma tack t_l: "float"$,
    $Gamma tack t_r: "float"$,
    $"op" in {+,-,*,\/}$,
  )
  let conclusion = $Gamma tack t_l "op" t_r : "float"$
  let _rule = rule(
    name: [T-ARITH],
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}
// T -VAR
#{
  let premises = (
    $x : sigma in Gamma$,
  )
  let conclusion = $Gamma tack x : sigma$

  let _rule = rule(name: [T-VAR], conclusion, ..premises)

  prooftree(_rule)
}

// T-LET
#{
  let premises = (
    $Gamma tack t:sigma$,
    $Gamma,(x:sigma) tack t_"body":sigma_"body"$,
  )
  let conclusion = $Gamma tack "let" x:=t "in" t_"body" : sigma_"body"$

  let _rule = rule(name: [T-LET], conclusion, ..premises)

  prooftree(_rule)
}

// T-FOR
#{
  let premises = (
    $Gamma,(i:r) tack t_"body" : sigma$,
  )
  let conclusion = $Gamma tack "for" i: r "in" t_"body" : "length"(r) dot sigma$
  let _rule = rule(
    name: "T-FOR",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}

// T-INDEX-RANGE
#{
  let premises = (
    $Gamma tack t : eta_(t) dot sigma$,
    $Gamma tack t_("index") : eta_(l)..eta_(r)$,
    $eta_(r) < eta_(t)$,
  )
  let conclusion = $Gamma tack t[t_"index"]: sigma$
  let _rule = rule(name: "T-INDEX-RANGE", conclusion, ..premises)
  prooftree(_rule)
}

// T-INDEX-RANGE-EMPTY
#{
  let premises = (
    $Gamma tack t_"index": "empty"$,
    $Gamma tack t :eta_t dot sigma$,
  )
  let conclusion = $Gamma tack t[t_"index"] : sigma$
  let _rule = rule(name: "T-INDEX-RANGE-EMPTY", conclusion, ..premises)
  prooftree(_rule)
}

// T-FST
#{
  let premise = $Gamma tack t:sigma_1 times sigma_2$
  let conclusion = $Gamma tack t."fst":sigma_1$
  let _rule = rule(
    name: "T-FST",
    conclusion,
    premise,
  )
  prooftree(_rule)
}

// T-SND
#{
  let premise = $Gamma tack t:sigma_1 times sigma_2$
  let conclusion = $Gamma tack t."snd":sigma_2$
  let _rule = rule(
    name: "T-SND",
    conclusion,
    premise,
  )
  prooftree(_rule)
}

// T-NAT
#{
  let _rule = rule(
    name: "T-NAT",
    $eta:eta..eta+1$,
  )
}

// T-IF
#{
  let premises = (
    $Gamma tack t_l : r_l$,
    $Gamma tack t_r: r_r$,
    $Gamma, (t_l: r_l inter r_r ) tack t_"if":sigma_"if"$,
    $(r_0,r_1) = r_l \/ r_r$,
    $Gamma, (t_l: r_0 ) tack t_"else":sigma_"else0"$,
    $Gamma, (t_l: r_1 ) tack t_"else":sigma_"else1"$,
    $sigma = sigma_"if" = sigma_"else0" = sigma_"else1"$,
  )
  let conclusion = $Gamma tack "if" t_l subset.eq t_r "then" t_"if" "else" t_"else" : sigma$
  let _rule = rule(
    name: "T-IF",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}
#pagebreak()

#set align(left)
= Auxillary definitions

#pseudocode-list[
  mkRng($eta_l$, $eta_r$) = *if* $0 <= eta_l <= eta_r$ *then* $eta_l..eta_r$ *else* empty
]

#pseudocode-list[
  - length($r$) = *match* r *with*
    - empty $=>$ 0
    - $eta_l..eta_r$ $=>$ $eta_r - eta_l + 1$
]

#pseudocode-list[
  - $r_l inter r_r$ = *match* $(r_l, r_r)$ *with*
    - (empty,\_) $=>$ empty
    - (\_,empty) $=>$ empty
    - ($eta_"l0"..eta_"l1", eta_"r0"..eta_"r1"$) $=>$ $"mkRng"(max(eta_"l0", eta_"r0"), min(eta_"l1", eta_"r1"))$

]


#pseudocode-list[
  - $r_l \/ r_r$ = *match* $r_l inter r_r$ *with*
    - empty $=>$ $(r_l, "empty")$
    - $eta_0..eta_1$ $=>$ *match* $r_l$ *with*
      - $eta_"l0"..eta_"l1"$ $=>$ (mkRng($eta_"l0", eta_0-1$), mkRng($eta_1+1, eta_"l1"$))
      - \_ $=>$ *unreachable*
]



#set align(left)
#pagebreak()
= Examples
== For expression
```scala
for i: (0..5) in
  for j: (0..6) in
    for k: (0..7) in
      4.2
```
This results in a value of type $5 dot 6 dot 7 dot #[float]$
```scala
for i : 0..5 in
  for j: 0..10 in
    1.2
```
This results in a value of type $5 dot 10 dot #[float]$
== Indexing by a value of type range
```scala
for i: 0..5 in
  a[0][i]
```
This is equivalent to: `a[0][0:5]`
== Slicing
```scala
for i: 0..10 in
  for j: 0..5 in
    a[i][j]
```
This is of type $10 dot 5 dot sigma$ and equivalent to `a[0..10][0..5]`
where $sigma$ is the type of $a[0][0]$
== let in
```scala
let arr =
  for i: 0..5 in
    for j : 0..5 in
      3.14159
in
for i: 0..2 in
  for j: 0..1 in
    arr[i][j]
```
This is of type $2dot 1 dot #[float]$

== let in, for, and tuple
=== tuple
```scala
let arr_1 =
  for i: 0..5 in
    for j: 0..5 in
      3.14159 in
let arr_2 =
  for i: 2..4 in
    for j: 1..3 in
      arr_1[i][j] in
(arr_1, arr_2)
```
This is of type $(5 dot 5 dot #[float]) times (2 dot 2 dot #[float])$

=== Nested tuple/array
```ocaml
let tup = (3.14159, for i : 0..5 in 6.25) in
  for i : 0..10 in
    tup
```
This is of type $10 dot (#[float] times (5 dot #[float]))$
