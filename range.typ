#import "@preview/curryst:0.5.1": prooftree, rule
= Grammar
== Base Type
$tau ::= sigma bar r$

$sigma ::= italic("float") bar sigma times sigma bar eta dot sigma$
== Natural Numbers
$eta ::= 0 bar 1 bar ...$
== Range
$r::= eta..eta bar r dot r$
= Term
$t ::= l bar p bar "for" i : r "in" t bar t."fst" bar t."snd" bar "let" x = t "in" t bar (t,t)$
- $i$ and $x$ are identifiers.
== Literal
$"fl" = 0.0 bar -4.21 bar 523.215 bar ...$

== Place Expression
$p::= x bar p[t] bar p angle.l t angle.r bar p."fst" bar p."snd"$


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

// T-LET
#{
  let premises = (
    $Gamma tack t:sigma$,
    $Gamma,(x:sigma) tack t_"body":sigma_"body"$,
  )
  let conclusion = $Gamma tack "let" x=t "in" t_"body" : sigma_"body"$

  let _rule = rule(name: [T-LET], conclusion, ..premises)

  prooftree(_rule)
}

// T-FOR
#{
  let premises = (
    $r:"ok"$,
    $Gamma,(i:r) tack t_"body" : sigma$,
  )
  let conclusion = $Gamma tack "for" i: r "in" t_"body" : r dot sigma$
  let _rule = rule(
    name: "T-FOR",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}

// T-SLICE
#{
  let premises = (
    $Gamma tack t : eta_1 dot eta_2 ... dot eta_n dot sigma$,
    $r = (eta_1^prime .. eta_1^#[$prime prime$]) dot (eta_2^prime .. eta_2^#[$prime prime$]) ... dot (eta_n^prime .. eta_n^#[$prime prime$])$,
    ($r:"ok"$, $forall i in {1,2,...,n}.eta_i^#[$prime prime$] <= eta_i$),
  )
  let conclusion = $Gamma tack t angle.l r angle.r : (eta_1^#[$prime prime$] - eta_1^prime) dot (eta_2^#[$prime prime$] - eta_2^prime) dot ... dot (eta_n^#[$prime prime$] - eta_n^prime) dot sigma$
  let _rule = rule(name: [T-SLICE], conclusion, stack-premises(premises: premises, height_diff: 1pt))
  prooftree(_rule)
}


//T-INDEX-NAT
#{
  let premise = $Gamma tack t[eta..(eta+1)]$

  let conclusion = $Gamma tack t[eta] : sigma$
  let _rule = rule(
    name: "T-INDEX-NAT",
    conclusion,
    premise,
  )
  prooftree(_rule)
}

// T-INDEX-RANGE
#{
  let premises = (
    $Gamma tack t : overline(eta_i) dot sigma$,
    $Gamma tack t_"index" : (eta_1^prime..eta_1^#[$prime prime$]) dot (eta_2^prime .. eta_2^#[$prime prime$]) dot ... dot (eta_n^prime .. eta_n^#[$prime prime$])$,
    $forall i in {1,2,...,n}.eta_i^#[$prime prime$] <= eta_i$,
  )
  let conclusion = $Gamma tack t[t_"index"]: sigma$
  let _rule = rule(name: "T-INDEX-RANGE", conclusion, stack-premises(premises: premises, height_diff: 1pt))
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

// T-FLOAT-LIT
#{
  let conclusion = $Gamma tack "fl": italic("float")$
  let _rule = rule(
    name: "T-FLOAT-LIT",
    conclusion,
  )
  prooftree(_rule)
}

// T-TUPLE-LIT
#{
  let premises = (
    $Gamma tack t_1: sigma_1$,
    $Gamma tack t_2: sigma_2$,
  )
  let conclusion = $Gamma tack (t_1,t_2) : sigma_1 times sigma_2$
  let _rule = rule(
    name: "T-TUPLE-LIT",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}



#align(left)[= Well-formedness rules]
// W-RANGE-ONE
#{
  let premises = (
    $eta_1 <= eta_2$,
  )
  let conclusion = $eta_1 .. eta_2 : "ok"$
  let _rule = rule(
    name: "W-RANGE-ONE",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}
// W-RANGE-MUL
#{
  let premises = (
    $r_1 : "ok"$,
    $r_2: "ok"$,
  )
  let conclusion = $r_1 dot r_2: "ok"$
  let _rule = rule(
    name: "W-RANGE-MUL",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}
#set align(left)
#pagebreak()
= Examples
== For expression
```scala
for i: range(0,5) . range(0,6) . range(0.7) in 4.2
```
This results in a value of type $5 dot 6 dot 7 dot italic("float")$
```scala
for i : range(0,5) in for j: range(0,10) in 1.2
```
This results in a value of type $5 dot 10 dot italic("float")$
== Indexing by a value of type range
```scala
for i: range(0,5) in a[0][i]
```
This is equivalent to: `a[0][0:5]`
== Slicing
```scala
a[range(0,10) . range(0,5)]
```
This is of type $10 dot 5 dot sigma$
where $sigma$ is the type of $a[0][0]$
== let in
```ocaml
let arr =
  for i: range(0,5) in
    for j : range(0,5) in
      3.14159
  in arr[range(0,2).range(0,1)]
```
This is of type $2dot 1 dot italic("float")$

== let in, for, and tuple
=== tuple
```ocaml
let arr_1 =
  for i: range(0,5) in
    for j: range(0,5) in
      3.14159 in
let arr_2 =
  for i: range(2,4) in
    for j: range(1,3) in
      arr_1[i][j] in
(arr_1, arr_2)
```
This is of type $(5 dot 5 dot italic("float")) times (2 dot 2 dot italic("float"))$

=== nested tuple/array
```ocaml
let tup = (3.14159, for i : range(0,5) in 6.25) in
  for i : range(0,10) in
    tup
```
This is of type $10 dot (italic("float") times (5 dot italic("float")))$
