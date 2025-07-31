#import "@preview/curryst:0.5.1": prooftree, rule
= Grammar
== Base Type
$tau ::= sigma bar r$

$sigma ::= italic("float") bar sigma times sigma bar eta dot sigma$
== Natural Numbers
$eta ::= 0 bar 1 bar ...$
== Range
$r::= eta..eta$
= Term
$t ::= "fl" bar eta bar p bar "for" i : r "in" t bar "let" x = t "in" t bar (t,t)$
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
  let conclusion = $Gamma tack "let" x=t "in" t_"body" : sigma_"body"$

  let _rule = rule(name: [T-LET], conclusion, ..premises)

  prooftree(_rule)
}

// T-FOR
#{
  let premises = (
    $r = eta_1 ..eta_2$,
    $r:"ok"$,
    $Gamma,(i:r) tack t_"body" : sigma$,
  )
  let conclusion = $Gamma tack "for" i: r "in" t_"body" : (eta_2 -eta_1) dot sigma$
  let _rule = rule(
    name: "T-FOR",
    conclusion,
    ..premises,
  )
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
    $Gamma tack t : eta_(t) dot sigma$,
    $Gamma tack t_("index") : eta_(l)..eta_(r)$,
    $eta_(r) <= eta_(t)$,
  )
  let conclusion = $Gamma tack t[t_"index"]: sigma$
  let _rule = rule(name: "T-INDEX-RANGE", conclusion, ..premises)
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


#align(left)[= Well-formedness rules]
// W-RANGE-ONE
#{
  let premises = (
    $eta_1 <= eta_2$,
  )
  let conclusion = $eta_1 .. eta_2 : "ok"$
  let _rule = rule(
    name: "W-RANGE",
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
for i: (0..5) in
  for j: (0..6) in
    for k: (0..7) in
      4.2
```
This results in a value of type $5 dot 6 dot 7 dot italic("float")$
```scala
for i : 0..5 in
  for j: 0..10 in
    1.2
```
This results in a value of type $5 dot 10 dot italic("float")$
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
This is of type $2dot 1 dot italic("float")$

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
This is of type $(5 dot 5 dot italic("float")) times (2 dot 2 dot italic("float"))$

=== Nested tuple/array
```ocaml
let tup = (3.14159, for i : 0..5 in 6.25) in
  for i : 0..10 in
    tup
```
This is of type $10 dot (italic("float") times (5 dot italic("float")))$
