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
$t ::= "fl" bar eta bar p bar "for" i : r "in" t bar "let" x := t "in" t bar (t,t) bar "if" t <= eta "then" t "else" t bar t + t bar t * t bar t - t bar t \/t$

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
    $r^prime = "mkRng"(eta_l..eta_r)$,
    $Gamma,(i:r^prime) tack t_"body" : sigma$,
  )
  let conclusion = $Gamma tack "for" i: eta_l..eta_r "in" t_"body" : "length"(r^prime) dot sigma$
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

// T-INDEX-NAT
#{
  let premises = ($Gamma tack t:eta_t dot sigma$, $eta < eta_t$)
  let conclusion = $Gamma tack t[eta] : sigma$
  let _rule = rule(name: "T-INDEX-NAT", conclusion, ..premises)
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

//T-IF
#{
  let premises = (
    $Gamma tack t:eta_l .. eta_r$,
    $r_"then" = "mkRng"(eta_l..min(eta, eta_r))$,
    $r_"else" = "mkRng"(min(eta, eta_r)+1..eta_r)$,
    $Gamma, (t:r_"then") tack t_"then" sigma_"then"$,
    $Gamma, (t:r_"else") tack t_"else" sigma_"else"$,
    $sigma = sigma_"then" = sigma_"else"$,
  )
  let conclusion = $Gamma tack "if" t <= eta "then" t_"then" "else" t_"else" : sigma$
  let _rule = rule(
    name: "T-IF",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}

//T-IF-EMPTY
#{
  let premises = (
    $Gamma tack t:"empty"$,
    $Gamma tack t_"then" sigma_"then"$,
    $Gamma tack t_"else" sigma_"else"$,
    $sigma = sigma_"then" = sigma_"else"$,
  )
  let conclusion = $Gamma tack "if" t <= eta "then" t_"then" "else" t_"else" : sigma$
  let _rule = rule(
    name: "T-IF-EMPTY",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}
#pagebreak()

#set align(left)
= Auxillary definitions

#pseudocode-list[
  - mkRng(r)  = *match* r *with*
    - $eta_l$..$eta_r$ $=>$ *if* $0 <= eta_l <= eta_r$ *then* $eta_l..eta_r$ *else* empty
    - empty $=>$ empty
]

#pseudocode-list[
  - length($r$) = *match* r *with*
    - empty $=>$ 0
    - $eta_l..eta_r$ $=>$ $eta_r - eta_l + 1$
]

// #pseudocode-list[
//   - $r_l inter r_r$ = *match* $(r_l, r_r)$ *with*
//     - (empty,\_) $=>$ empty
//     - (\_,empty) $=>$ empty
//     - ($eta_"l0"..eta_"l1", eta_"r0"..eta_"r1"$) $=>$ $"mkRng"(max(eta_"l0", eta_"r0"), min(eta_"l1", eta_"r1"))$

// ]


// #pseudocode-list[
//   - $r_l \/ r_r$ = *match* $r_l inter r_r$ *with*
//     - empty $=>$ $(r_l, "empty")$
//     - $eta_0..eta_1$ $=>$ *match* $r_l$ *with*
//       - $eta_"l0"..eta_"l1"$ $=>$ (mkRng($eta_"l0", eta_0-1$), mkRng($eta_1+1, eta_"l1"$))
//       - \_ $=>$ *unreachable*
// ]
