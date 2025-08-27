#import "@preview/curryst:0.5.1": prooftree, rule
#import "@preview/lovelace:0.3.0": pseudocode-list
#set text(size: 14pt)
= Todo
- Introduce subtyping lattice
- Lambdas
= Grammar
== Base Type
$tau ::= sigma bar r$

$sigma ::= #[float] bar sigma times sigma bar eta dot sigma$
== Natural Numbers
$eta ::= 0 bar 1 bar ...$
== Range
$r::= eta..eta$
= Term
$t ::= "fl" bar p bar "for" i : r "in" t bar "let" x := t "in" t bar (t,t) bar "if" t <= eta "then" t "else" t bar t + t bar t * t bar t - t bar t \/t$

- $i$ and $x$ are identifiers.
== Literal
$"fl" ::= 0.0 bar -4.21 bar 523.215 bar ...$

== Place Expression
$p::= x bar p[t] bar p."fst" bar p."snd"$


= Environment
== Type Environment
$Gamma ::= bullet bar Gamma,(x:tau)$

#pagebreak()
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
    $eta_l..eta_r : "ok"$,
    $Gamma,(i:eta_l..eta_r) tack t_"body" : sigma$,
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
    $r_"then" = eta_l..min(eta, eta_r)$,
    $r_"else" = (min(eta, eta_r)+1)..eta_r$,
    $r_"then" : "ok"$,
    $r_"else" : "ok"$,
    $Gamma, (t:r_"then") tack t_"then" : sigma$,
    $Gamma, (t:r_"else") tack t_"else" : sigma$,
  )
  let conclusion = $Gamma tack "if" t <= eta "then" t_"then" "else" t_"else" : sigma$
  let _rule = rule(
    name: "T-IF",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}

//T-THEN-ONLY
//If there is only if path possible, then only check the if path
#{
  let premises = (
    $Gamma tack t:eta_l .. eta_r$,
    $eta_r <= eta$,
    $Gamma tack t_"then" : sigma$,
  )
  let conclusion = $Gamma tack "if" t <= eta "then" t_"then" "else" t_"else" : sigma$
  let _rule = rule(
    name: "T-THEN-ONLY",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}
#pagebreak()

#set align(left)
= Well-formedness Rules
#set align(center)
#{
  let premise = $eta_0 <= eta_1$
  let conclusion = $eta_0..eta_1:"ok"$
  let _rule = rule(
    name: "W-RANGE",
    conclusion,
    premise,
  )
  prooftree(_rule)
}
#pagebreak()
#set align(left)
= Auxillary Definitions
$"length"(eta_0..eta_1) = eta_1 - eta_0 + 1$
