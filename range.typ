#import "@preview/curryst:0.5.1": prooftree, rule
#import "@preview/lovelace:0.3.0": pseudocode-list
#set text(size: 14pt)
= Grammar
== Types
$tau ::= sigma bar r$

#{
  // eventually add:
  let _ = $product_(x:r)sigma$
}
== Base Types
$sigma ::= #[float] bar sigma times sigma bar eta dot sigma bar sigma -> sigma$
== Natural Numbers
$eta ::= 0 bar 1 bar ...$
== Range
$r::= eta..eta$
= Term
$t ::= p bar "let" x := t "in" t bar (t,t) bar "if" t <= eta "then" t "else" t bar t + t bar t * t bar t - t bar t \/t bar t space t bar v$

$v = "fl" bar "for" i : r "in" t bar (v,v) bar lambda (x: sigma).t bar eta$
- $i$ and $x$ are identifiers.
== Literal
$"fl" ::= 0.0 bar -4.21 bar 523.215 bar ...$

== Place Expression
$p::= x bar p[t] bar p."fst" bar p."snd"$


= Environment
== Type Environment
$Gamma ::= bullet bar Gamma,(x:tau)$
== Evaluation Context
$rho ::= bullet bar rho, [x mapsto v]$
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
#align(left)[#rect[$Gamma tack t : sigma$]]
// T-ABS
#{
  let premises = (
    $Gamma,(x:sigma_1) tack t:sigma_2$,
  )
  let conclusion = $Gamma tack lambda (x : sigma_1). t: sigma_1 -> sigma_2$
  let _rule = rule(
    name: [T-ABS],
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}

// T-APP
#{
  let premises = (
    $f : sigma_1 -> sigma_2$,
    $Gamma tack t: sigma_3$,
    $exists sigma. sigma_3 inter.sq sigma_1 = sigma$,
  )
  let conclusion = $f space t: sigma_2$
  let _rule = rule(
    name: [T-APP],
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}

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
  let conclusion = $Gamma tack "for" i: eta_l..eta_r "in" t_"body" : "length"(eta_l..eta_r) dot sigma$
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
    $Gamma, (t:r_"then") tack t_"then" : sigma_1$,
    $Gamma, (t:r_"else") tack t_"else" : sigma_2$,
    $sigma_1 union.sq sigma_2 = sigma$,
  )
  let conclusion = $Gamma tack "if" t <= eta "then" t_"then" "else" t_"else" : sigma$
  let _rule = rule(
    name: "T-IF",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}

#pagebreak()
#align(left)[= Wellformedness Rules]
#align(left)[#rect[$r:"ok"$]]
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
#set align(left)
= Subtyping Rules
#rect[$sigma union.sq sigma = sigma$]
$
  sigma union.sq sigma = sigma\
  eta_1 dot sigma union.sq eta_2 dot sigma = min(eta_1, eta_2)dot sigma\
  (sigma_1,sigma_2) union.sq (sigma_3,sigma_4) = (sigma_1 union.sq sigma_3, sigma_2 union.sq sigma_4) \
  "float" union.sq "float" = "float"\
  sigma_1 -> sigma_2 union.sq sigma_3 -> sigma_4 = (sigma_1 inter.sq sigma_3) -> (sigma_2 union.sq sigma_4)\
$
#rect[$sigma inter.sq sigma = sigma$]
$
  sigma inter.sq sigma = sigma\
  eta_1 dot sigma inter.sq eta_2 dot sigma = max(eta_1, eta_2) dot sigma\
  (sigma_1,sigma_2) inter.sq (sigma_3,sigma_4) = (sigma_1 inter.sq sigma_3, sigma_2 inter.sq sigma_4)\
  "float" inter.sq "float" = "float"
$
#pagebreak()
#align(left)[= Evaluation Rules
  #rect[$rho tack t --> t$]
]
#set align(center)
#{
  let premise = $rho tack t_1 --> t_1^prime$
  let conclusion = $rho tack t_1 t_2 --> t_1^prime t_2$
  let _rule = rule(
    name: "E-APP1",
    conclusion,
    premise,
  )
  prooftree(_rule)
}
#{
  let premise = $rho tack t_2 --> t_2^prime$
  let conclusion = $rho tack v space t_2 --> v space t_2^prime$
  let _rule = rule(
    name: "E-APP2",
    conclusion,
    premise,
  )
  prooftree(_rule)
}
#{
  let _rule = rule(
    name: "E-APPABS",
    $rho tack (lambda (x : sigma_1). t_"body") v --> [x mapsto v] t_"body"$,
  )
  prooftree(_rule)
}
#{
  let premise = $rho tack$
}

#{
  let _rule = rule(
    name: "E-VAR",
    $rho tack x --> v$,
    $[x mapsto v] in rho$,
  )
  prooftree(_rule)
}

#{
  let premises = (
    $rho tack t --> v$,
    $rho, [x mapsto v] tack t_"body" --> t_"body"^prime$,
  )
  let conclusion = $rho tack "let" x = t "in" t_"body" --> t_"body"^prime$
  let _rule = rule(
    name: "E-LET",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}

#{
  let premise = $rho tack t_1 --> t_1^prime$
  let conclusion = $rho tack t_1[v] --> t_1^prime [v]$
  let _rule = rule(
    name: "E-INDEX",
    conclusion,
    premise,
  )
  prooftree(_rule)
}
#{
  let premise = $rho, [i mapsto eta] tack t --> t^prime$
  let conclusion = $rho tack ("for" i : r "in" t) [eta] --> t^prime$
  let _rule = rule(
    name: "E-APPINDEX",
    conclusion,
    premise,
  )
  prooftree(_rule)
}

#{
  let premise = $rho tack t_1 --> t_1^prime$
  let conclusion = $rho tack (t_1, t_2) --> (t_1^prime, t_2)$
  let _rule = rule(
    name: "E-TUP1",
    conclusion,
    premise,
  )
  prooftree(_rule)
}

#{
  let premise = $rho tack t_2 --> t_2^prime$
  let conclusion = $rho tack (t_1, t_2) --> (t_1, t_2^prime)$
  let _rule = rule(
    name: "E-TUP2",
    conclusion,
    premise,
  )
  prooftree(_rule)
}

#{
  let premise = $rho tack t_1 --> t_1^prime$
  let conclusion = $rho tack t_1."fst" --> t_1^prime."fst"$
  let _rule = rule(
    name: "E-FST",
    conclusion,
    premise,
  )
  prooftree(_rule)
}

#{
  let premise = $rho tack t_1 --> t_1^prime$
  let conclusion = $rho tack t_1."snd" --> t_1^prime."snd"$
  let _rule = rule(
    name: "E-SND",
    conclusion,
    premise,
  )
  prooftree(_rule)
}

#{
  prooftree(rule(
    name: "E-FSTAPP",
    $rho tack (v_1,v_2)."fst" --> v_1$,
  ))
}

#{
  prooftree(rule(
    name: "E-SNDAPP",
    $rho tack (v_1,v_2)."snd" --> v_2$,
  ))
}


#{
  let premise = $rho tack t_1 --> t_1^prime$
  let conclusion = $rho tack "if" t_1 <= eta "then" t_2 "else" t_3 --> "if" t_1^prime <= eta "then" t_2 "else" t_3$
  let _rule = rule(
    name: "E-IF1",
    conclusion,
    premise,
  )
  prooftree(_rule)
}

#{
  let premise = $rho tack t_2 --> t_2^prime$
  let conclusion = $rho tack "if" v_1 <= eta "then" t_2 "else" t_3 -->"if" v <= eta "then" t_2^prime "else" t_3$
  let _rule = rule(
    name: "E-IF2",
    conclusion,
    premise,
  )
  prooftree(_rule)
}

#{
  let premise = $rho tack t_3 --> t_3^prime$
  let conclusion = $rho tack "if" v_1 <= eta "then" v_2 "else" t_3 --> "if" v <= eta "then" v_2 "else" t_3^prime$
  let _rule = rule(
    name: "E-IF3",
    conclusion,
    premise,
  )
  prooftree(_rule)
}

#{
  let premise = $eta_1 <= eta_2$
  let conclusion = $rho tack "if" eta_1 <= eta_2 "then" v_1 "else" v_2 --> v_1$
  let _rule = rule(
    name: "E-IFTRUE",
    conclusion,
    premise,
  )
  prooftree(_rule)
}

#{
  let premise = $eta_1 > eta_2$
  let conclusion = $rho tack "if" eta_1 <= eta_2 "then" v_1 "else" v_2 --> v_2$
  let _rule = rule(
    name: "E-IFFALSE",
    conclusion,
    premise,
  )
  prooftree(_rule)
}

// #{
//   let premise = $rho \\[i mapsto v] tack t_1 --> t_1^prime$
//   let conclusion = $rho tack "for" i:r space t--> "for" i:r space t_1^prime$
//   let _rule = rule(
//     name: "E-FOR",
//     conclusion,
//     premise,
//   )
//   prooftree(_rule)
// }
#pagebreak()
#set align(left)
= Auxillary Definitions
$
  "length"(eta_0..eta_1) = eta_1 - eta_0 + 1
$

