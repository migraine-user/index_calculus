#import "@preview/curryst:0.5.1": prooftree, rule
= Grammar
== Base Type
$tau ::= sigma bar r$

$sigma ::= italic("float") bar sigma times sigma bar eta dot sigma$
== (Meta) Natural Number
$eta ::= 0 bar 1 bar ...$
== Range
$r::= eta..eta bar r dot r$
= Term
$t ::= l bar p bar x bar "for" i : l "in" t bar t."fst" bar t."snd" bar "let" x = t "in" t bar (t,t)$
== Literal
$l ::= "nat" bar "float"$

$"nat" = 0 bar 1 bar ...$

$"float" = 0.0 bar -4.21 bar 523.215 bar ...$
== Range Literal
$"rl" ::= "range"("nat","nat") bar "range"("nat","nat") dot "rl"$

== Place Expression
$p::= x bar p[t] bar p angle.l t angle.r bar p."fst" bar p."snd"$


= Environment
== Type Environment
$Gamma ::= bullet bar Gamma,(x:tau)$
== Kind Environment
$Delta ::= bullet$
- there are no contents to be used.



= Typing Rules
// Utility for declarative premise stacking
#let push-premises(premises: array) = {
  grid(
    columns: premises.len(),
    column-gutter: 1em,
    row-gutter: .5em,
    align: center,
    ..premises
  )
}

#let stack-premises(premises: array) = {
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
    ..stacked
  )
}
#set align(center)

// T-LET
#{
  let premises = (
    (
      $Delta;Gamma tack t:sigma$,
      $not exists tau. Gamma(x)=tau$,
    ),
    $Delta;Gamma,(x:sigma) tack t_"body":sigma_"body"$,
  )
  let conclusion = $Delta;Gamma tack "let" x=t "in" t_"body" : sigma_"body"$

  let _rule = rule(name: [T-LET], conclusion, stack-premises(
    premises: premises,
  ))

  prooftree(_rule)
}

// T-FOR
#{
  let premises = (
    $Gamma tack bracket.l.double "rl" bracket.r.double = r$,
    $Delta;Gamma,(i:r) tack t_"body" : sigma$,
  )
  let conclusion = $Delta;Gamma tack "for" i: "rl" "in" t_"body" : r dot sigma$
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
    $Delta;Gamma tack t : overline(eta_i dot sigma)$,
    (
      $Delta ; Gamma tack t_"range" : overline(eta_i^prime .. eta_i^#[$prime prime$])$,
      $overline(eta_i^#[$prime prime$]) <= overline(eta_i)$,
    ),
  )
  let conclusion = $Delta; Gamma tack t angle.l t_"range" angle.r : overline((eta_i^#[$prime prime$] - eta_i^prime + 1)) dot sigma$
  let _rule = rule(name: [T-SLICE], conclusion, stack-premises(premises: premises))
  prooftree(_rule)
}


//T-INDEX-NAT
#{
  let premises = (
    $Delta;Gamma tack t:eta_1 dot sigma$,
    $Delta tack bracket.l.double italic("nat") bracket.r.double = eta_2$,
    $eta_1 > eta_2$,
  )
  let conclusion = $Delta;Gamma tack t[italic("nat")] : sigma$
  let _rule = rule(
    name: "T-INDEX-NAT",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}



// T-INDEX-RANGE
#{
  let premises = (
    $Delta; Gamma tack t : overline(eta_i) dot sigma$,
    $Delta tack t_"index" : overline(eta_i^prime..eta_i^#[$prime prime$])$,
    $overline(eta_i^#[$prime prime$]) <= overline(eta_i)$,
  )
  let conclusion = $Delta;Gamma tack t[t_"index"]: sigma$
  let _rule = rule(
    name: "T-INDEX-RANGE",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}

// T-FST
#{
  let premise = $Delta;Gamma tack t:sigma_1 times sigma_2$
  let conclusion = $Delta;Gamma tack t."fst":sigma_1$
  let _rule = rule(
    name: "T-FST",
    conclusion,
    premise,
  )
  prooftree(_rule)
}

// T-SND
#{
  let premise = $Delta;Gamma tack t:sigma_1 times sigma_2$
  let conclusion = $Delta;Gamma tack t."snd":sigma_2$
  let _rule = rule(
    name: "T-SND",
    conclusion,
    premise,
  )
  prooftree(_rule)
}

// T-RANGE-LIT
// #{
//   let premise = $Delta tack bracket.l.double r l bracket.r.double = r$
//   let conclusion = $Delta; Gamma tack r l : r$
//   let _rule = rule(
//     name: "T-RANGE-LIT",
//     conclusion,
//     premise,
//   )
//   prooftree(_rule)
// }

// T-FLOAT-LIT
#{
  let conclusion = $Delta;Gamma tack "float": italic("float")$
  let _rule = rule(
    name: "T-FLOAT-LIT",
    conclusion,
  )
  prooftree(_rule)
}

// T-TUPLE-LIT
#{
  let premises = (
    $Delta;Gamma tack t_1: sigma_1$,
    $Delta;Gamma tack t_2: sigma_2$,
  )
  let conclusion = $Delta;Gamma tack (t_1,t_2) : sigma_1 times sigma_2$
  let _rule = rule(
    name: "T-TUPLE-LIT",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}



#align(left)[= Kinding rules]
// K-NAT-LIT
#{
  prooftree(rule(
    name: "K-NAT-LIT",
    $Delta tack bracket.l.double "nat" bracket.r.double = eta$,
  ))
}
// K-RANGE-ONE
#{
  let premises = (
    $Delta tack bracket.l.double "nat"_1 bracket.r.double= eta_1$,
    $Delta tack bracket.l.double "nat"_2 bracket.r.double= eta_2$,
    $eta_1 <= eta_2$,
  )
  let conclusion = $Delta tack bracket.l.double "range"("nat"_1, "nat"_2) bracket.r.double = eta_1 .. eta_2$
  let _rule = rule(
    name: "K-RANGE-ONE",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}
// K-RANGE-MUL
#{
  let premises = (
    $Delta tack bracket.l.double "rl"_1 bracket.r.double = r_1$,
    $Delta tack bracket.l.double "rl"_2 bracket.r.double = r_2$,
  )
  let conclusion = $Delta tack bracket.l.double "rl"_1 dot "rl"_2 bracket.r.double= r_1 dot r_2$
  let _rule = rule(
    name: "K-RANGE-MUL",
    conclusion,
    ..premises,
  )
  prooftree(_rule)
}
