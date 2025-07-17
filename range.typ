#import "@preview/curryst:0.5.1": prooftree, rule
= Grammar
== Base Type
$tau ::= sigma bar r$

$sigma ::= italic("float") bar sigma times sigma bar eta dot sigma$
== (Meta) Natural Number
$eta ::= 0 bar 1 bar ...$
== Ranges
$r::= eta..eta bar r dot r$

= Term
$t ::= l bar p bar x bar "for" i : l "in" t bar t."fst" bar t."snd" bar "let" x = t "in" t bar (t,t)$
== Literal
$l ::= "nat" bar "float"$

$"nat" = 0 bar 1 bar ...$

$"float" = 0.0 bar -4.21 bar 523.215 bar ...$
== Place Expression
$p::= x bar p[t] bar p angle.l t angle.r bar p."fst" bar p."snd"$

== Type Literal
$italic("rl") ::= "range"(eta,eta) bar italic("rl") dot "range"(eta,eta)$
= Environment
== Type Environment
$Gamma ::= bullet bar Gamma,(x:tau)$
== Kind Environment
$Delta ::= bullet$
- there are no contents to be used.



= Typing Rules
// utility to stack prems vertically
#let stack-premises(..premises) = align(center)[#premises.pos().join("\n")]
#let push-premises(..premises) = [#premises.pos().join("     ")]
#set align(center)

// T-LET
#let t_let_prems = (
  push-premises(
    $Delta;Sigma tack t:sigma$,
    $not exists tau^prime. Gamma(x)=tau^prime$,
  ),
  $Gamma;Sigma,(x:sigma) tack t_"body":sigma_"body"$,
)

#let t_let = rule(name: [T-LET], [$Sigma;Gamma tack "let" x=t "in" t_"body" : sigma_"body"$], [#stack-premises(
    ..t_let_prems,
  )])

#prooftree(t_let)

// T-SLICE
#let t-slice-prems = (
  $Delta;Gamma tack t : overline(eta_i dot sigma)$,
  push-premises(
    $Delta ; Gamma tack t_"range" : overline(eta_i^prime .. eta_i^#[$prime prime$])$,
    $overline(eta_i^#[$prime prime$]) <= overline(eta_i)$,
  ),
)
#let t-slice-conc = $Delta; Gamma tack t angle.l t_"range" angle.r : overline((eta_i^#[$prime prime$] - eta_i^prime + 1)) dot sigma$
#let t_slice = rule(name: [T-SLICE], [#t-slice-conc], [#stack-premises(..t-slice-prems)])
#prooftree(t_slice)

//T-INDEX-NAT
#let t-index-nat-prems = (
    $Delta;Gamma tack t:eta_1 dot sigma$,
    $Delta tack bracket.l.double italic("nat") bracket.r.double = eta_2$,
    $eta_1 > eta_2$
)
#let t-index-nat = rule(
    name: "T-INDEX-NAT",
    $Delta;Gamma tack t[italic("nat")] : sigma$,
    ..t-index-nat-prems
)
#prooftree(t-index-nat)