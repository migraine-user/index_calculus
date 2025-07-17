## Syntax:
### Base types
$\tau ::= \sigma \mid r$
$\sigma ::= \text{float}\mid \sigma \times \sigma \mid \eta \cdot \sigma$

### Natural numbers (Meta)
$\eta ::= 0 \mid 1 \mid ...$

### Ranges
$r ::= \eta..\eta \mid r \cdot r$

### Term
$t ::= l \mid p \mid x \mid \text{for } i : l\ \text{in}\ t \mid t.\text{fst} \mid t.\text{snd} \mid \text{let } x =t \text{ in } t \mid (t,t)$

$l ::= rr  \mid nat \mid float$

$rr::= \text{range}(\eta,\eta) \mid rr \cdot \text{range}(\eta,\eta)$

$nat = 0 \mid 1 \mid ...$
- $x$ and $i$ are just identifiers.

### Place expression
$p ::= x \mid p[t] \mid p\langle t \rangle \mid p.\text{fst}\mid p.\text{snd}$
### Type environment
$\Gamma ::= \bullet \mid \Gamma,(x:\tau)$
### Kind environment
$\Delta ::= \bullet \mid \Delta,(\alpha : \kappa)$
- a mapping from a literal nat / range to actual nats / ranges. There are no actual variables stored in $\Delta$ as of now.
## Typing Rules:


$$
\frac{
  \begin{array}{c}
    \Delta;\Gamma \vdash t : \sigma \\
    \neg\exists\tau^\prime.\Gamma(x)=\tau^\prime \\
    \Delta;\Gamma, (t : \sigma) \vdash  t_{body} : \sigma_{body}
  \end{array}
}{
  \Delta;\Gamma \vdash \text{let }x = t \text{ in } t_{body}
}
\text{T-LET}
$$

$$
\frac{
    \begin{array}{c}
        \Delta;\Gamma \vdash t:\overline {\eta_i} \cdot \sigma\\
        \Delta\vdash t_{range} : \overline{\eta_i^\prime..\eta_i^{\prime\prime}} \\
        {\overline\eta_i^{\prime\prime}} \leq{\overline\eta_j}
    \end{array}
}
{
    \Delta;\Gamma \vdash t\langle t_{range}\rangle : \overline{(\eta_i^{\prime\prime} - \eta_i^\prime+1)} \cdot \sigma 
}
\text{T-SLICE}
$$


$$
\frac{\begin{array}{c}
    \Delta;\Gamma\vdash t : \eta_1 \cdot \sigma \\ \eta_1 \gt \eta_2 \\
    \Delta\vdash[[nat]] = \eta_2
\end{array}}{
    \Delta;\Gamma\vdash t[nat]:\sigma 
}
\text{T-INDEX-NAT}
$$

$$
\frac{
    \begin{array}{c}
        \Delta;\Gamma \vdash t:\overline {\eta_i} \cdot \sigma\\
        \Delta\vdash t_{index} : \overline{\eta_i^\prime..\eta_i^{\prime\prime}} \\
        {\overline\eta_i^{\prime\prime}} \leq{\overline\eta_j}
    \end{array}
}
{
    \Delta;\Gamma \vdash t[t_{index}] : \sigma 
}
\text{T-INDEX-RANGE}
$$

$$
\frac{
    \Delta;\Gamma\vdash t:\sigma_1\times\sigma_2
}{\Delta;\Gamma\vdash t.\text{fst}:\sigma_1}
\text{T-FST}
$$

$$
\frac{
    \Delta;\Gamma\vdash t:\sigma_1\times\sigma_2
}{\Delta;\Gamma\vdash t.\text{snd}:\sigma_2}
\text{T-SND}
$$


$$
\frac{\begin{array}{c}
    \Delta \vdash [[rr_{iter}]] = r \\
    \Delta;\Gamma, (i:r)\vdash t_{body} : \sigma
\end{array}}{
    \Delta;\Gamma\vdash\text{for } i : rr_{iter}\ \text{in}\ t_{body}:r\cdot\sigma
}
\text{T-FOR}
$$

<!-- $$
\frac{\Delta \vdash [[l]] = r}{\Delta;\Gamma \vdash l : r}
\text{T-RANGE-LIT}
$$ -->
$$
\frac{}{\Delta;\Gamma \vdash float : \text{float}}\text{T-FLOAT-LIT}
$$

$$
\frac{\Delta;\Gamma \vdash v_1:\sigma_1\ \ \ \  \Delta;\Gamma \vdash v_2:\sigma_2}{\Delta;\Gamma \vdash (v_1,v_2) : \sigma_1 \times \sigma_2}\text{T-TUPLE-LIT}
$$

$$
\frac{\Delta \vdash [[rr]] = r}{
    \Delta;\Gamma\vdash rr : r
}
\text{T-RANGE-LIT}
$$

## Kinding rules

$$
\frac{\begin{array}{c}
\Delta \vdash [[l_1]] = \eta_1 &
\Delta \vdash [[l_2]] = \eta_2 &
\eta_1 \leq \eta_2
\end{array}}
{\Delta \vdash \text[[{range}(l_1,l_2)]] = \eta_1..\eta_2}
\text{K-RANGE-ONE}$$

$$
\frac{\begin{array}{c}
    \Delta \vdash [[rr_1]] = r_1 & \Delta \vdash [[rr_2]] = r_2
\end{array}}
{\Delta \vdash [[rr_1 \cdot rr_2]] = r_1 \cdot r_2 }
\text{K-RANGE-MUL}
$$


$$
\frac{}
{\Delta \vdash [[nat]] = \eta }
\text{K-NAT-LIT}
$$
