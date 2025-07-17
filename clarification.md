## For
$$
\frac{\begin{array}{c}
    \Delta \vdash [[rr_{iter}]] = r \\
    \Delta;\Gamma, (i:r)\vdash t_{body} : \sigma
\end{array}}{
    \Delta;\Gamma\vdash\text{for } i : rr_{iter}\ \text{in}\ t_{body}:r\cdot\sigma
}
\text{T-FOR}
$$

This rule lets you do something like:
```ml
for i : range(0,5) . range(0,5) . range(0.5) in 4.2
```
and it evaluates to a value of type 3d array with 5 elements each.

## Indexing by range
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

This rule is useful because what you might want to do is
```ml
for ij : range(0,5) . range(0,5) in for k : range(0,5) in a[0][ij][k]
```
And this expression is analogous to:
```python
for i in range(5):
    for j in range(5):
        for k in range(5):
            a[0][i][j][k]
```
The type resulting from this is `5.5.5.?` where `?` is whatever the type of `a[0][0][0][0]` is.
