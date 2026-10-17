# Actual integrated 2-4-4 stability for 243 signed physical slots

Base: `09f7146e` — fix trilinear absolute difference inequality.

This module strengthens the earlier *pointwise* trilinear perturbation to the
exact **spatially integrated** estimate. For six real Schwartz functions,
linearity of the Bochner integral and coefficient-one real Hölder give

\[
\begin{aligned}
\left|\int abc-\int a'b'c'\right| \leq {}&
\|a-a'\|_2\|b\|_4\|c\|_4\\
&+\|a'\|_2\|b-b'\|_4\|c\|_4\\
&+\|a'\|_2\|b'\|_4\|c-c'\|_4.
\end{aligned}
\]

The norms are *actual real integral roots*, obtained from the previously
proved `realLpEnorm`-to-integral identities. All the integrals involved are
integrable by Schwartz pairing, including differences.

Applying this to the three jets of each actual physical slot yields the
unconditional estimate

\[
|M(f)-M(g)| \le 2\sum_{i,k,l,r,j}\mathcal E_{iklrj}(f,g),
\]

where `schwartzPhysicalSlotPerturbation244 f g p` is exactly the sum of
three positive 2-4-4 products of differences of the real derivatives.
There is no factor 243 outside the sum, and the physical energy-pairing
factor 2 is explicit.

**Scope:** The result compares two Schwartz profiles. The approximation
condition for an arbitrary physical H³ slice still requires constructing
strong derivative approximants and proving their signed products converge to
the canonical physical spatial-energy pairings. Neither follows from scalar
L² density alone, and this file does not assert it.
