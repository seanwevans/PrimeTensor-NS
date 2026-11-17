# Constructed finite Z³ Galerkin non-escape and speed certificate

**Parent commit**: `3bc4cce1da85c5fb6d1f13f757282995afbc42f3`

## Exact mathematical input

The previously constructed Picard solution obeys the *moving* Wiener mass
estimate

\[
W_{r_a(t)}(u_S(t)) \le 100,\qquad
r_a(t)=\log 2 -100(t-a),\qquad
0\le t-a\le\tau=\frac{\log(10/9)}{100}.
\]

Since every retained Fourier mode contributes a nonnegative summand
and the weight \(e^{r|n|_1}\ge1\) for \(r\ge0\), each retained coefficient
has norm at most 100. The real finite product space has the maximum norm,
so \(\|u_S(t)\|_{\mathrm{Pi}}\le100\), **independently of the support cardinality**.

Because \(r_a(t)\ge\log(9/5)\), the previously proved genuine full-Leray
source bound implies

\[
 W_{\log(3/2)}(F_S(u_S(t)))\le51000
\]

for \(0\le\mu\le 1/10\), with no output collision or cutoff factor.
The same weighted mode domination gives the **actual finite-state derivative bound**
\[\|u'_S(t)\|_{\mathrm{Pi}}=\|F_S(u_S(t))\|_{\mathrm{Pi}}\le51000.\]
This is the quantitative equicontinuity input needed to construct a terminal
state at a hypothetical finite maximal endpoint, before restarting Picard.
The continuous finite-dimensional Picard field is automatically time-Bochner
integrable on the local closed interval.

## What this does and does not prove

The module proves a **local non-escape and time-integrability certificate for
an actually constructed solution**, not merely a hypothetical path. Its
interval length can still depend on the finite set.

The missing research step is the genuine maximal-solution / extension theorem:
for a smooth autonomous vector field on a finite-dimensional real normed
space, a solution bounded as it approaches a finite terminal time extends.
Apply the non-escape certificate to every partial interval, argue that the
maximal endpoint cannot precede the common \(\tau\), and conclude the
cutoff-independent existence interval. This step is **not** an axiom or hidden
hypothesis in the current module.

This is an analytic-ball periodic Galerkin argument and does not prove
arbitrary-data global H³ Navier–Stokes continuation.

## Audit

No `sorry`, `admit`, `axiom`, or `native_decide`. Registry checks the
new Lean declarations and their axiom dependencies. The user environment
must compile the Lean module and run the project-wide audit before commit.
