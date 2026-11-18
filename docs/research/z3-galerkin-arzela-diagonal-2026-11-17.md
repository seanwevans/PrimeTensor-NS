# Genuine Z³ Galerkin diagonal Arzelà–Ascoli extraction

**Parent commit:** `6cbef8c70bba30e0fd4249c2062fae4acc9d6db0`

The verified finite Galerkin construction works on the common closed interval
\(I=[a,a+\tau]\), \(\tau=\log(10/9)/100\), with the strong complex Leray ODE,
\(W_{\log(9/5)}(u_S(t))\le100\), and 51000-Lipschitz temporal control.

This module formalizes the *first actual infinite-mode compactness extraction*.

1. **Arzelà–Ascoli time-curve class.** Let \(X\) be the three-component
   complex coefficient space and \(\mathcal A\subset C_b(I,X)\) consist of
   51000-Lipschitz curves with pointwise norm at most 100. Its closure in the
   supremum metric is compact: the target closed 100-ball is compact, and the
   common Lipschitz constant ensures equicontinuity.
2. **Countable product compactness.** The lattice \(\mathbb Z^3\) is
   countable, so the product of the compact time-curve closures is sequentially
   compact. A single strictly increasing \(\phi:\mathbb N\to\mathbb N\)
   yields convergence in every coordinate BCF supremum metric.
3. **Uniform time convergence.** The BCF distance bounds every pointwise
   distance. Hence for every fixed Fourier frequency \(n\) and \(\epsilon>0\),
   eventually \(\sup_{t\in I}\|u_{S_{\phi(k)}}(t,n)-g_n(t)\|<\epsilon\).
4. **Actual coefficients.** The coordinate map of a finite coefficient state
   is a norm-one evaluation; off-cutoff modes are zero. Thus its temporal
   Lipschitz constant and pointwise 100 bound follow from the genuine
   Galerkin envelope. The final theorem simultaneously *constructs the
   Galerkin curves* and extracts a common subsequence, with no hypothesis of
   preexisting convergence and no nesting assumption on the cutoffs.

**Exactly proved, if Lean verifies:** one strictly increasing subsequence with
uniform-in-time convergence for every fixed Fourier coefficient, under the
already-established strict initial analytic 100-ball and viscosity assumptions.

**Not yet proved:** (i) strong convergence of entire Fourier series in a
weighted Wiener topology using the `200(5/6)^N` fixed-core comparison,
(ii) convergence of the complete projected Leray convolution under expanding
cutoffs, (iii) the resulting infinite-frequency strong ODE/PDE solution,
(iv) any global H³ regularity or Clay Navier–Stokes conclusion. For nonlinear
passage, the cutoff family must exhaust the integer lattice and finite initial
data must approximate compatible infinite data. The current theorem deliberately
does not assume these facts.

The result introduces no axioms, admits, or surrogate ODE. It uses the pinned
mathlib results `BoundedContinuousFunction.arzela_ascoli`, `isCompact_univ_pi`,
and `IsCompact.tendsto_subseq`.
