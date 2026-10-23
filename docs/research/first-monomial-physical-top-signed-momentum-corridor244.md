# Signed physical momentum compact bound — 23 October 2026

Base: `aa0a6fdd` (`reduce compact temporal domination to physical momentum term bounds`).

## Mathematical advance

Previous local compact-test differentiation assumed an independent uniform
pointwise bound on **each** physical PDE term: the Laplacian, advection, and
pressure gradient. Such bounds are unnecessarily strong when the three terms
cancel. This increment controls only their signed sum:

\[
R_j(t,x)=\Delta u_j(t,x)-(u\cdot\nabla)u_j(t,x)-\partial_jp(t,x).
\]

By the actual preterminal PDE, \(R_j=\partial_tu_j\). If \(|R_j|\le C\) on a
short time neighborhood and the compact support of a weak test \(\phi_j\),
then the integrable spatial function \(C|\phi_j|\) dominates the temporal
derivative pairing. This implies the previously formalized scalar weak FTC,
selected/old weak–strong uniqueness, actual positive-time eighth raw Fourier
moments, and the necessary physical \(D_1\)-or-\(M_8\) escape alternative.

The previous independent termwise bounds imply the signed bound with constant
\(3C\); the reverse implication is not used or asserted.

## Fixed-time closure

The project already proves continuous spatial sections for \(\partial_tu_j\)
at every strict time, even without joint spacetime continuity. Compactness of
a weak-test support therefore gives \(C(t,\phi,j)<\infty\) bounding the signed
momentum RHS **at that one time**. This is proved without a high-frequency
pointwise derivative estimate. It does **not** supply a constant uniform over
nearby times, so it does not by itself close the weak FTC frontier.

## Why H³ does not automatically give pointwise second-derivative bounds

In three space dimensions an \(H^3\) estimate puts second derivatives in
\(H^1\), hence \(L^6\), but does not in general control their \(L^\infty\)
norm. Scaling a smooth compact solenoidal bump as
\(u_\varepsilon(x)=\varepsilon^{3/2}v(x/\varepsilon)\)
keeps its homogeneous \(H^3\) norm order one while its second derivative
supremum grows like \(\varepsilon^{-1/2}\). Accordingly, uniform compact
pointwise bounds require more than a bare local H³ norm ceiling.

## Remaining analytic frontier

Derive a compact-test weak-time FTC from locally uniform *spatial L²* or
weaker mixed-norm estimates on the signed physical projected right-hand side,
without assuming a time-uniform pointwise compact bound. Pressure cancellation
against solenoidal tests and the existing actual Fourier Leray source
identification should be exploited before estimating individual PDE terms.

All new terminal alternatives remain necessary/conditional statements, not
unconditional Navier–Stokes regularity.
