# Hermitian compact spectral H3 density (baseline d7928545)

## Precise analytic input and construction

The earlier smooth-compact density theorem approximates an arbitrary weighted
H3 Fourier L2 scalar with a genuine smooth, compact-frequency complex
representative, but does not preserve Fourier reality. The previous
`FullThirdHermitianTransverseCutoff` theorem proves that an **input-Hermitian**
Schwartz vector becomes real-solenoidal after bounded Leray projection, so
this input-reality issue is the missing nonconditional step.

This module defines the real-linear L2 reflection-conjugation map
`J F(ξ) = conj (F(-ξ))` and the bounded real-linear average
`P = (Id + J)/2`. The imported Fourier reflection and complex-conjugation
CLMs supply continuity and their a.e. representative identities. A direct
conjugation-involution proof shows P fixes every Hermitian state.

Given smooth compact g, form `g_sym(ξ) = (g(ξ) + conj(g(-ξ)))/2`.
The file proves `g_sym` has smooth compact support, exact pointwise Fourier
reality, and, crucially, `P(g.toLp) = g_sym.toLp` in the actual L2 carrier.
Using the bounded operator norm of P gives quantitative density of
Hermitian compact-smooth Schwartz vectors in the Hermitian weighted H3 state.
The constant is `‖P‖ + 1`; no unjustified isometric projection estimate is
introduced.

## Main new bridge

For a raw-Hermitian weighted H3 velocity U, each of its three weighted
Fourier components has a Hermitian smooth compact approximation in the
actual weighted L2 topology. A finite-product sup-norm bound gives genuine
three-component strong approximation. When U is also Fourier-divergence-free,
apply the previously constructed bounded spectral Leray multiplier.
Every result is Fourier divergence-free, raw-Hermitian, and has the exact real
L2 decoder. The weighted H3 error is bounded by six times the compact
Hermitian approximation error, so arbitrarily small errors follow without a
separate density axiom.

## Exact scope and next mathematical frontier

Although each **input** spectral Schwartz representative has smooth compact
frequency support, its image under the frequency-dependent Leray projection
need not be Schwartz at ξ=0. In particular, the new density theorem is
**spectral density**, not yet density by genuine real divergence-free
physical Schwartz velocities. The existing physical construction in
`FullThirdCompactHermitianSolenoidalSchwartz` uses smooth localization and a
polynomial transverse numerator, but that numerator introduces a factor
`|ξ|²` and the Hermitianization introduces a factor 2 on transverse states.

The next analytic step must build **annular** cutoff approximants, use the
normalized transverse projector away from zero, and prove strong weighted-H3
convergence, then transfer exact physical Schwartz derivative jets to the
canonical signed-flux completion. Only after that can the longitudinal
correction be removed along the actual completion sequence.

No Navier-Stokes global regularity assertion follows from this module alone.
