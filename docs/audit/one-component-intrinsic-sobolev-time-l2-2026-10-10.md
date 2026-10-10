# Intrinsic physical Ḣ^(3/2) seminorm in time L² (2026-10-10)

Parent checkpoint: `bbeefdd8` — `formalize physical homogeneous H3/2 Fourier Sobolev membership`.

## Closed internal analytic interfaces

`OneComponentPhysicalHomogeneousSobolev.lean` defined the actual *physical*
Fourier–Sobolev membership predicate for `f : H3ScalarL2`: existence of a real
Euclidean physical L² field whose Fourier transform equals
`((2π)²‖ξ‖²)^(3/4) * 𝓕(f)` almost everywhere. It proved uniqueness of the
real L² derivative. No claim about unrelated spaces of distributions was made.

`OneComponentIntrinsicSobolevTimeL2.lean` now constructs the canonical real
fractional derivative for any `f` satisfying that predicate, proves that any
other witness agrees with it, and defines its *physical Sobolev seminorm* as
the real L² norm. For a genuine strict-time velocity snapshot the canonical
seminorm is exactly the norm of the real fractional derivative from `7ef2f8e3`.

The time profile is zero-extended off `(0,T)` and inherits its exact Fourier
energy identity, global Borel measurability, and strict-preterminal time
continuity, without hypothesizing an arbitrary measurable proxy.

One physical curl-component **strong H³ endpoint** and the existing H³ energy
class then produce a common strict terminal interval `(c,T)` on which both
transverse intrinsic physical Ḣ^(3/2) seminorm profiles belong to `L²_t`.
The positive complementary component alone supplies a single-component
analytic criterion; the negative component is extra information.

## Honest remaining bridges

The Liu–Zhang theorem is about a *local strong solution* of the genuine
3-D incompressible Navier–Stokes equations and an admissible unit-vector
projection `u·β(t)` on `[0,T]`. It says that finite
`∫₀ᵀ ‖u(t)·β(t)‖_{Ḣ^(3/2)}² dt` implies continuation.

Reference: Yanlin Liu and Ping Zhang, *On the One Time-Varying Component
Regularity Criteria for 3-D Navier–Stokes Equations*, SIAM J. Math. Anal.
56 (2024), 6213–6231, DOI 10.1137/23M1623124.
https://doi.org/10.1137/23M1623124

The present patch does **not** formalize the paper's distributional homogeneous
Sobolev-space definition, its local strong-solution class and PDE eligibility,
its translation to this repository's `SmoothContinuationExtension`, or an
application on a shifted terminal interval. The paper's external continuation
theorem has not been imported/proved in Lean. The physical-curl strong H³
endpoint is an explicit hypothesis, not a property of all admissible paths.

No conclusion of unconditional Navier–Stokes global regularity is drawn.
