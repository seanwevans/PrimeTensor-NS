# Native mixed sixth-flux: asymmetric Fourier Young estimate

Base: `9cf8520ae7e03e71232abf57db67bfb0e2b386d3` — bound native mixed lowmaximum sixth flux by finite radial budgets.

## Hard analytic step

The integrated native sixth-flux polarization telescope of `edb0317f3` is an EXACT signed three-term identity. Its radius-six contraction estimate of `9cf8520ae` leaves three mixed budgets. They are not diagonal in the three Fourier polarizations; applying the previous diagonal triad estimate without an argument would be invalid.

Here a genuinely asymmetric real Fourier Young inequality is proved. Let `S` be any measurable sector of the actual six-dimensional conserving pair plane, let `K` be integrable, and let `F²,W²,H` be integrable with `H≥0`. If on `S`:

    K(p,r) ≤ F(p) W(r) H(-(p+r)),

then the measure-preserving triad rearrangement and the pointwise elementary square inequality imply

    ∫_S K ≤ (1/2) ( ∫ F² + ∫ W² ) (∫ H).

The proof does NOT invoke an invalid `L² × L² × L² -> L¹` whole-space convolution estimate. A second theorem retains the free balancing parameter `λ>0`:

    ∫_S K ≤ (1/2) ( λ² ∫ F² + λ⁻² ∫ W² ) (∫ H).

This reciprocal scaling matters when one outer argument is a small difference and the other is merely bounded.

## Actual mixed complex flux

For three possibly unrelated complex Fourier polarizations `P,Q,W`, write `a_P(ξ)` for the native Euclidean complex polarization norm of `P(ξ)`.

On the EXACT low-maximum sector, all three conserving ordinary Fourier radii lie below `2(R+1)` (the project's normalized gradient threshold contains `2π`). The native mixed contraction budget satisfies the pointwise bound

    B₆(P,Q,W)(p,r)
      ≤ 3 [2(R+1)] a_P(p) a_Q(-(p+r)) a_W(r).

The three contraction terms are handled with the repository's **complex bilinear** polarization dot Cauchy estimate, the Euclidean mixed frequency contraction bound, and the strict common-radius property. There is no Hermitian conjugation or polarization identification.

Thus, under explicitly stated global integrability of the mixed budget, outer squared Fourier amplitudes and middle Fourier `L¹` amplitude:

    ∫_LowMax(R) B₆(P,Q,W)
      ≤ 3 [2(R+1)] (∫ a_P² + ∫ a_W²)/2 · ∫ a_Q.

The scaled version replaces the numerator by `λ² ∫ a_P² + λ⁻² ∫ a_W²`. Composing this with the previous `3[2(R+1)]⁶` coefficient yields a polynomial cutoff cost of order `[2(R+1)]⁷` for the mixed low-maximum sixth-flux budget.

## Boundary of the claim

The module does not yet discharge global mixed-budget integrability from arbitrary spectral states or identify the real solenoidal Schwartz Fourier polarizations with their native weighted `H³` representatives in the mixed arguments. Those are the next concrete source-to-Fourier transfer steps. The conditional integral estimates preserve all original physical kinetic-gap witnesses and do not assert near-terminal signed-flux freezing or global regularity.

## Seventh-order bound for the actual flux

`thirdFullKinetic_lowMax_mixedFlux_le_scaledL2L2L1244` composes the mixed Young budget with the native signed six-symbol radius-six coefficient estimate:

    ∫_LowMax(R) |F₆(P,Q,W)|
       ≤ 9 [2(R+1)]⁷
           * (λ² ∫ a_P² + λ⁻² ∫ a_W²)/2
           * ∫ a_Q.

The integrated mixed flux, global mixed contraction budget, the two outer squared amplitudes and the middle amplitude must be integrable as stated in the Lean theorem. Neither spectral representation nor integrability is silently inferred. This bound may be used independently for each of the three exact mixed telescope summands, with independent `λ` choices.
