# Three-dimensional Jacobian of the actual real Schwartz dilation

**Base commit:** `8d35dbaf`.

The prior module constructed the real `SchwartzMap` dilation under every
positive scalar scale, with the exact directional chain rules through order
four. This checkpoint adds the *genuine Haar-volume change of variables*,
not a scalar profile surrogate.

`MeasureTheory.Measure.integral_comp_smul_of_nonneg` provides

    ∫ x, g (scale • x) = (scale ^ finrank ℝ V3)⁻¹ * ∫ x, g x.

The carrier `V3` is `EuclideanSpace ℝ (Axis Depth.three)`; its finrank is
proved to be three from the existing `axis_univ_three` theorem. Consequently

    ∫ x, g (scale • x) = (scale ^ 3)⁻¹ * ∫ x, g x.

Applying this identity to the squared real Schwartz components and their
actual directional derivatives gives precisely the five factors

    k = 0,1,2,3,4 : (scale^k)^2 * (scale^3)⁻¹.

The results establish the full analytic ingredients for L² derivative
energy and dissipation scaling on the Fourier Euclidean carrier. They DO
NOT yet add the coordinate sums into H³ energy, transfer the scaled
components through `h3SchwartzPoint3Scalar`, show solenoidality under
physical dilation, or derive the signed 243-slot monomial's scale⁴ law.
These are distinct subsequent steps.

Verification is deferred to the user's Lean 4/mathlib checkout. No `sorry`,
`admit`, new axioms or proof assumptions are used. Perform standalone
`lake env lean`, root/full build and the baseline audits before committing.
