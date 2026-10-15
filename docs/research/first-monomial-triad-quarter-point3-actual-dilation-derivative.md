# Real Schwartz dilation: derivative bridge to spatial scaling

**Base checkpoint:** `b707f4f8`.

This Lean module constructs **actual** Schwartz components on the canonical
`EuclideanSpace ℝ (Axis Depth.three)` carrier under every positive isotropic
coordinate dilation `x ↦ scale • x`. It uses Mathlib's
`SchwartzMap.compCLMOfContinuousLinearEquiv` rather than a raw, untyped
function composition. The dilation equivalence uses a nonzero real unit.

Theorems prove the pointwise pullback identity and exact scaling of each
ordered directional derivative through fourth order:

    ∂ₘ (f ∘ dilation_scale) = scale · (∂ₘ f) ∘ dilation_scale
    ∂ₘ∂ₙ (...) = scale² · (∂ₘ∂ₙ f) ∘ dilation_scale
    ∂ₘ∂ₙ∂ₚ (...) = scale³ · (...) ∘ dilation_scale
    ∂ₘ∂ₙ∂ₚ∂q (...) = scale⁴ · (...) ∘ dilation_scale

All three velocity components are packaged by pointwise dilation. This
module does **not yet** claim volume-Jacobian scaling for integrals,
physical Point3 derivative correspondence, preservation of divergence in
the physical carrier, or the full cubic monomial's `scale^4` equality.
Those obligations are next, beginning with the change-of-variables formula.

This patch does not prove the uniform critical-half coefficient bound for
all solenoidal Schwartz shapes. Lean compilation is unverified during
artifact preparation; run the standalone Lean file, full project build,
and baseline audit before committing.
