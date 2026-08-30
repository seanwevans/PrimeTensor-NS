import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedOverlapGluing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Duhamel

/-!
# Classicalization: locality of the heat--Leray Duhamel term

Overlap uniqueness will be applied one elapsed time at a time.  For a target
time `q`, only the values of the nonlinear input paths on `[0,q]` can enter

    ∫₀^q K_{q-s}(U(s),V(s)) ds.

The globally defined physical extensions used elsewhere in the restart stack
are clamped after the endpoint of their own interval.  Consequently, when we
restrict the canonical restart to a shorter overlap interval, we need one
explicit locality theorem saying that those different post-endpoint
extensions cannot change the Duhamel value before the endpoint.

This file records that fact at two levels:

* pointwise locality of the retarded integrand;
* interval locality of the complete Duhamel integral.

No estimate or integrability argument is needed.  Equality follows directly
from equality of the two input paths on the integration interval.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-! ## Pointwise locality -/

/-- At one integration time, the retarded heat--Leray integrand depends only
on the two state values at that time. -/
theorem h3SpectralFinHeatLerayDuhamelIntegrand_congr_at
    {ν t s : ℝ}
    (hν : 0 < ν)
    {U₁ U₂ V₁ V₂ : ℝ → H3SpectralFinVectorState}
    (hU : U₁ s = U₂ s)
    (hV : V₁ s = V₂ s) :
    h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν U₁ V₁ s
      =
    h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν U₂ V₂ s := by
  unfold h3SpectralFinHeatLerayDuhamelIntegrand

  by_cases hs : 0 < t - s
  · rw [dif_pos hs, dif_pos hs, hU, hV]
  · rw [dif_neg hs, dif_neg hs]

/-! ## Interval locality -/

/-- The Duhamel value at a nonnegative target `t` is unchanged if both input
paths are replaced by paths agreeing with them throughout `[0,t]`.

In particular, the values of either replacement path after `t` are completely
irrelevant to the Duhamel value at `t`. -/
theorem h3SpectralFinHeatLerayDuhamel_congr_Icc
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    {U₁ U₂ V₁ V₂ : ℝ → H3SpectralFinVectorState}
    (hU :
      ∀ s : ℝ,
        s ∈ Set.Icc (0 : ℝ) t →
          U₁ s = U₂ s)
    (hV :
      ∀ s : ℝ,
        s ∈ Set.Icc (0 : ℝ) t →
          V₁ s = V₂ s) :
    h3SpectralFinHeatLerayDuhamel
        ν t hν U₁ V₁
      =
    h3SpectralFinHeatLerayDuhamel
        ν t hν U₂ V₂ := by
  unfold h3SpectralFinHeatLerayDuhamel

  apply intervalIntegral.integral_congr

  intro s hs

  have hsIcc :
      s ∈ Set.Icc (0 : ℝ) t := by
    simpa only [uIcc_of_le ht] using hs

  exact
    h3SpectralFinHeatLerayDuhamelIntegrand_congr_at
      hν
      (hU s hsIcc)
      (hV s hsIcc)

/-- Diagonal form used by the quadratic mild equation: replacing one path by
an equal path on `[0,t]` does not change the quadratic Duhamel term. -/
theorem h3SpectralFinHeatLerayDuhamel_self_congr_Icc
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    {U V : ℝ → H3SpectralFinVectorState}
    (hUV :
      ∀ s : ℝ,
        s ∈ Set.Icc (0 : ℝ) t →
          U s = V s) :
    h3SpectralFinHeatLerayDuhamel
        ν t hν U U
      =
    h3SpectralFinHeatLerayDuhamel
        ν t hν V V := by
  exact
    h3SpectralFinHeatLerayDuhamel_congr_Icc
      hν ht hUV hUV

end
end Euclidean
end Bridge
end PrimeTensor
