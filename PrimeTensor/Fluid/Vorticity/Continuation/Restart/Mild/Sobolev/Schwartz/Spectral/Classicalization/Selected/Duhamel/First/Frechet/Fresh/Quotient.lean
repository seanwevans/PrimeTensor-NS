import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.First.Frechet.Fresh.Integral
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.First.Frechet.Fresh.Rescaled

/-!
# Classicalization: first-Fréchet fresh-tail quotient

The fixed-domain first-Fréchet fresh integral limit is now closed:

    ∫₀¹ D_a H_{h(1-u)}
      N(W(t+hu),W(t+hu))(x) du
      ⟶
    D_a N(W(t),W(t))(x).

The affine-rescaling checkpoint already proves, for every nonzero `h`,

    h⁻¹ • ∫ₜ^{t+h} D_a K(t+h,s,x) ds
      =
    ∫₀¹ freshFrechetRescaled(h,u) du.

This file combines those two results.  Consequently the literal normalized
first-Fréchet fresh tail converges from the right to the instantaneous forcing
coordinate derivative.

This closes the fresh contribution needed by the selected Duhamel
first-Fréchet right-quotient split.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFirstFrechetFreshQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The normalized literal selected first-Fréchet fresh tail converges from the
right to the instantaneous forcing derivative in the chosen coordinate
direction. -/
theorem tendsto_inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechet_selectedRestart_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          (∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
              ν (t + h) W W i x s ea))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        ((fderiv ℝ
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W t) (W t) i)
            x) ea)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  have hRescaled :=
    tendsto_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand_selectedRestart_zero_right
      hν U₀ hA hU₀ ht htR i a x

  have hRescaledPos :
      Tendsto
        (fun h : ℝ =>
          ∫ u in (0 : ℝ)..1,
            h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
              ν t h W i a x u)
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝
          ((fderiv ℝ
              (h3RawFinLerayOuterProductDivergenceC0Representative
                (W t) (W t) i)
              x) ea)) := by
    exact
      hRescaled.mono_left
        (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)

  have hEq :
      (fun h : ℝ =>
        h⁻¹ •
          (∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
              ν (t + h) W W i x s ea))
        =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ =>
        ∫ u in (0 : ℝ)..1,
          h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
            ν t h W i a x u) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    dsimp only [ea]
    exact
      inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechet_eq_rescaled
        (ne_of_gt hh) W i a x

  exact
    Tendsto.congr'
      hEq.symm
      hRescaledPos

end

end Euclidean
end Bridge
end PrimeTensor
