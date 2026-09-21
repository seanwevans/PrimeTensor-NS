import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Fresh.Integral
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Fresh.Rescaled

/-!
# Classicalization: third-Fréchet fresh-tail quotient

The fixed-domain third-Fréchet fresh integral limit is now closed:

    ∫₀¹ D_a D_b D_c H_{h(1-u)}
      N(W(t+hu),W(t+hu))(x) du
      ⟶
    D³N(W(t),W(t))(x)[e_a,e_b,e_c].

The affine-rescaling checkpoint already proves, for every nonzero `h`,

    h⁻¹ • ∫ₜ^{t+h} thirdRetarded(t+h,s) ds
      =
    ∫₀¹ freshThirdFrechetRescaled(h,u) du.

Combining those two statements closes the normalized literal fresh tail.

No new estimate or reconstruction theorem is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelThirdFrechetFreshQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The normalized literal selected third-Fréchet fresh tail converges from
the right to the instantaneous forcing third-coordinate derivative. -/
theorem tendsto_inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechet_selectedRestart_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    let ec : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 c)
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          (∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
              ν (t + h) W W i a b c x s))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (iteratedFDeriv ℝ 3
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          x
          ![ea, eb, ec])) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  let ec : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 c)

  have hRescaled :=
    tendsto_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand_selectedRestart_zero_right
      hν U₀ hA hU₀ ht htR i a b c x

  have hRescaledPos :
      Tendsto
        (fun h : ℝ =>
          ∫ u in (0 : ℝ)..1,
            h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
              ν t h W i a b c x u)
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝
          (iteratedFDeriv ℝ 3
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W t) (W t) i)
            x
            ![ea, eb, ec])) := by
    exact
      hRescaled.mono_left
        (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)

  have hEq :
      (fun h : ℝ =>
        h⁻¹ •
          (∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
              ν (t + h) W W i a b c x s))
        =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ =>
        ∫ u in (0 : ℝ)..1,
          h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
            ν t h W i a b c x u) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact
      inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechet_eq_rescaled
        (ne_of_gt hh) W i a b c x

  exact
    Tendsto.congr'
      hEq.symm
      hRescaledPos

end

end Euclidean
end Bridge
end PrimeTensor
