import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Frechet.Fresh.Integral
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Frechet.Fresh.Rescaled

/-!
# Classicalization: second-Fréchet fresh-tail quotient

The fixed-domain second-Fréchet fresh integral limit is now closed:

    ∫₀¹ D² H_{h(1-u)}
      N(W(t+hu),W(t+hu))(x)[e_b,e_a] du
      ⟶
    D² N(W(t),W(t))(x)[e_a,e_b].

The affine-rescaling checkpoint already proves, for every nonzero `h`,

    h⁻¹ • ∫ₜ^{t+h} D² K(t+h,s,x)[e_b,e_a] ds
      =
    ∫₀¹ freshSecondFrechetRescaled(h,u) du.

This file combines those two results.  Consequently the literal normalized
second-Fréchet fresh tail converges from the right to the instantaneous forcing
Hessian coordinate.

This closes the fresh contribution needed by the selected Duhamel
second-Fréchet right-quotient split.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelSecondFrechetFreshQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The normalized literal selected second-Fréchet fresh tail converges from
the right to the instantaneous forcing Hessian coordinate. -/
theorem tendsto_inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechet_selectedRestart_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          (∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
              ν (t + h) W W i x s eb ea))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (iteratedFDeriv ℝ 2
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          x
          ![ea, eb])) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  have hRescaled :=
    tendsto_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand_selectedRestart_zero_right
      hν U₀ hA hU₀ ht htR i a b x

  have hRescaledPos :
      Tendsto
        (fun h : ℝ =>
          ∫ u in (0 : ℝ)..1,
            h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand
              ν t h W i a b x u)
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝
          (iteratedFDeriv ℝ 2
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W t) (W t) i)
            x
            ![ea, eb])) := by
    exact
      hRescaled.mono_left
        (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)

  have hEq :
      (fun h : ℝ =>
        h⁻¹ •
          (∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
              ν (t + h) W W i x s eb ea))
        =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ =>
        ∫ u in (0 : ℝ)..1,
          h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand
            ν t h W i a b x u) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    dsimp only [ea, eb]
    exact
      inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechet_eq_rescaled
        (ne_of_gt hh) W i a b x

  exact
    Tendsto.congr'
      hEq.symm
      hRescaledPos

end

end Euclidean
end Bridge
end PrimeTensor
