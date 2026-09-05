import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.GlobalFubini

/-!
# Global product integrability of the selected Duhamel head kernel

The terminal-half kernel required the endpoint `9/4` machinery because its heat
lag degenerates as `s ↑ t`.

The complementary midpoint head is simpler.  On

    0 < s < t/2

the lag `t - s` stays strictly positive, while the selected restart-radius path
is uniformly bounded by `2 * A`.  The existing Fourier `L¹` forcing estimate
therefore gives a constant source-time majorant for the full frequency norm of
the retarded kernel.

Combining joint measurability, fixed-source-time Fourier integrability, and
that constant majorant gives genuine product integrability on

    (0,t/2) × H3FourierPoint3.

This is the only analytic input needed before applying the same unrestricted
Fubini swap already used for the terminal tail.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedHeadGlobalProduct
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected raw retarded kernel is globally product-integrable on the
positive-lag midpoint head `(0,t/2)`. -/
theorem h3SelectedDuhamelHeadComplexKernel_fubini_integrable_global
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (t / 2))).prod
        (volume : Measure H3FourierPoint3)) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (t / 2))

  let K : ℝ × H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelTailComplexKernel
      ν A t hν U₀ hA hU₀ i

  let P : ℝ → ℝ :=
    fun s =>
      ∫ ξ : H3FourierPoint3,
        ‖K (s, ξ)‖

  let M : ℝ :=
    h3NonlinearForcingL1Coefficient * (2 * A) * (2 * A)

  have hWb :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)

  have hWbound : ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    simpa only [
      W,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    ] using hWb.2 s

  have htwoA : 0 ≤ 2 * A := by
    positivity

  have hC : 0 ≤ h3NonlinearForcingL1Coefficient :=
    h3NonlinearForcingL1Coefficient_nonneg

  have hJoint :
      AEStronglyMeasurable
        K
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [K, μt]
    exact
      (measurable_h3SelectedDuhamelTailComplexKernel
        hν U₀ hA hU₀ i).aestronglyMeasurable

  have hPMeas :
      AEStronglyMeasurable P μt := by
    dsimp only [P]
    exact hJoint.norm.integral_prod_right'

  have hhalfNonneg : 0 ≤ t / 2 := by
    linarith

  have hMajorant :
      Integrable (fun _s : ℝ => M) μt := by
    dsimp only [μt]
    change
      IntegrableOn
        (fun _s : ℝ => M)
        (Set.Ioo (0 : ℝ) (t / 2))
        volume
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hhalfNonneg]
    exact intervalIntegrable_const

  have hPInt :
      Integrable P μt := by
    refine hMajorant.mono' hPMeas ?_
    dsimp only [μt]
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs

    have hst : s < t := by
      linarith [hs.2]

    have hτ : 0 < t - s :=
      sub_pos.mpr hst

    have hHeat :
        (∫ ξ : H3FourierPoint3,
            ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
              ν (t - s) (W s) (W s) i ξ‖)
          ≤
        h3RawFinLerayOuterProductDivergenceL1Mass
          (W s) (W s) i :=
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_norm_integral_le_L1Mass
        hν hτ (W s) (W s) i

    have hL1 :
        h3RawFinLerayOuterProductDivergenceL1Mass
            (W s) (W s) i
          ≤
        h3NonlinearForcingL1Coefficient * ‖W s‖ * ‖W s‖ :=
      h3RawFinLerayOuterProductDivergenceL1Mass_le
        (W s) (W s) i

    have hFirst :
        h3NonlinearForcingL1Coefficient * ‖W s‖
          ≤
        h3NonlinearForcingL1Coefficient * (2 * A) :=
      mul_le_mul_of_nonneg_left
        (hWbound s)
        hC

    have hSecond :
        h3NonlinearForcingL1Coefficient * ‖W s‖ * ‖W s‖
          ≤
        h3NonlinearForcingL1Coefficient * (2 * A) * (2 * A) :=
      mul_le_mul
        hFirst
        (hWbound s)
        (norm_nonneg _)
        (mul_nonneg hC htwoA)

    have hPnonneg : 0 ≤ P s := by
      dsimp only [P]
      exact integral_nonneg fun ξ => norm_nonneg _

    rw [Real.norm_eq_abs, abs_of_nonneg hPnonneg]

    calc
      P s
          =
        ∫ ξ : H3FourierPoint3,
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν (t - s) (W s) (W s) i ξ‖ := by
              rfl
      _ ≤
        h3RawFinLerayOuterProductDivergenceL1Mass
          (W s) (W s) i :=
        hHeat
      _ ≤
        h3NonlinearForcingL1Coefficient * ‖W s‖ * ‖W s‖ :=
        hL1
      _ ≤ M := by
        dsimp only [M]
        exact hSecond

  refine (integrable_prod_iff hJoint).2 ?_
  constructor

  · dsimp only [μt]
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs

    have hst : s < t := by
      linarith [hs.2]

    have hτ : 0 < t - s :=
      sub_pos.mpr hst

    dsimp only [K]
    unfold h3SelectedDuhamelTailComplexKernel
    exact
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_integrable
        hν hτ (W s) (W s) i

  · exact hPInt

end

end Euclidean
end Bridge
end PrimeTensor
