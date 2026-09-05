import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Selected.Frozen.Primitive

/-!
# Selected quarter-Hölder forcing: frozen terminal primitive mass

`Forcing.SelectedFrozenPrimitive` integrates the second heat moment in lag at
fixed frequency.  This file multiplies that primitive by the forcing frozen at
the terminal state and then integrates in frequency.

The point is to spend only the already available Fourier `L¹` mass of the
frozen forcing.  The resulting budget is

    ((2π)^2 ν)⁻¹ * 4 * C_L1 * A^2,

with no terminal-lag singularity and no division by the frequency.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedFrozenMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- After evaluating the fixed-frequency heat primitive explicitly, its
product with the frozen selected forcing is frequency-integrable and bounded
by viscosity inverse times the frozen forcing `L¹` mass. -/
theorem h3RawFinLerayOuterProductDivergence_frozenSecondMomentPrimitive_explicit_frequencyIntegral_le_selectedRestart
    {ν A T t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hT : 0 ≤ T)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (∫ ξ : H3FourierPoint3,
        (((2 * Real.pi) ^ 2 * ν)⁻¹) *
          (1 - Real.exp
            (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))) *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
      ≤
    (((2 * Real.pi) ^ 2 * ν)⁻¹) *
      (4 * h3NonlinearForcingL1Coefficient * A ^ 2) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let cInv : ℝ := ((2 * Real.pi) ^ 2 * ν)⁻¹

  have hc : 0 < (2 * Real.pi) ^ 2 * ν := by
    positivity

  have hcInv0 : 0 ≤ cInv := by
    dsimp only [cInv]
    exact inv_nonneg.mpr hc.le

  have hRawInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (h3RawFinLerayOuterProductDivergence_integrable (W t) (W t) i).norm

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          cInv *
            ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRawInt.const_mul cInv

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          cInv *
            (1 - Real.exp
              (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))) *
            ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    have hFactor :
        AEStronglyMeasurable
          (fun ξ : H3FourierPoint3 =>
            cInv *
              (1 - Real.exp
                (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))))
          (volume : Measure H3FourierPoint3) := by
      exact (by fun_prop : Continuous (fun ξ : H3FourierPoint3 =>
        cInv *
          (1 - Real.exp
            (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))))).aestronglyMeasurable
    exact hFactor.mul hRawInt.aestronglyMeasurable

  have hTargetInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          cInv *
            (1 - Real.exp
              (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))) *
            ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajorantInt.mono' hTargetMeas ?_
    filter_upwards with ξ

    have hprod :
        0 ≤ (2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2 := by
      positivity

    have hexpLe :
        Real.exp
            (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))
          ≤ 1 := by
      calc
        Real.exp
            (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))
            ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (neg_nonpos.mpr hprod)
        _ = 1 := Real.exp_zero

    have hSub0 :
        0 ≤ 1 - Real.exp
          (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2)) :=
      sub_nonneg.mpr hexpLe

    have hFactor0 :
        0 ≤ cInv *
          (1 - Real.exp
            (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))) :=
      mul_nonneg hcInv0 hSub0

    have hFactorLe :
        cInv *
            (1 - Real.exp
              (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2)))
          ≤ cInv := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left
          (sub_le_self 1
            ((Real.exp_pos
              (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))).le))
          hcInv0)

    have hTarget0 :
        0 ≤
          cInv *
            (1 - Real.exp
              (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))) *
            ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ :=
      mul_nonneg hFactor0 (norm_nonneg _)

    have hMajorant0 :
        0 ≤
          cInv *
            ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ :=
      mul_nonneg hcInv0 (norm_nonneg _)

    have hBound :
        cInv *
            (1 - Real.exp
              (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))) *
            ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖
          ≤
        cInv *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ :=
      mul_le_mul_of_nonneg_right hFactorLe (norm_nonneg _)

    simpa only [Real.norm_eq_abs, abs_of_nonneg hTarget0,
      abs_of_nonneg hMajorant0] using hBound

  have hIntegralLe :
      (∫ ξ : H3FourierPoint3,
          cInv *
            (1 - Real.exp
              (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))) *
            ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        cInv *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := by
    refine integral_mono_ae hTargetInt hMajorantInt ?_
    filter_upwards with ξ

    have hFactorLe :
        cInv *
            (1 - Real.exp
              (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2)))
          ≤ cInv := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left
          (sub_le_self 1
            ((Real.exp_pos
              (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))).le))
          hcInv0)

    exact
      mul_le_mul_of_nonneg_right hFactorLe (norm_nonneg _)

  have hMass :=
    h3RawFinLerayOuterProductDivergenceL1Mass_selectedRestart_le
      hν U₀ hA hU₀ t i

  calc
    (∫ ξ : H3FourierPoint3,
        (((2 * Real.pi) ^ 2 * ν)⁻¹) *
          (1 - Real.exp
            (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))) *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        cInv *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := by
      simpa only [cInv] using hIntegralLe
    _ =
      cInv *
        h3RawFinLerayOuterProductDivergenceL1Mass (W t) (W t) i := by
      unfold h3RawFinLerayOuterProductDivergenceL1Mass
      rw [integral_const_mul]
    _ ≤
      cInv *
        (4 * h3NonlinearForcingL1Coefficient * A ^ 2) :=
      mul_le_mul_of_nonneg_left hMass hcInv0
    _ =
      (((2 * Real.pi) ^ 2 * ν)⁻¹) *
        (4 * h3NonlinearForcingL1Coefficient * A ^ 2) := by
      rfl

/-- The actual fixed-frequency time primitive, before substituting its closed
form, has the same selected frozen-forcing frequency budget. -/
theorem h3RawFinLerayOuterProductDivergence_frozenSecondMomentPrimitive_frequencyIntegral_le_selectedRestart
    {ν A T t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hT : 0 ≤ T)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (∫ ξ : H3FourierPoint3,
        (∫ q in (0 : ℝ)..T,
          ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν q ξ‖) *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
      ≤
    (((2 * Real.pi) ^ 2 * ν)⁻¹) *
      (4 * h3NonlinearForcingL1Coefficient * A ^ 2) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  calc
    (∫ ξ : H3FourierPoint3,
        (∫ q in (0 : ℝ)..T,
          ‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν q ξ‖) *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        (((2 * Real.pi) ^ 2 * ν)⁻¹) *
          (1 - Real.exp
            (-((2 * Real.pi) ^ 2 * ν * T * ‖ξ‖ ^ 2))) *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [h3HeatFourierSymbol_secondMoment_timeIntegral_eq hν hT ξ]
    _ ≤
      (((2 * Real.pi) ^ 2 * ν)⁻¹) *
        (4 * h3NonlinearForcingL1Coefficient * A ^ 2) := by
      dsimp only [W]
      exact
        h3RawFinLerayOuterProductDivergence_frozenSecondMomentPrimitive_explicit_frequencyIntegral_le_selectedRestart
          hν U₀ hA hU₀ hT i

end

end Euclidean
end Bridge
end PrimeTensor
