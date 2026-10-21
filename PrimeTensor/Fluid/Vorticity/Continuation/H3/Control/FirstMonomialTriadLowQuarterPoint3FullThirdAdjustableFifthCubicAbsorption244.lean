import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGlobalFifthCubicAbsorption244
import Mathlib.Tactic

/-!
# Adjustable signed fifth-moment absorption against cubic Leray forcing

The strict-time Fourier PDE supplies the exact signed identity

  D₃' = -2 M₅ + F_global,

where the full-space absolute transfer controls F_global. Rather than spend
exactly one fifth-moment share, a positive Young parameter ε gives

  G ≤ ε M₅ + ε⁻¹ M₃,
  D₃' + (2 - ε) M₅ ≤ ε⁻¹ M₃.

The parameter is unrestricted except ε > 0. For 0 < ε < 2 the signed PDE
retains strictly positive viscous dissipation. This interpolation does NOT
improve the best forcing-fraction threshold M₃/M₅ = 1 obtained at ε=1:
ε(2-ε) ≤ 1. Its value is allowing a selectable viscous share when separate
forcing envelopes are available. No terminal integrability is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeAdjustableFifthCubic244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Adjustable square-completion, with exact q⁵ and q³ Fourier weights.
The parameter must be strictly positive to invert it. -/
theorem h3_globalForcingTwoMoment_pointwise_adjustable244
    (ε q : ℝ) (hε : 0 < ε) (hq : 0 ≤ q) (z f : ℂ) :
    2 * q ^ 4 * |(inner ℂ z f).re| ≤
      ε * (q ^ 5 * ‖z‖ ^ 2) + ε⁻¹ * (q ^ 3 * ‖f‖ ^ 2) := by
  have hRe : |(inner ℂ z f).re| ≤ ‖z‖ * ‖f‖ := by
    calc
      |(inner ℂ z f).re| ≤ ‖inner ℂ z f‖ :=
        Complex.abs_re_le_norm _
      _ ≤ ‖z‖ * ‖f‖ := norm_inner_le_norm z f
  have hWeight : 0 ≤ 2 * q ^ 4 := by positivity
  have hBound :
      ε * (2 * q ^ 4 * |(inner ℂ z f).re|) ≤
        ε * (2 * q ^ 4 * (‖z‖ * ‖f‖)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hRe hWeight) hε.le
  have hSquare :
      0 ≤ q ^ 3 * (ε * q * ‖z‖ - ‖f‖) ^ 2 :=
    mul_nonneg (pow_nonneg hq 3) (sq_nonneg _)
  have hIdentity :
      ε ^ 2 * (q ^ 5 * ‖z‖ ^ 2) + q ^ 3 * ‖f‖ ^ 2 -
          ε * (2 * q ^ 4 * (‖z‖ * ‖f‖)) =
        q ^ 3 * (ε * q * ‖z‖ - ‖f‖) ^ 2 := by
    ring
  have hScaled :
      ε * (2 * q ^ 4 * |(inner ℂ z f).re|) ≤
        ε ^ 2 * (q ^ 5 * ‖z‖ ^ 2) + q ^ 3 * ‖f‖ ^ 2 := by
    linarith only [hBound, hSquare, hIdentity]
  have hScaledRight :
      (2 * q ^ 4 * |(inner ℂ z f).re|) * ε ≤
        ε ^ 2 * (q ^ 5 * ‖z‖ ^ 2) + q ^ 3 * ‖f‖ ^ 2 := by
    calc
      (2 * q ^ 4 * |(inner ℂ z f).re|) * ε =
          ε * (2 * q ^ 4 * |(inner ℂ z f).re|) := by ring
      _ ≤ _ := hScaled
  calc
    2 * q ^ 4 * |(inner ℂ z f).re| ≤
        (ε ^ 2 * (q ^ 5 * ‖z‖ ^ 2) + q ^ 3 * ‖f‖ ^ 2) / ε :=
      (le_div_iff₀ hε).2 hScaledRight
    _ = ε * (q ^ 5 * ‖z‖ ^ 2) + ε⁻¹ * (q ^ 3 * ‖f‖ ^ 2) := by
      field_simp [ne_of_gt hε]

/-- The existing full absolute Leray-transfer profile is bounded by a
continuously adjustable fifth/cubic moment budget at every strict time. -/
theorem h3Path_globalAbsoluteTransfer_le_adjustableFifthCubic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hε : 0 < ε) :
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt
        hH3 hClass ht ≤
      ε * h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht +
        ε⁻¹ * h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
          hH3 hClass ht := by
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  let z : Fin 3 → H3FourierPoint3 → ℂ :=
    fun j ξ => h3SpectralScalarRawFourierL2 (U j) ξ
  let f : Fin 3 → H3FourierPoint3 → ℂ :=
    fun j ξ => h3RawFinLerayOuterProductDivergence U U j ξ
  let g : Fin 3 → H3FourierPoint3 → ℝ :=
    fun j ξ => h3FourierGradientSquare ξ ^ 4 * (inner ℂ (z j ξ) (f j ξ)).re
  let m5 : Fin 3 → H3FourierPoint3 → ℝ :=
    fun j ξ => h3FourierGradientSquare ξ ^ 5 * ‖z j ξ‖ ^ 2
  let m3 : Fin 3 → H3FourierPoint3 → ℝ :=
    fun j ξ => h3FourierGradientSquare ξ ^ 3 * ‖f j ξ‖ ^ 2
  have hEach (j : Fin 3) :
      2 * (∫ ξ : H3FourierPoint3, |g j ξ|) ≤
        ε * (∫ ξ : H3FourierPoint3, m5 j ξ) +
          ε⁻¹ * (∫ ξ : H3FourierPoint3, m3 j ξ) := by
    have hIntG : Integrable (g j) (volume : Measure H3FourierPoint3) := by
      change Integrable
        (h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt
          hH3 hClass ht j) (volume : Measure H3FourierPoint3)
      exact integrable_h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt'
        hH3 hClass ht j
    have hInt5 : Integrable (m5 j) (volume : Measure H3FourierPoint3) := by
      change Integrable (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 5 *
          ‖h3SpectralScalarRawFourierL2 (U j) ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3)
      simpa only [U, htAbs] using
        (integrable_h3TerminalPhysicalTopDissipationDiffusionCoordinateDensityAt
          hH3 hClass ht j)
    have hInt3 : Integrable (m3 j) (volume : Measure H3FourierPoint3) := by
      change Integrable
        (h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
          hH3 hClass ht j) (volume : Measure H3FourierPoint3)
      exact integrable_h3TerminalPhysicalTopDissipationForcingCubicCoordinateDensityAt
        hH3 hClass ht j
    have hAbsG : Integrable (fun ξ : H3FourierPoint3 => |g j ξ|)
        (volume : Measure H3FourierPoint3) := by
      simpa only [Real.norm_eq_abs] using hIntG.norm
    have hPoint : ∀ ξ : H3FourierPoint3,
        2 * |g j ξ| ≤ ε * m5 j ξ + ε⁻¹ * m3 j ξ := by
      intro ξ
      dsimp only [g, m5, m3, z, f]
      rw [abs_mul, abs_of_nonneg (pow_nonneg
        (h3FourierGradientSquare_nonneg ξ) 4)]
      simpa only [mul_assoc] using
        (h3_globalForcingTwoMoment_pointwise_adjustable244
          ε (h3FourierGradientSquare ξ) hε
          (h3FourierGradientSquare_nonneg ξ)
          (h3SpectralScalarRawFourierL2 (U j) ξ)
          (h3RawFinLerayOuterProductDivergence U U j ξ))
    have hIntRight : Integrable
        (fun ξ : H3FourierPoint3 =>
          ε * m5 j ξ + ε⁻¹ * m3 j ξ)
        (volume : Measure H3FourierPoint3) :=
      (hInt5.const_mul ε).add (hInt3.const_mul ε⁻¹)
    have hIntegral :
        (∫ ξ : H3FourierPoint3, 2 * |g j ξ|) ≤
          ∫ ξ : H3FourierPoint3, ε * m5 j ξ + ε⁻¹ * m3 j ξ :=
      integral_mono (hAbsG.const_mul 2) hIntRight hPoint
    calc
      2 * (∫ ξ : H3FourierPoint3, |g j ξ|) =
          ∫ ξ : H3FourierPoint3, 2 * |g j ξ| := by
            rw [integral_const_mul]
      _ ≤ ∫ ξ : H3FourierPoint3, ε * m5 j ξ + ε⁻¹ * m3 j ξ :=
          hIntegral
      _ = ε * (∫ ξ : H3FourierPoint3, m5 j ξ) +
          ε⁻¹ * (∫ ξ : H3FourierPoint3, m3 j ξ) := by
            rw [integral_add (hInt5.const_mul ε) (hInt3.const_mul ε⁻¹)]
            rw [integral_const_mul, integral_const_mul]
  unfold h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt
    h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferCoordinateAt
    h3PathTopFourierGlobalFifthMass244
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
  dsimp only
  change (∑ j : Fin 3, 2 * (∫ ξ : H3FourierPoint3, |g j ξ|)) ≤
    ε * (∑ j : Fin 3, ∫ ξ : H3FourierPoint3, m5 j ξ) +
      ε⁻¹ * (∑ j : Fin 3, ∫ ξ : H3FourierPoint3, m3 j ξ)
  calc
    (∑ j : Fin 3, 2 * (∫ ξ : H3FourierPoint3, |g j ξ|)) ≤
      ∑ j : Fin 3,
        (ε * (∫ ξ : H3FourierPoint3, m5 j ξ) +
          ε⁻¹ * (∫ ξ : H3FourierPoint3, m3 j ξ)) := by
            apply Finset.sum_le_sum
            intro j hj
            exact hEach j
    _ = ε * (∑ j : Fin 3, ∫ ξ : H3FourierPoint3, m5 j ξ) +
      ε⁻¹ * (∑ j : Fin 3, ∫ ξ : H3FourierPoint3, m3 j ξ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Signed global PDE inequality retaining (2-ε) fifth velocity shares.
For 0 < ε < 2 this is a genuinely coercive viscous estimate. -/
theorem h3Path_globalFourthRadialPairing_add_adjustableFifth_le_cubic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hε : 0 < ε) :
    h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t +
      (2 - ε) * h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht ≤
      ε⁻¹ * h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
        hH3 hClass ht := by
  have hTop := h3Path_fourthRadialPairing_eq_globalHeat_add_Leray244
    hH3 hClass ht
  have hHeat := h3Path_globalHeatRate_eq_negTwoFifthMass244
    hH3 hClass ht
  have hSigned := h3Path_globalLerayRate_le_fullAbsoluteTransfer244
    hH3 hClass ht
  have hYoung := h3Path_globalAbsoluteTransfer_le_adjustableFifthCubic244
    hH3 hClass ht hε
  calc
    h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t +
        (2 - ε) * h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht =
      h3PathTopFourierGlobalLerayRate244 hH3 t
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ -
      ε * h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht := by
        rw [hTop, hHeat]
        ring
    _ ≤ h3TerminalPhysicalTopDissipationFullAbsoluteNonlinearTransferAt
          hH3 hClass ht -
        ε * h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht :=
      sub_le_sub_right hSigned _
    _ ≤ ε⁻¹ * h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
          hH3 hClass ht := by
      linarith only [hYoung]

/-- Specialize the adjustable bound to retain three halves of M₅, charging
two copies of cubic forcing. -/
theorem h3Path_globalFourthRadialPairing_add_threeHalvesFifth_le_twoCubic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t +
      (3 / 2 : ℝ) * h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht ≤
      2 * h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
        hH3 hClass ht := by
  have h := h3Path_globalFourthRadialPairing_add_adjustableFifth_le_cubic244
    hH3 hClass ht (show 0 < (1 / 2 : ℝ) by norm_num)
  simpa only [show (2 : ℝ) - (1 / 2 : ℝ) = 3 / 2 by norm_num,
    show (1 / 2 : ℝ)⁻¹ = 2 by norm_num] using h

/-- If cubic forcing cannot pay the adjustable viscous share, top
fourth-radial dissipation is nonincreasing. -/
theorem h3Path_globalFourthRadialPairing_nonpos_of_adjustable_cubicBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hε : 0 < ε)
    (hBudget :
      ε⁻¹ * h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
        hH3 hClass ht ≤
      (2 - ε) * h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht) :
    h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t ≤ 0 := by
  have hRate := h3Path_globalFourthRadialPairing_add_adjustableFifth_le_cubic244
    hH3 hClass ht hε
  linarith only [hRate, hBudget]

/-- The forcing-to-dissipation threshold ε(2-ε) reaches at most one.
Thus tuning Young cannot produce a stronger universal forcing fraction
than the ε = 1 checkpoint. -/
theorem h3_adjustableFifthCubic_threshold_le_one244 (ε : ℝ) :
    ε * (2 - ε) ≤ 1 := by
  nlinarith only [sq_nonneg (ε - 1)]

end
end PrimeTensor.FirstMonomialTriad
