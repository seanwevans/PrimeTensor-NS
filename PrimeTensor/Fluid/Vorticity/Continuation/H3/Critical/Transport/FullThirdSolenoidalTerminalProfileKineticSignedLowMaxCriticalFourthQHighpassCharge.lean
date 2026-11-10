import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalDyadicSharpFourierHighpass
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE
import Mathlib.Tactic

/-!
# Critical physical H³ highpass source versus one additional forcing derivative

The sharp critical dyadic gate charges the net top-H³ growth plus actual
fifth/phase losses to the third-radial nonlinear forcing highpass. This file
makes the derivative loss quantitatively explicit. The canonical fourth-Q
source equals q² times the *same physical Leray nonlinearity*, where
q(ξ)=(2π)²‖ξ‖². It has one more radial derivative than the third-radial
source, up to the exact factor (2π)³.

At every strict physical time and every ρ>0:
  (2π)^6 ρ² ‖1_{|2πξ|≥ρ} F³_j‖₂² ≤ ‖F⁴Q_j‖₂².

No order-eight velocity moment hypothesis is added: the fourth-Q Fourier
state is the already constructed genuine strict-time physical forcing state.
This does NOT bound its norm by the fifth-order viscous velocity expenditure.
The latter is the new analytic obstruction, not a fact assumed here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeCriticalFourthQ244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceCriticalFourthQ244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A sharp high-frequency Bernstein estimate on quotient-safe Fourier L².
The comparison is stated as an a.e. moment inequality, not as a claim that
an arbitrary Fourier L² state has an additional derivative. -/
theorem thirdFullKinetic_highpass_norm_le_of_oneRadialMoment244
    (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c)
    (F G : H3FourierComplexL2)
    (hMoment : ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      c * h3FourierGradientMagnitude ξ * ‖F ξ‖ ≤ ‖G ξ‖) :
    ‖F - h3CriticalFourierSharpLowCutoffCLM ρ F‖ ≤
      (c * ρ)⁻¹ * ‖G‖ := by
  have hCoeffPos : 0 ≤ (c * ρ)⁻¹ :=
    (inv_pos.mpr (mul_pos hc hρ)).le
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [h3Critical_fourierSharpHighpass_ae ρ F, hMoment]
    with ξ hHigh hWeighted
  rw [hHigh]
  by_cases hOutside : ξ ∈ (h3TerminalRadialFrequencyBelow ρ)ᶜ
  · rw [Set.indicator_of_mem hOutside]
    have hNot : ξ ∉ h3TerminalRadialFrequencyBelow ρ :=
      hOutside
    have hFrequency : ρ ≤ h3FourierGradientMagnitude ξ := by
      change ¬ h3FourierGradientMagnitude ξ < ρ at hNot
      exact le_of_not_gt hNot
    have hRaw : (c * ρ) * ‖F ξ‖ ≤ ‖G ξ‖ := by
      calc
        (c * ρ) * ‖F ξ‖ =
          c * (ρ * ‖F ξ‖) := by ring
        _ ≤ c * (h3FourierGradientMagnitude ξ * ‖F ξ‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hFrequency (norm_nonneg _)) hc.le
        _ = c * h3FourierGradientMagnitude ξ * ‖F ξ‖ := by ring
        _ ≤ ‖G ξ‖ := hWeighted
    calc
      ‖F ξ‖ ≤ ‖G ξ‖ / (c * ρ) :=
        (le_div_iff₀ (mul_pos hc hρ)).mpr (by
          simpa only [mul_comm] using hRaw)
      _ = (c * ρ)⁻¹ * ‖G ξ‖ := by ring
  · rw [Set.indicator_of_notMem hOutside, norm_zero]
    exact mul_nonneg hCoeffPos (norm_nonneg _)

/-- The canonical physical q²-forcing is an exact one-derivative frequency
majorant of the third-radial forcing. The coefficient (2π)³ is not omitted. -/
theorem thirdFullPhysical_thirdRadial_fourthQ_aeMoment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (j : Fin 3) :
    let F := h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
      hH3 hClass j t
    let G := h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
      hH3 hClass j t
    ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      (2 * Real.pi) ^ 3 * h3FourierGradientMagnitude ξ * ‖F ξ‖ ≤
        ‖G ξ‖ := by
  dsimp only
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  have hThird :
      (h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
        hH3 hClass j t : H3FourierPoint3 → ℂ) =ᵐ[volume]
        (fun ξ => ((‖ξ‖ ^ 3 : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence U U j ξ) := by
    rw [h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path_eq
      hH3 hClass ht j]
    have hRep :=
      h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2At_ae
        hH3 hClass ht j
    simpa only [U, h3Path_actualSpectralVelocity_eq_terminalState244 hH3 t htAbs]
      using hRep
  have hFourth :
      (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
        hH3 hClass j t : H3FourierPoint3 → ℂ) =ᵐ[volume]
        (fun ξ => ((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence U U j ξ) := by
    rw [h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_eq
      hH3 hClass ht j]
    have hRep :=
      h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At_ae
        hH3 hClass ht j
    simpa only [U, h3Path_actualSpectralVelocity_eq_terminalState244 hH3 t htAbs]
      using hRep
  filter_upwards [hThird, hFourth] with ξ h3 h4
  rw [h3, h4]
  let N : ℂ := h3RawFinLerayOuterProductDivergence U U j ξ
  have h3Norm : ‖((‖ξ‖ ^ 3 : ℝ) : ℂ) * N‖ =
      ‖ξ‖ ^ 3 * ‖N‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 3)]
  have h4Norm : ‖((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ) * N‖ =
      h3FourierGradientSquare ξ ^ 2 * ‖N‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (h3FourierGradientSquare_nonneg ξ) 2)]
  change (2 * Real.pi) ^ 3 * h3FourierGradientMagnitude ξ *
      ‖((‖ξ‖ ^ 3 : ℝ) : ℂ) * N‖ ≤
      ‖((h3FourierGradientSquare ξ ^ 2 : ℝ) : ℂ) * N‖
  rw [h3Norm, h4Norm]
  dsimp only [h3FourierGradientMagnitude, h3FourierGradientSquare]
  exact le_of_eq (by ring)

/-- Actual physical highpass F³ is controlled by the *existing* strict-time
fourth-Q Leray forcing state, with the exact one-power radial decay. -/
theorem thirdFullPhysical_thirdRadialHighpass_le_fourthQ244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 < ρ) (j : Fin 3) :
    ‖thirdFullPhysicalCriticalThirdForcingHighpass244
      hH3 hClass ρ j t‖ ≤
      (((2 * Real.pi) ^ 3) * ρ)⁻¹ *
        ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
          hH3 hClass j t‖ := by
  have hPi : 0 < ((2 * Real.pi) ^ 3 : ℝ) := by positivity
  exact thirdFullKinetic_highpass_norm_le_of_oneRadialMoment244
    ρ ((2 * Real.pi) ^ 3) hρ hPi _ _
    (thirdFullPhysical_thirdRadial_fourthQ_aeMoment244
      hH3 hClass ht j)

/-- Squared physical highpass forcing, normalized against its fourth-Q
source: the full (2π)^6 cancels the Fourier convention in the dyadic charge. -/
theorem thirdFullPhysical_thirdRadialHighpass_fourthQ_square244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 < ρ) (j : Fin 3) :
    (2 * Real.pi) ^ 6 * ρ ^ 2 *
      ‖thirdFullPhysicalCriticalThirdForcingHighpass244 hH3 hClass ρ j t‖ ^ 2 ≤
      ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
        hH3 hClass j t‖ ^ 2 := by
  let H : H3FourierComplexL2 :=
    thirdFullPhysicalCriticalThirdForcingHighpass244 hH3 hClass ρ j t
  let G : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
      hH3 hClass j t
  have hNorm : ‖H‖ ≤ (((2 * Real.pi) ^ 3) * ρ)⁻¹ * ‖G‖ :=
    thirdFullPhysical_thirdRadialHighpass_le_fourthQ244
      hH3 hClass ht ρ hρ j
  have hSquare : ‖H‖ ^ 2 ≤
      ((((2 * Real.pi) ^ 3) * ρ)⁻¹ * ‖G‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hNorm 2
  have hMult : 0 ≤ (2 * Real.pi) ^ 6 * ρ ^ 2 := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hSquare hMult
  change (2 * Real.pi) ^ 6 * ρ ^ 2 * ‖H‖ ^ 2 ≤ ‖G‖ ^ 2
  calc
    _ ≤ (2 * Real.pi) ^ 6 * ρ ^ 2 *
        ((((2 * Real.pi) ^ 3) * ρ)⁻¹ * ‖G‖) ^ 2 := hScaled
    _ = ‖G‖ ^ 2 := by
      have hp : 2 * Real.pi ≠ 0 := by positivity
      have hρ0 : ρ ≠ 0 := ne_of_gt hρ
      field_simp [hp, hρ0]


/-- The strict-time fourth-Q source pays the actual net growth, viscous loss,
and phase loss at one interior dyadic witness, uniformly for all subsequently
chosen positive Fourier cutoffs. This does not assert any bound of the
fourth-Q forcing by velocity fifth-order dissipation. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_fourthQSourceCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hs : s ∈ Set.Ioo b T) (ht : t ∈ Set.Ioo b T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDouble : T - s = 2 * (T - t))
    (B : ℝ) (hB : 0 < B)
    (hRate : 1 ≤ B * (T - t) ^ 8 *
      (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3)
    (K : ℝ)
    (hNear : Real.log B + 8 * Real.log (T - s) +
        3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) <
        8 * Real.log 2 - 3 * K * (t - s)) :
    ∃ r : ℝ, r ∈ Set.Ioo s t ∧
      K < h3PathPhysicalTopSignedLogRate244 hClass r ∧
      ∀ ρ : ℝ, 0 < ρ →
        (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
            h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
          h3TerminalPhysicalTopDissipation3Path hClass r <
          (2 * Real.pi) ^ 6 *
            (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
              ρ (velocityH3Energy0At u b)) +
          (ρ ^ 2)⁻¹ *
            ∑ j : Fin 3,
              ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
                hH3 hClass j r‖ ^ 2 := by
  obtain ⟨r, hr, hNet, hAll⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_sharpAdaptiveJointHighpass244
      hH3 hClass b hb hs ht hst hD hDouble B hB hRate K hNear
  refine ⟨r, hr, hNet, ?_⟩
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hs.1 hr.1), lt_trans hr.2 ht.2⟩
  intro ρ hρ
  let C : ℝ := (2 * Real.pi) ^ 6
  let L : ℝ := thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
    ρ (velocityH3Energy0At u b)
  let H (j : Fin 3) : ℝ :=
    ‖thirdFullPhysicalCriticalThirdForcingHighpass244
      hH3 hClass ρ j r‖ ^ 2
  let G (j : Fin 3) : ℝ :=
    ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
      hH3 hClass j r‖ ^ 2
  have hEach (j : Fin 3) : C * H j ≤ (ρ ^ 2)⁻¹ * G j := by
    have hSquare := thirdFullPhysical_thirdRadialHighpass_fourthQ_square244
      hH3 hClass hrClass ρ hρ j
    have hReorder : (C * H j) * ρ ^ 2 ≤ G j := by
      simpa only [C, H, G, mul_left_comm, mul_comm, mul_assoc] using hSquare
    calc
      C * H j ≤ G j / (ρ ^ 2) :=
        (le_div_iff₀ (pow_pos hρ 2)).mpr hReorder
      _ = (ρ ^ 2)⁻¹ * G j := by ring
  have hSum : C * (∑ j : Fin 3, H j) ≤
      (ρ ^ 2)⁻¹ * (∑ j : Fin 3, G j) := by
    calc
      C * (∑ j : Fin 3, H j) = ∑ j : Fin 3, C * H j :=
        by rw [Finset.mul_sum]
      _ ≤ ∑ j : Fin 3, (ρ ^ 2)⁻¹ * G j := by
        apply Finset.sum_le_sum
        intro j _
        exact hEach j
      _ = (ρ ^ 2)⁻¹ * (∑ j : Fin 3, G j) := by rw [Finset.mul_sum]
  have hCharge :
      (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
          h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
        h3TerminalPhysicalTopDissipation3Path hClass r <
      C * (3 * L + ∑ j : Fin 3, H j) := by
    simpa only [C, L, H] using hAll ρ hρ.le
  calc
    _ < C * (3 * L + ∑ j : Fin 3, H j) := hCharge
    _ = C * (3 * L) + C * (∑ j : Fin 3, H j) := by ring
    _ ≤ C * (3 * L) + (ρ ^ 2)⁻¹ * (∑ j : Fin 3, G j) :=
      add_le_add_right hSum _
    _ = _ := by rfl

end
end PrimeTensor.FirstMonomialTriad
