import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalTwoScaleFifthAbsorption
import Mathlib.Tactic

/-!
# Localize the exact fourth-Q Navier--Stokes balance before estimating it

The accepted critical source peak first bounded high-third forcing by the
FULL fourth-Q forcing. This needlessly discarded Fourier localization before
applying the physical PDE. Here the one-derivative comparison is applied to
both complementary Fourier projections, so only the HIGH fourth-Q forcing
is charged. The exact PDE identity then transfers that high forcing to the
same highpass of the fourth-radial temporal velocity and third-Q heat state.

For every strict physical time, positive rho, and positive D3:

  ((log D3)' + Phi5 + PhiPhase) D3
    <= (2*pi)^6 * 3 * Low_rho(E0(b))
       + (2/rho^2) * (HighTemporal4_rho + HighSixthHeat_rho).

At the existing critical dyadic witness the left signed-log term may be
replaced strictly by K. The COMPLETE physical fifth-order expenditure is
retained on the left: there is no low-frequency heat payment, no half-loss,
and no independent eighth-order raw velocity moment hypothesis.

This is a stronger necessary obstruction, not a terminal-uniform bound on
the high temporal or high sixth heat tails, and not a continuation proof.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

-- The Fourier carrier inherits the canonical three-axis product volume.
-- This local instance is needed before the a.e. highpass multiplier lemma.
noncomputable local instance axisFintypeCriticalLocalizedFourthQ244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceCriticalLocalizedFourthQ244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Localized Bernstein comparison: the derivative-majorant is itself
restricted to the SAME complementary band as the lower-order state. -/
theorem thirdFullKinetic_highpass_norm_le_highpass_oneRadialMoment244
    (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c)
    (F G : H3FourierComplexL2)
    (hMoment : ∀ᵐ ξ ∂(volume : Measure H3FourierPoint3),
      c * h3FourierGradientMagnitude ξ * ‖F ξ‖ ≤ ‖G ξ‖) :
    ‖F - h3CriticalFourierSharpLowCutoffCLM ρ F‖ ≤
      (c * ρ)⁻¹ *
        ‖G - h3CriticalFourierSharpLowCutoffCLM ρ G‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    h3Critical_fourierSharpHighpass_ae ρ F,
    h3Critical_fourierSharpHighpass_ae ρ G,
    hMoment
  ] with ξ hF hG hWeighted
  rw [hF, hG]
  by_cases hOutside : ξ ∈ (h3TerminalRadialFrequencyBelow ρ)ᶜ
  · rw [Set.indicator_of_mem hOutside, Set.indicator_of_mem hOutside]
    have hNot : ξ ∉ h3TerminalRadialFrequencyBelow ρ := hOutside
    have hFrequency : ρ ≤ h3FourierGradientMagnitude ξ := by
      change ¬ h3FourierGradientMagnitude ξ < ρ at hNot
      exact le_of_not_gt hNot
    have hRaw : (c * ρ) * ‖F ξ‖ ≤ ‖G ξ‖ := by
      calc
        (c * ρ) * ‖F ξ‖ = c * (ρ * ‖F ξ‖) := by ring
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
  · simpa only [Set.indicator_of_notMem hOutside, norm_zero, mul_zero]
      using (le_refl (0 : ℝ))

/-- The genuine fourth-Q nonlinear forcing only needs its SAME sharp
highpass when it controls the third-radial Leray source highpass. -/
theorem thirdFullPhysical_thirdRadialHighpass_le_fourthQHighpass244
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
            hH3 hClass j t -
          h3CriticalFourierSharpLowCutoffCLM ρ
            (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
              hH3 hClass j t)‖ := by
  have hPi : 0 < ((2 * Real.pi) ^ 3 : ℝ) := by positivity
  exact thirdFullKinetic_highpass_norm_le_highpass_oneRadialMoment244
    ρ ((2 * Real.pi) ^ 3) hρ hPi _ _
    (thirdFullPhysical_thirdRadial_fourthQ_aeMoment244
      hH3 hClass ht j)

/-- The exact Fourier factors cancel even after the fourth-Q source is
localized: there is NO full fourth-Q state-size loss. -/
theorem thirdFullPhysical_thirdRadialHighpass_fourthQHighpass_square244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 < ρ) (j : Fin 3) :
    (2 * Real.pi) ^ 6 * ρ ^ 2 *
      ‖thirdFullPhysicalCriticalThirdForcingHighpass244
        hH3 hClass ρ j t‖ ^ 2 ≤
      ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
          hH3 hClass j t -
        h3CriticalFourierSharpLowCutoffCLM ρ
          (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
            hH3 hClass j t)‖ ^ 2 := by
  let H : H3FourierComplexL2 :=
    thirdFullPhysicalCriticalThirdForcingHighpass244 hH3 hClass ρ j t
  let G : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
      hH3 hClass j t
  let P := h3CriticalFourierSharpLowCutoffCLM ρ
  have hNorm : ‖H‖ ≤ (((2 * Real.pi) ^ 3) * ρ)⁻¹ * ‖G - P G‖ :=
    thirdFullPhysical_thirdRadialHighpass_le_fourthQHighpass244
      hH3 hClass ht ρ hρ j
  have hSquare : ‖H‖ ^ 2 ≤
      ((((2 * Real.pi) ^ 3) * ρ)⁻¹ * ‖G - P G‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hNorm 2
  have hMult : 0 ≤ (2 * Real.pi) ^ 6 * ρ ^ 2 := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hSquare hMult
  change (2 * Real.pi) ^ 6 * ρ ^ 2 * ‖H‖ ^ 2 ≤ ‖G - P G‖ ^ 2
  calc
    _ ≤ (2 * Real.pi) ^ 6 * ρ ^ 2 *
        ((((2 * Real.pi) ^ 3) * ρ)⁻¹ * ‖G - P G‖) ^ 2 := hScaled
    _ = ‖G - P G‖ ^ 2 := by
      have hp : 2 * Real.pi ≠ 0 := by positivity
      have hρ0 : ρ ≠ 0 := ne_of_gt hρ
      field_simp [hp, hρ0]

/-- The actual fourth-radial temporal velocity state is cut at the same
sharp radius as the nonlinear high-frequency source. -/
noncomputable def thirdFullPhysicalCriticalFourthTemporalHighpass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ρ : ℝ) (j : Fin 3) (t : ℝ) : H3FourierComplexL2 :=
  deriv (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
      hH3 hClass j) t -
    h3CriticalFourierSharpLowCutoffCLM ρ
      (deriv (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
        hH3 hClass j) t)

/-- Exact localized PDE: high fourth-Q forcing equals minus the high
physical fourth-radial time derivative minus the high third-Q heat state. -/
theorem thirdFullPhysical_fourthQHighpass_eq_temporalHigh_sub_thirdQHigh244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (ρ : ℝ) (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
        hH3 hClass j t -
      h3CriticalFourierSharpLowCutoffCLM ρ
        (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
          hH3 hClass j t) =
      -thirdFullPhysicalCriticalFourthTemporalHighpass244
        hH3 hClass ρ j t -
      thirdFullPhysicalCriticalThirdQHeatHighpass244
        hH3 hClass ρ j t := by
  let G : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
      hH3 hClass j t
  let D : H3FourierComplexL2 :=
    deriv (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
      hH3 hClass j) t
  let V : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
      hH3 hClass j t
  let P := h3CriticalFourierSharpLowCutoffCLM ρ
  have hPDE : G = -D - V := by
    dsimp only [G, D, V]
    rw [h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_eq
      hH3 hClass ht j,
      h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path_eq
      hH3 hClass ht j]
    exact h3TerminalPhysicalTopDissipationForcingFourthQFourierL2At_eq_neg_deriv_sub_velocityThirdQ
      hH3 hClass ht j
  change G - P G = -(D - P D) - (V - P V)
  rw [hPDE]
  simp only [map_sub, map_neg]
  abel

/-- Highpass fourth-Q forcing pays ONLY highpass fourth-time and heat
costs: low frequencies of both PDE states cancel before any triangle bound. -/
theorem thirdFullPhysical_fourthQHighpassSquare_le_temporalHighThirdQHigh244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (ρ : ℝ) (j : Fin 3) :
    ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
        hH3 hClass j t -
      h3CriticalFourierSharpLowCutoffCLM ρ
        (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
          hH3 hClass j t)‖ ^ 2 ≤
      2 * (
        ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
          hH3 hClass ρ j t‖ ^ 2 +
        ‖thirdFullPhysicalCriticalThirdQHeatHighpass244
          hH3 hClass ρ j t‖ ^ 2) := by
  let F : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
      hH3 hClass j t -
    h3CriticalFourierSharpLowCutoffCLM ρ
      (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
        hH3 hClass j t)
  let D : H3FourierComplexL2 :=
    thirdFullPhysicalCriticalFourthTemporalHighpass244 hH3 hClass ρ j t
  let V : H3FourierComplexL2 :=
    thirdFullPhysicalCriticalThirdQHeatHighpass244 hH3 hClass ρ j t
  have hEq : F = -D - V :=
    thirdFullPhysical_fourthQHighpass_eq_temporalHigh_sub_thirdQHigh244
      hH3 hClass ht ρ j
  have hNorm : ‖F‖ ≤ ‖D‖ + ‖V‖ := by
    rw [hEq]
    calc
      ‖-D - V‖ ≤ ‖-D‖ + ‖V‖ := norm_sub_le _ _
      _ = ‖D‖ + ‖V‖ := by rw [norm_neg]
  have hSq : ‖F‖ ^ 2 ≤ (‖D‖ + ‖V‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg F) hNorm 2
  have hDiff : 0 ≤ (‖D‖ - ‖V‖) ^ 2 := sq_nonneg _
  change ‖F‖ ^ 2 ≤ 2 * (‖D‖ ^ 2 + ‖V‖ ^ 2)
  nlinarith only [hSq, hDiff]

/-- Genuine three-coordinate sum of squares for the high-frequency PDE.
No full temporal or full sixth-order velocity norm enters this estimate. -/
theorem thirdFullPhysical_fourthQHighpassSum_le_temporalHighThirdQHigh244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (ρ : ℝ) :
    (∑ j : Fin 3,
      ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
          hH3 hClass j t -
        h3CriticalFourierSharpLowCutoffCLM ρ
          (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
            hH3 hClass j t)‖ ^ 2) ≤
      2 * (
        (∑ j : Fin 3,
          ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
            hH3 hClass ρ j t‖ ^ 2) +
        (∑ j : Fin 3,
          ‖thirdFullPhysicalCriticalThirdQHeatHighpass244
            hH3 hClass ρ j t‖ ^ 2)) := by
  calc
    _ ≤ ∑ j : Fin 3,
      2 * (
        ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
          hH3 hClass ρ j t‖ ^ 2 +
        ‖thirdFullPhysicalCriticalThirdQHeatHighpass244
          hH3 hClass ρ j t‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      exact thirdFullPhysical_fourthQHighpassSquare_le_temporalHighThirdQHigh244
        hH3 hClass ht ρ j
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Pointwise physical signed-log/fifth/phase budget with ALL costs
frequency-localized at the SAME cutoff, not only at a dyadic peak. -/
theorem thirdFullPhysical_signedLogFifthPhase_le_localizedFourthQ244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (r : ℝ) (hr : r ∈ Set.Ioo b T)
    (hD : 0 < velocityH3Dissipation3At u r)
    (ρ : ℝ) (hρ : 0 < ρ) :
    (h3PathPhysicalTopSignedLogRate244 hClass r +
        h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
        h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
      h3TerminalPhysicalTopDissipation3Path hClass r ≤
      (2 * Real.pi) ^ 6 *
        (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
          ρ (velocityH3Energy0At u b)) +
      2 * (ρ ^ 2)⁻¹ * (
        (∑ j : Fin 3,
          ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
            hH3 hClass ρ j r‖ ^ 2) +
        (∑ j : Fin 3,
          ‖thirdFullPhysicalCriticalThirdQHeatHighpass244
            hH3 hClass ρ j r‖ ^ 2)) := by
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hr.1, hr.2⟩
  let C : ℝ := (2 * Real.pi) ^ 6
  let L : ℝ := thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
    ρ (velocityH3Energy0At u b)
  let F (j : Fin 3) : ℝ :=
    ‖thirdFullPhysicalCriticalThirdForcingHighpass244
      hH3 hClass ρ j r‖ ^ 2
  let G (j : Fin 3) : ℝ :=
    ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
        hH3 hClass j r -
      h3CriticalFourierSharpLowCutoffCLM ρ
        (h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
          hH3 hClass j r)‖ ^ 2
  let D (j : Fin 3) : ℝ :=
    ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
      hH3 hClass ρ j r‖ ^ 2
  let V (j : Fin 3) : ℝ :=
    ‖thirdFullPhysicalCriticalThirdQHeatHighpass244
      hH3 hClass ρ j r‖ ^ 2
  have hEach (j : Fin 3) : C * F j ≤ (ρ ^ 2)⁻¹ * G j := by
    have hSquare :=
      thirdFullPhysical_thirdRadialHighpass_fourthQHighpass_square244
        hH3 hClass hrClass ρ hρ j
    have hReorder : (C * F j) * ρ ^ 2 ≤ G j := by
      simpa only [C, F, G, mul_left_comm, mul_comm, mul_assoc] using hSquare
    calc
      C * F j ≤ G j / (ρ ^ 2) :=
        (le_div_iff₀ (pow_pos hρ 2)).mpr hReorder
      _ = (ρ ^ 2)⁻¹ * G j := by ring
  have hSum : C * (∑ j : Fin 3, F j) ≤
      (ρ ^ 2)⁻¹ * (∑ j : Fin 3, G j) := by
    calc
      C * (∑ j : Fin 3, F j) = ∑ j : Fin 3, C * F j :=
        by rw [Finset.mul_sum]
      _ ≤ ∑ j : Fin 3, (ρ ^ 2)⁻¹ * G j := by
        apply Finset.sum_le_sum
        intro j _
        exact hEach j
      _ = (ρ ^ 2)⁻¹ * (∑ j : Fin 3, G j) := by rw [Finset.mul_sum]
  have hPDE : (∑ j : Fin 3, G j) ≤
      2 * ((∑ j : Fin 3, D j) + (∑ j : Fin 3, V j)) := by
    simpa only [G, D, V] using
      (thirdFullPhysical_fourthQHighpassSum_le_temporalHighThirdQHigh244
        hH3 hClass hrClass ρ)
  have hCoeff : 0 ≤ (ρ ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  have hTailBound : C * (∑ j : Fin 3, F j) ≤
      2 * (ρ ^ 2)⁻¹ *
        ((∑ j : Fin 3, D j) + (∑ j : Fin 3, V j)) := by
    calc
      C * (∑ j : Fin 3, F j) ≤
          (ρ ^ 2)⁻¹ * (∑ j : Fin 3, G j) := hSum
      _ ≤ (ρ ^ 2)⁻¹ *
          (2 * ((∑ j : Fin 3, D j) + (∑ j : Fin 3, V j))) :=
        mul_le_mul_of_nonneg_left hPDE hCoeff
      _ = 2 * (ρ ^ 2)⁻¹ *
          ((∑ j : Fin 3, D j) + (∑ j : Fin 3, V j)) := by ring
  have hSigned :=
    thirdFullPhysical_signedLogPlusFifthPhase_le_sharpKineticLowHigh244
      hH3 hClass b hb r hr hD ρ hρ.le
  have hResult :
      (h3PathPhysicalTopSignedLogRate244 hClass r +
        h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
        h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
        h3TerminalPhysicalTopDissipation3Path hClass r ≤
      C * (3 * L) +
        2 * (ρ ^ 2)⁻¹ *
          ((∑ j : Fin 3, D j) + (∑ j : Fin 3, V j)) := by
    calc
      _ ≤ C * (3 * L + ∑ j : Fin 3, F j) := by
        simpa only [C, L, F] using hSigned
      _ = C * (3 * L) + C * (∑ j : Fin 3, F j) := by ring
      _ ≤ C * (3 * L) +
          2 * (ρ ^ 2)⁻¹ *
            ((∑ j : Fin 3, D j) + (∑ j : Fin 3, V j)) :=
        add_le_add_right hTailBound _
  simpa only [C, L, D, V] using hResult

/-- Critical dyadic net-growth peaks require high-frequency time or sixth
heat expenditure at the SAME forcing radius. The ENTIRE fifth moment and
positive phase defect remain on the left. No auxiliary moment bound is
postulated, and the physical witness works for all radii. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_localizedTemporalSixth244
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
          2 * (ρ ^ 2)⁻¹ * (
            (∑ j : Fin 3,
              ‖thirdFullPhysicalCriticalFourthTemporalHighpass244
                hH3 hClass ρ j r‖ ^ 2) +
            (∑ j : Fin 3,
              ‖thirdFullPhysicalCriticalThirdQHeatHighpass244
                hH3 hClass ρ j r‖ ^ 2)) := by
  obtain ⟨r, hr, hNet⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_netSignedLogPeak244
      hH3 hClass
      (show s ∈ Set.Ioo a T from
        ⟨lt_trans hb.1 hs.1, hs.2⟩)
      (show t ∈ Set.Ioo a T from
        ⟨lt_trans hb.1 ht.1, ht.2⟩)
      hst hD hDouble B hB hRate K hNear
  refine ⟨r, hr, hNet, ?_⟩
  have hrTail : r ∈ Set.Ioo b T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hrTail.1, hrTail.2⟩
  have hDr : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hrClass]
    exact hD r ⟨hr.1.le, hr.2.le⟩
  intro ρ hρ
  have hRatePlus :
      K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
          h3PathPhysicalTopPhaseActionRate244 hH3 hClass r <
      h3PathPhysicalTopSignedLogRate244 hClass r +
          h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
          h3PathPhysicalTopPhaseActionRate244 hH3 hClass r := by
    linarith only [hNet]
  exact lt_of_lt_of_le
    (mul_lt_mul_of_pos_right hRatePlus hDr)
    (thirdFullPhysical_signedLogFifthPhase_le_localizedFourthQ244
      hH3 hClass b hb r hrTail
      (hD r ⟨hr.1.le, hr.2.le⟩) ρ hρ)

end
end PrimeTensor.FirstMonomialTriad
