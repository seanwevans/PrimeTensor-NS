import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalDyadicNetHighpassExpenditure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassFourierMassEscape
import Mathlib.Tactic

/-!
# Sharp Fourier Pythagoras for the actual critical H3 Leray source

The previous net fifth/phase source gate bounded the full third-radial
forcing square by twice the sum of low/high forcing squares. That factor
two came from applying the triangle inequality to an ACTUAL measurable
Fourier projection, even though the low and high Fourier indicators are
orthogonal. This file proves the exact native L2 square identity, applies
it to the physical nonlinear source, and retains its net fifth/phase
expenditure on the single dyadic interior witness.

For every sharp radial frequency cutoff rho and actual strict physical time,

    M3 = (2*pi)^6 * sum_j (||P_rho F3_j||^2 + ||(1-P_rho)F3_j||^2)
       <= (2*pi)^6 * (3 * L_rho(E0(b)) + H_rho).

The factor two is removed without eighth Fourier moments or any new
terminal regularity premise. Hence at a near-critical net-growth time r,

    (K + fifth(r) + phase(r)) * D3(r)
      < (2*pi)^6 * (3 * L_rho(E0(b)) + H_rho(r))

for EVERY rho>=0, with r selected BEFORE rho. Equivalently the actual
nonlinear highpass square mass must strictly exceed the shortfall between
the physical net-growth expenditure and the kinetic low-band budget.

This sharpness is a rigorous improvement of the H3-native physical gate,
not an upper estimate on H_rho. Closing the source-versus-viscosity
inequality still requires new solenoidal nonlinear analysis.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeSharpHighpass244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceSharpHighpass244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Fourier sharp cutoff and its complementary indicator enjoy exact
Pythagoras in the *quotient-safe* complex L2 norm, for any radius.
This is stronger than the generic linear-operator triangle inequality. -/
theorem thirdFullKinetic_sharpFourierLowHigh_square_identity244
    (ρ : ℝ) (F : H3FourierComplexL2) :
    ‖F‖ ^ 2 =
      ‖h3CriticalFourierSharpLowCutoffCLM ρ F‖ ^ 2 +
      ‖F - h3CriticalFourierSharpLowCutoffCLM ρ F‖ ^ 2 := by
  let S : Set H3FourierPoint3 := h3TerminalRadialFrequencyBelow ρ
  let f : H3FourierPoint3 → ℝ := fun ξ => ‖F ξ‖ ^ 2
  have hLow :
      ‖h3CriticalFourierSharpLowCutoffCLM ρ F‖ ^ 2 =
        ∫ ξ in S, f ξ ∂volume := by
    change ‖h3CriticalFourierSharpLowCutoffApply ρ F‖ ^ 2 = _
    rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]
    rw [← integral_indicator (measurableSet_h3TerminalRadialFrequencyBelow ρ)]
    apply integral_congr_ae
    filter_upwards [h3Critical_fourierSharpLowCutoffApply_ae ρ F]
      with ξ hξ
    rw [hξ]
    by_cases hS : ξ ∈ S
    · rw [Set.indicator_of_mem hS, Set.indicator_of_mem hS]
    · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem hS]
      simp
  have hHigh :
      ‖F - h3CriticalFourierSharpLowCutoffCLM ρ F‖ ^ 2 =
        ∫ ξ in Sᶜ, f ξ ∂volume := by
    simpa only [S, f] using
      (h3Critical_fourierSharpHighpass_norm_sq_eq_integral ρ F)
  have hIntegrable : Integrable f volume := by
    dsimp only [f]
    exact (MeasureTheory.Lp.memLp F).integrable_norm_pow (by norm_num)
  have hPartition :
      (∫ ξ in S, f ξ ∂volume) +
        (∫ ξ in Sᶜ, f ξ ∂volume) =
        ∫ ξ, f ξ ∂volume := by
    exact integral_add_compl
      (measurableSet_h3TerminalRadialFrequencyBelow ρ) hIntegrable
  calc
    ‖F‖ ^ 2 = ∫ ξ, f ξ ∂volume := by
      exact h3FourierComplexL2_norm_sq_eq_integral_norm_sq F
    _ = (∫ ξ in S, f ξ ∂volume) +
          (∫ ξ in Sᶜ, f ξ ∂volume) := hPartition.symm
    _ = ‖h3CriticalFourierSharpLowCutoffCLM ρ F‖ ^ 2 +
          ‖F - h3CriticalFourierSharpLowCutoffCLM ρ F‖ ^ 2 := by
      rw [hLow, hHigh]

/-- The ACTUAL three-coordinate physical third-radial forcing mass has
constant ONE in the sharp low/high square split. The only inequality is
the known kinetic upper bound on the low Fourier band. -/
theorem thirdFullPhysical_criticalThirdForcingMass_sharpKineticLowHigh244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (t : ℝ) (ht : t ∈ Set.Ioo b T) :
    (2 * Real.pi) ^ 6 *
      (∑ j : Fin 3,
        (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
          hH3 hClass j t‖ : ℝ) ^ 2) ≤
      (2 * Real.pi) ^ 6 *
        (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
          ρ (velocityH3Energy0At u b) +
          ∑ j : Fin 3,
            (‖thirdFullPhysicalCriticalThirdForcingHighpass244
              hH3 hClass ρ j t‖ : ℝ) ^ 2) := by
  let F : Fin 3 → H3FourierComplexL2 := fun j =>
    h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
      hH3 hClass j t
  let P := h3CriticalFourierSharpLowCutoffCLM ρ
  let L := thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
    ρ (velocityH3Energy0At u b)
  have hLow (j : Fin 3) : ‖P (F j)‖ ^ 2 ≤ L := by
    exact thirdFullPhysical_criticalThirdForcingLowSquare_le_kinetic244
      hH3 hClass b hb ρ hρ t ht j
  have hLowSum :
      (∑ j : Fin 3, ‖P (F j)‖ ^ 2) ≤ 3 * L := by
    calc
      (∑ j : Fin 3, ‖P (F j)‖ ^ 2) ≤
          ∑ _j : Fin 3, L := by
        apply Finset.sum_le_sum
        intro j _
        exact hLow j
      _ = 3 * L := by simp <;> ring
  have hSplit :
      (∑ j : Fin 3, ‖F j‖ ^ 2) =
        (∑ j : Fin 3, ‖P (F j)‖ ^ 2) +
        (∑ j : Fin 3, ‖F j - P (F j)‖ ^ 2) := by
    calc
      (∑ j : Fin 3, ‖F j‖ ^ 2) =
          ∑ j : Fin 3,
            (‖P (F j)‖ ^ 2 + ‖F j - P (F j)‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro j _
        exact thirdFullKinetic_sharpFourierLowHigh_square_identity244 ρ (F j)
      _ = (∑ j : Fin 3, ‖P (F j)‖ ^ 2) +
            (∑ j : Fin 3, ‖F j - P (F j)‖ ^ 2) :=
        Finset.sum_add_distrib
  have hSum :
      (∑ j : Fin 3, ‖F j‖ ^ 2) ≤
        3 * L + ∑ j : Fin 3, ‖F j - P (F j)‖ ^ 2 := by
    rw [hSplit]
    exact add_le_add_left hLowSum _
  have hC : 0 ≤ (2 * Real.pi) ^ 6 := by positivity
  change (2 * Real.pi) ^ 6 * (∑ j : Fin 3, ‖F j‖ ^ 2) ≤
    (2 * Real.pi) ^ 6 *
      (3 * L + ∑ j : Fin 3, ‖F j - P (F j)‖ ^ 2)
  exact mul_le_mul_of_nonneg_left hSum hC

/-- Exact Navier--Stokes signed-log growth plus positive fifth and phase
losses is bounded by the kinetically controlled lowband and the sharp
highpass remainder, with no spurious factor two. -/
theorem thirdFullPhysical_signedLogPlusFifthPhase_le_sharpKineticLowHigh244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (r : ℝ) (hr : r ∈ Set.Ioo b T)
    (hD : 0 < velocityH3Dissipation3At u r)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (h3PathPhysicalTopSignedLogRate244 hClass r +
        h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
        h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
      h3TerminalPhysicalTopDissipation3Path hClass r ≤
      (2 * Real.pi) ^ 6 *
        (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
          ρ (velocityH3Energy0At u b) +
         ∑ j : Fin 3,
           (‖thirdFullPhysicalCriticalThirdForcingHighpass244
             hH3 hClass ρ j r‖ : ℝ) ^ 2) := by
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hr.1, hr.2⟩
  have hDr : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hrClass]
    exact hD
  have hBalance :=
    h3Path_topCubic_eq_signedLog_add_fifth_add_phase244
      hH3 hClass hrClass
  have hCubic :=
    h3Path_topCubic_eq_thirdRadialLerayNormSquares244
      hH3 hClass hrClass
  rw [hBalance] at hCubic
  have hIdentity :
      (h3PathPhysicalTopSignedLogRate244 hClass r +
          h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
          h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
        h3TerminalPhysicalTopDissipation3Path hClass r =
        (2 * Real.pi) ^ 6 *
          (∑ j : Fin 3,
            (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
              hH3 hClass j r‖ : ℝ) ^ 2) :=
    (eq_div_iff hDr.ne').mp hCubic
  calc
    _ = (2 * Real.pi) ^ 6 *
        (∑ j : Fin 3,
          (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
            hH3 hClass j r‖ : ℝ) ^ 2) := hIdentity
    _ ≤ (2 * Real.pi) ^ 6 *
        (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
          ρ (velocityH3Energy0At u b) +
         ∑ j : Fin 3,
           (‖thirdFullPhysicalCriticalThirdForcingHighpass244
             hH3 hClass ρ j r‖ : ℝ) ^ 2) :=
      thirdFullPhysical_criticalThirdForcingMass_sharpKineticLowHigh244
        hH3 hClass b hb ρ hρ r hr

/-- One strict physical net-growth witness, selected independently of
rho, pays the full physical fifth and phase expenditure against the SHARP
kinetic-low/highpass budget. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_sharpAdaptiveJointHighpass244
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
      ∀ ρ : ℝ, 0 ≤ ρ →
        (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
            h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
          h3TerminalPhysicalTopDissipation3Path hClass r <
          (2 * Real.pi) ^ 6 *
            (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
              ρ (velocityH3Energy0At u b) +
             ∑ j : Fin 3,
               (‖thirdFullPhysicalCriticalThirdForcingHighpass244
                 hH3 hClass ρ j r‖ : ℝ) ^ 2) := by
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, hs.2⟩
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  obtain ⟨r, hr, hNet⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_netSignedLogPeak244
      hH3 hClass hsClass htClass hst hD hDouble B hB hRate K hNear
  refine ⟨r, hr, hNet, ?_⟩
  have hrTail : r ∈ Set.Ioo b T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  have hDr : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    have hrClass : r ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 hrTail.1, hrTail.2⟩
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
    (thirdFullPhysical_signedLogPlusFifthPhase_le_sharpKineticLowHigh244
      hH3 hClass b hb r hrTail (hD r ⟨hr.1.le, hr.2.le⟩) ρ hρ)

/-- The sharp highpass deficit certificate, with no ad hoc half-budget
hypothesis: whenever the net fifth/phase source charge exceeds the
kinetically available low-frequency budget, the *difference* must be
carried by the genuinely nonlinear highpass Leray forcing. A single time
works simultaneously for ALL post-selected Fourier radii. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_sharpHighpassDeficit244
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
      ∀ ρ : ℝ, 0 ≤ ρ →
        (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
            h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
          h3TerminalPhysicalTopDissipation3Path hClass r -
          3 * (2 * Real.pi) ^ 6 *
            thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
              ρ (velocityH3Energy0At u b) <
          (2 * Real.pi) ^ 6 *
            ∑ j : Fin 3,
              (‖thirdFullPhysicalCriticalThirdForcingHighpass244
                hH3 hClass ρ j r‖ : ℝ) ^ 2 := by
  obtain ⟨r, hr, hNet, hAll⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_sharpAdaptiveJointHighpass244
      hH3 hClass b hb hs ht hst hD hDouble B hB hRate K hNear
  refine ⟨r, hr, hNet, ?_⟩
  intro ρ hρ
  let A : ℝ :=
    (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
        h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
      h3TerminalPhysicalTopDissipation3Path hClass r
  let C : ℝ := (2 * Real.pi) ^ 6
  let L : ℝ := thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
    ρ (velocityH3Energy0At u b)
  let H : ℝ := ∑ j : Fin 3,
    (‖thirdFullPhysicalCriticalThirdForcingHighpass244
      hH3 hClass ρ j r‖ : ℝ) ^ 2
  have hCharge : A < C * (3 * L + H) := by
    simpa only [A, C, L, H] using hAll ρ hρ
  change A - 3 * C * L < C * H
  nlinarith only [hCharge]

end
end PrimeTensor.FirstMonomialTriad
