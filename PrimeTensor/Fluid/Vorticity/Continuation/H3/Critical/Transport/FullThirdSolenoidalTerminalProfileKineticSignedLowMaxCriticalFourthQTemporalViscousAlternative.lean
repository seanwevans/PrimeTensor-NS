import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalFourthQHighpassCharge
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Balance
import Mathlib.Tactic

/-!
# Fourth-Q forcing charge: actual physical temporal derivative or heat state

The accepted critical dyadic highpass gate charges the net H3 log-production,
including fifth and phase losses, to an actual strict-time fourth-Q nonlinear
Leray forcing state. This file applies the already-proved *exact* physical
fourth-radial Fourier PDE equation

  F4Q_j = - d/dt V4_j - Q3_j,

where Q3_j is the physical third-Q velocity heat state. Thus the fourth-Q
nonlinear mass is bounded by two ACTUAL physical costs, not by a hypothetical
forcing envelope or unproven H3->higher moment estimate.

At the one dyadic physical net-growth witness r, for every rho>0:

 [K + fifth(r) + phase(r)] D3(r)
   < (2pi)^6 * 3 * LowBudget(rho,E0(b))
       + (2/rho^2) * (TemporalFourthMass(r) + VelocityThirdQMass(r)).

The theorem also gives the alternative with coefficient four: the first term
above cannot be large unless one of the temporal-fourth or velocity-third-Q
square masses pays the requisite frequency charge. These statements do not
bound either cost by the physical fifth-order velocity expenditure; that is
the remaining real analytic frontier.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The exact fourth-radial physical Fourier PDE triangle inequality has a
square-mass version, with no assumed higher Fourier moments. -/
theorem thirdFullPhysical_fourthQSquare_le_temporalThirdQCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (j : Fin 3) :
    ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
        hH3 hClass j t‖ ^ 2 ≤
      2 * (
        ‖deriv
          (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
            hH3 hClass j) t‖ ^ 2 +
        ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
          hH3 hClass j t‖ ^ 2) := by
  let F : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
      hH3 hClass j t
  let D : H3FourierComplexL2 :=
    deriv (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
      hH3 hClass j) t
  let V : H3FourierComplexL2 :=
    h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
      hH3 hClass j t
  have hNorm : ‖F‖ ≤ ‖D‖ + ‖V‖ := by
    dsimp only [F, D, V]
    exact
      norm_h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path_le_deriv_add_velocityThirdQPath
        hH3 hClass ht j
  have hSq : ‖F‖ ^ 2 ≤ (‖D‖ + ‖V‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg F) hNorm 2
  have hDiff : 0 ≤ (‖D‖ - ‖V‖) ^ 2 := sq_nonneg _
  change ‖F‖ ^ 2 ≤ 2 * (‖D‖ ^ 2 + ‖V‖ ^ 2)
  nlinarith only [hSq, hDiff]

/-- All three physical forcing coordinates satisfy the summed fourth-Q
PDE cost split. Each cost is a real Hilbert square, not a sup-norm proxy. -/
theorem thirdFullPhysical_fourthQSumSquares_le_temporalThirdQCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    (∑ j : Fin 3,
      ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
        hH3 hClass j t‖ ^ 2) ≤
      2 * (
        (∑ j : Fin 3,
          ‖deriv
            (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
              hH3 hClass j) t‖ ^ 2) +
        (∑ j : Fin 3,
          ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
            hH3 hClass j t‖ ^ 2)) := by
  calc
    (∑ j : Fin 3,
      ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
        hH3 hClass j t‖ ^ 2) ≤
        ∑ j : Fin 3,
          2 * (
            ‖deriv
              (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                hH3 hClass j) t‖ ^ 2 +
            ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
              hH3 hClass j t‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro j _
        exact thirdFullPhysical_fourthQSquare_le_temporalThirdQCost244
          hH3 hClass ht j
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- On a genuine last-half H3 critical clock, one strict physical net-log
peak forces a lowpass/physical-temporal/velocity-heat upper budget for every
subsequently chosen positive Fourier cutoff. No additional raw moment
hypotheses or artificial terminal supremum are supplied. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_fourthQTemporalThirdQBudget244
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
              ‖deriv
                (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                  hH3 hClass j) r‖ ^ 2) +
            (∑ j : Fin 3,
              ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
                hH3 hClass j r‖ ^ 2)) := by
  obtain ⟨r, hr, hNet, hAll⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_fourthQSourceCharge244
      hH3 hClass b hb hs ht hst hD hDouble B hB hRate K hNear
  refine ⟨r, hr, hNet, ?_⟩
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hs.1 hr.1), lt_trans hr.2 ht.2⟩
  intro ρ hρ
  let A : ℝ :=
    (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
        h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
      h3TerminalPhysicalTopDissipation3Path hClass r
  let C : ℝ := (2 * Real.pi) ^ 6 *
    (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
      ρ (velocityH3Energy0At u b))
  let F4 : ℝ := ∑ j : Fin 3,
    ‖h3TerminalPhysicalTopDissipationForcingFourthQFourierL2Path
      hH3 hClass j r‖ ^ 2
  let Vt : ℝ := ∑ j : Fin 3,
    ‖deriv
      (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
        hH3 hClass j) r‖ ^ 2
  let Vq : ℝ := ∑ j : Fin 3,
    ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
      hH3 hClass j r‖ ^ 2
  have hCharge : A < C + (ρ ^ 2)⁻¹ * F4 := by
    dsimp only [A, C, F4]
    exact hAll ρ hρ
  have hSource : F4 ≤ 2 * (Vt + Vq) := by
    dsimp only [F4, Vt, Vq]
    exact thirdFullPhysical_fourthQSumSquares_le_temporalThirdQCost244
      hH3 hClass hrClass
  have hInv : 0 ≤ (ρ ^ 2)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg hρ.le 2)
  have hBound : A < C + 2 * (ρ ^ 2)⁻¹ * (Vt + Vq) := by
    calc
      A < C + (ρ ^ 2)⁻¹ * F4 := hCharge
      _ ≤ C + (ρ ^ 2)⁻¹ * (2 * (Vt + Vq)) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hSource hInv) C
      _ = C + 2 * (ρ ^ 2)⁻¹ * (Vt + Vq) := by ring
  simpa only [A, C, Vt, Vq] using hBound

/-- The same critical physical peak forces an explicit alternative:
its net fifth/phase charge is carried either by the fourth-radial temporal
velocity derivative or by the genuine third-Q velocity heat state.
The frequency cutoff can be chosen *after* selecting the time. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_temporalOrThirdQ244
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
        ((K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
              h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
            h3TerminalPhysicalTopDissipation3Path hClass r <
          (2 * Real.pi) ^ 6 *
            (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
              ρ (velocityH3Energy0At u b)) +
          4 * (ρ ^ 2)⁻¹ *
            (∑ j : Fin 3,
              ‖deriv
                (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                  hH3 hClass j) r‖ ^ 2) ∨
         (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
              h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
            h3TerminalPhysicalTopDissipation3Path hClass r <
          (2 * Real.pi) ^ 6 *
            (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
              ρ (velocityH3Energy0At u b)) +
          4 * (ρ ^ 2)⁻¹ *
            (∑ j : Fin 3,
              ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
                hH3 hClass j r‖ ^ 2)) := by
  obtain ⟨r, hr, hNet, hAll⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_fourthQTemporalThirdQBudget244
      hH3 hClass b hb hs ht hst hD hDouble B hB hRate K hNear
  refine ⟨r, hr, hNet, ?_⟩
  intro ρ hρ
  let A : ℝ :=
    (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
        h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
      h3TerminalPhysicalTopDissipation3Path hClass r
  let C : ℝ := (2 * Real.pi) ^ 6 *
    (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
      ρ (velocityH3Energy0At u b))
  let Vt : ℝ := ∑ j : Fin 3,
    ‖deriv
      (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
        hH3 hClass j) r‖ ^ 2
  let Vq : ℝ := ∑ j : Fin 3,
    ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
      hH3 hClass j r‖ ^ 2
  let Q : ℝ := (ρ ^ 2)⁻¹
  have hCharge : A < C + 2 * Q * (Vt + Vq) := by
    simpa only [A, C, Vt, Vq, Q] using hAll ρ hρ
  by_cases hTemporal : A < C + 4 * Q * Vt
  · left
    simpa only [A, C, Vt, Q] using hTemporal
  · right
    have hTemporalLower : C + 4 * Q * Vt ≤ A :=
      le_of_not_gt hTemporal
    have hHeat : A < C + 4 * Q * Vq := by
      nlinarith only [hCharge, hTemporalLower]
    simpa only [A, C, Vq, Q] using hHeat

end
end PrimeTensor.FirstMonomialTriad
