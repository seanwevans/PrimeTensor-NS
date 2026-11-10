import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalThirdQHeatFifthMassCutoff
import Mathlib.Tactic

/-!
# Two-scale physical H3 fifth-order absorption and high-sixth defect

At a genuine critical dyadic physical source-peak time the sharp Leray source
cutoff radius rho and the third-Q heat cutoff radius sigma need not coincide.
Using the same radius in both places loses the entire fifth velocity square
mass on the right-hand side. Independent radii allow genuine absorption:

  A = (K + M5/D3 + Phase/D3) * D3
  A < Low(rho) + (2/rho^2) * (D4 + sigma^2*M5 + H6(sigma)).

Choosing sigma=rho/2 makes the fifth coefficient exactly one half. Therefore:

  (K + Phase/D3 + (M5/D3)/2) * D3
      < Low(rho) + (2/rho^2) * (D4 + H6(rho/2)).

The heat tail remains exact and the temporal cost remains the actual physical
fourth-radial velocity derivative. No unproved high-tail smallness or terminal
regularity assumption is introduced. This is a necessary critical obstruction,
not a Navier--Stokes continuation theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Exact scalar two-radius algebra. The physical source cutoff rho and the
heat cutoff rho/2 leave half of the positive fifth-order expenditure on the
left side of the PDE budget. -/
theorem thirdFullKinetic_twoScale_halfFifth_scalar244
    (rho K phase fifth D C temporal high : ℝ) (hrho : 0 < rho)
    (h : (K + fifth + phase) * D <
      C + 2 * (rho ^ 2)⁻¹ *
        (temporal + (rho / 2) ^ 2 * (fifth * D) + high)) :
    (K + phase + fifth / 2) * D <
      C + 2 * (rho ^ 2)⁻¹ * (temporal + high) := by
  have hrho0 : rho ≠ 0 := ne_of_gt hrho
  have hScale : 2 * (rho ^ 2)⁻¹ * (rho / 2) ^ 2 = (1 : ℝ) / 2 := by
    field_simp [hrho0] <;> ring
  have hRight :
      C + 2 * (rho ^ 2)⁻¹ *
          (temporal + (rho / 2) ^ 2 * (fifth * D) + high) -
        (fifth * D) / 2 =
      C + 2 * (rho ^ 2)⁻¹ * (temporal + high) := by
    calc
      _ = C + 2 * (rho ^ 2)⁻¹ * (temporal + high) +
          (2 * (rho ^ 2)⁻¹ * (rho / 2) ^ 2 - 1 / 2) *
            (fifth * D) := by ring
      _ = C + 2 * (rho ^ 2)⁻¹ * (temporal + high) := by
        rw [hScale]
        ring
  calc
    (K + phase + fifth / 2) * D =
        (K + fifth + phase) * D - (fifth * D) / 2 := by ring
    _ < C + 2 * (rho ^ 2)⁻¹ *
          (temporal + (rho / 2) ^ 2 * (fifth * D) + high) -
        (fifth * D) / 2 := sub_lt_sub_right h _
    _ = C + 2 * (rho ^ 2)⁻¹ * (temporal + high) := hRight

/-- One physical net-growth time works with TWO INDEPENDENT Fourier radii:
the source radius rho and the heat radius sigma. No artificial high-sixth
ceiling is inserted. The established fifth-order velocity cost is canonical. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_twoScaleFifthHeat244
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
      ∀ rho : ℝ, 0 < rho →
        ∀ sigma : ℝ, 0 ≤ sigma →
          (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
              h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
            h3TerminalPhysicalTopDissipation3Path hClass r <
            (2 * Real.pi) ^ 6 *
              (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
                rho (velocityH3Energy0At u b)) +
            2 * (rho ^ 2)⁻¹ * (
              (∑ j : Fin 3,
                ‖deriv
                  (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                    hH3 hClass j) r‖ ^ 2) +
              sigma ^ 2 *
                (h3PathPhysicalTopFifthActionRate244 hH3 hClass r *
                  h3TerminalPhysicalTopDissipation3Path hClass r) +
              (∑ j : Fin 3,
                ‖thirdFullPhysicalCriticalThirdQHeatHighpass244
                  hH3 hClass sigma j r‖ ^ 2)) := by
  obtain ⟨r, hr, hNet, hAll⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_fourthQTemporalThirdQBudget244
      hH3 hClass b hb hs ht hst hD hDouble B hB hRate K hNear
  refine ⟨r, hr, hNet, ?_⟩
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_trans hs.1 hr.1), lt_trans hr.2 ht.2⟩
  have hDr : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hrClass]
    exact hD r ⟨hr.1.le, hr.2.le⟩
  have hFifth :
      h3PathTopFourierGlobalFifthMass244 hH3 hClass r hrClass =
        h3PathPhysicalTopFifthActionRate244 hH3 hClass r *
          h3TerminalPhysicalTopDissipation3Path hClass r := by
    unfold h3PathPhysicalTopFifthActionRate244
    simp only [dif_pos hrClass]
    exact (div_mul_cancel₀ _ hDr.ne').symm
  intro rho hrho sigma hsigma
  let A : ℝ :=
    (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
      h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
      h3TerminalPhysicalTopDissipation3Path hClass r
  let C : ℝ := (2 * Real.pi) ^ 6 *
    (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
      rho (velocityH3Energy0At u b))
  let F5 : ℝ := h3PathTopFourierGlobalFifthMass244 hH3 hClass r hrClass
  let D4 : ℝ := ∑ j : Fin 3,
    ‖deriv (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
      hH3 hClass j) r‖ ^ 2
  let Q3 : ℝ := ∑ j : Fin 3,
    ‖h3TerminalPhysicalTopDissipationVelocityThirdQFourierL2Path
      hH3 hClass j r‖ ^ 2
  let H6 : ℝ := ∑ j : Fin 3,
    ‖thirdFullPhysicalCriticalThirdQHeatHighpass244
      hH3 hClass sigma j r‖ ^ 2
  have hInput : A < C + 2 * (rho ^ 2)⁻¹ * (D4 + Q3) := by
    simpa only [A, C, D4, Q3] using hAll rho hrho
  have hLowHigh : Q3 ≤ sigma ^ 2 * F5 + H6 := by
    simpa only [Q3, F5, H6] using
      (thirdFullPhysical_thirdQHeatSquare_le_fifthPlusHigh244
        hH3 hClass hrClass sigma hsigma)
  have hCoeff : 0 ≤ 2 * (rho ^ 2)⁻¹ := by positivity
  have hResult : A < C + 2 * (rho ^ 2)⁻¹ *
      (D4 + sigma ^ 2 * F5 + H6) := by
    calc
      A < C + 2 * (rho ^ 2)⁻¹ * (D4 + Q3) := hInput
      _ ≤ C + 2 * (rho ^ 2)⁻¹ *
          (D4 + (sigma ^ 2 * F5 + H6)) :=
        add_le_add_right
          (mul_le_mul_of_nonneg_left
            (add_le_add_right hLowHigh D4) hCoeff) C
      _ = C + 2 * (rho ^ 2)⁻¹ *
          (D4 + sigma ^ 2 * F5 + H6) := by ring
  simpa only [A, C, D4, F5, H6, hFifth] using hResult

/-- The half-scale sigma=rho/2 absorbs exactly HALF the true fifth-order
viscous expenditure, leaving only the fourth-radial temporal cost and an
actual high-sixth Fourier tail above rho/2 on the right side. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_halfFifthAbsorption244
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
      ∀ rho : ℝ, 0 < rho →
        (K + h3PathPhysicalTopPhaseActionRate244 hH3 hClass r +
            h3PathPhysicalTopFifthActionRate244 hH3 hClass r / 2) *
          h3TerminalPhysicalTopDissipation3Path hClass r <
          (2 * Real.pi) ^ 6 *
            (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
              rho (velocityH3Energy0At u b)) +
          2 * (rho ^ 2)⁻¹ * (
            (∑ j : Fin 3,
              ‖deriv
                (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                  hH3 hClass j) r‖ ^ 2) +
            (∑ j : Fin 3,
              ‖thirdFullPhysicalCriticalThirdQHeatHighpass244
                hH3 hClass (rho / 2) j r‖ ^ 2)) := by
  obtain ⟨r, hr, hNet, hAll⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_twoScaleFifthHeat244
      hH3 hClass b hb hs ht hst hD hDouble B hB hRate K hNear
  refine ⟨r, hr, hNet, ?_⟩
  intro rho hrho
  have hsigma : 0 ≤ rho / 2 := by positivity
  exact thirdFullKinetic_twoScale_halfFifth_scalar244
    rho K
    (h3PathPhysicalTopPhaseActionRate244 hH3 hClass r)
    (h3PathPhysicalTopFifthActionRate244 hH3 hClass r)
    (h3TerminalPhysicalTopDissipation3Path hClass r)
    ((2 * Real.pi) ^ 6 *
      (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
        rho (velocityH3Energy0At u b)))
    (∑ j : Fin 3,
      ‖deriv
        (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
          hH3 hClass j) r‖ ^ 2)
    (∑ j : Fin 3,
      ‖thirdFullPhysicalCriticalThirdQHeatHighpass244
        hH3 hClass (rho / 2) j r‖ ^ 2)
    hrho (hAll rho hrho (rho / 2) hsigma)

/-- The same scale-separated PDE peak identifies the exact remaining
high-sixth deficit. It is strictly charged without assuming temporal
smallness; temporal expenditure is explicitly subtracted from the left. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_highSixthDeficit244
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
      ∀ rho : ℝ, 0 < rho →
        (K + h3PathPhysicalTopPhaseActionRate244 hH3 hClass r +
            h3PathPhysicalTopFifthActionRate244 hH3 hClass r / 2) *
          h3TerminalPhysicalTopDissipation3Path hClass r -
          (2 * Real.pi) ^ 6 *
            (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
              rho (velocityH3Energy0At u b)) -
          2 * (rho ^ 2)⁻¹ *
            (∑ j : Fin 3,
              ‖deriv
                (h3TerminalPhysicalTopDissipationFourthRadialComponentL2Path
                  hH3 hClass j) r‖ ^ 2) <
          2 * (rho ^ 2)⁻¹ *
            (∑ j : Fin 3,
              ‖thirdFullPhysicalCriticalThirdQHeatHighpass244
                hH3 hClass (rho / 2) j r‖ ^ 2) := by
  obtain ⟨r, hr, hNet, hAll⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_halfFifthAbsorption244
      hH3 hClass b hb hs ht hst hD hDouble B hB hRate K hNear
  refine ⟨r, hr, hNet, ?_⟩
  intro rho hrho
  have hCharge := hAll rho hrho
  nlinarith only [hCharge]

end
end PrimeTensor.FirstMonomialTriad
