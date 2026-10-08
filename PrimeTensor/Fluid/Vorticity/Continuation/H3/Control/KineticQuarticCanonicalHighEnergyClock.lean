import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalHighEnergyMoment
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Riccati.Integrability

/-!
# Eventual high-energy occupation from the terminal Riccati clock

The previous canonical selected-direct argument localized hypothetical
nonextension to a nonintegrable high-energy square-root H3 moment, conditional
on positive kinetic mass at the anchor.  The existing terminal Riccati
lower bound supplies a stronger, independent route: nonextension forces

    2 ≤ K * (T - t) * sqrt(E_H3(t))

on every energy-class tail, where K is strictly positive.  For any fixed
finite energy cutoff L, every sufficiently late strict time therefore has
E_H3(t) > L.  The high-energy square-root moment then agrees pointwise
with the full square-root energy on a final interval.

Together with the already-established nonintegrability of the full
square-root energy, this removes the positive-kinetic-mass assumption from
the necessary high-energy moment obstruction.  All conclusions remain
conditional on hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

/-- A short terminal clock window and the Riccati lower bound rule out
energy below any prescribed cutoff. -/
theorem h3PathCanonical_energy_gt_cutoff_of_short_terminal_gap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t L q : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hq : 0 < q)
    (hWindow : h3PathSqrtEnergyRiccatiCoefficient * q *
      Real.sqrt (max L 0) < 2)
    (hLate : T - t < q) :
    L < velocityH3EnergyAt u t := by
  by_contra hNot
  have hEnergy : velocityH3EnergyAt u t ≤ L := le_of_not_gt hNot
  have hSqrt : Real.sqrt (velocityH3EnergyAt u t) ≤
      Real.sqrt (max L 0) :=
    Real.sqrt_le_sqrt (le_trans hEnergy (le_max_left L 0))
  have hDist : h3PathSqrtEnergyRiccatiCoefficient * (T - t) ≤
      h3PathSqrtEnergyRiccatiCoefficient * q :=
    mul_le_mul_of_nonneg_left (le_of_lt hLate)
      (le_of_lt h3PathSqrtEnergyRiccatiCoefficient_pos)
  have hProduct :
      h3PathSqrtEnergyRiccatiCoefficient * (T - t) *
          Real.sqrt (velocityH3EnergyAt u t) ≤
        h3PathSqrtEnergyRiccatiCoefficient * q *
          Real.sqrt (max L 0) := by
    exact mul_le_mul hDist hSqrt (Real.sqrt_nonneg _)
      (mul_nonneg (le_of_lt h3PathSqrtEnergyRiccatiCoefficient_pos)
        (le_of_lt hq))
  have hRate :=
    two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrtEnergy_of_noH3PathExtension
      hH3 hNoExtension hClass ht
  exact (not_lt_of_ge (hRate.trans hProduct)) hWindow

/-- Every fixed energy cutoff admits a positive terminal-clock width for
which the Riccati inequality rules out the bounded-energy regime. -/
theorem h3PathCanonical_exists_short_terminal_gap_for_cutoff (L : ℝ) :
    ∃ q : ℝ, 0 < q ∧
      h3PathSqrtEnergyRiccatiCoefficient * q *
        Real.sqrt (max L 0) < 2 := by
  let K : ℝ := h3PathSqrtEnergyRiccatiCoefficient
  let S : ℝ := Real.sqrt (max L 0)
  have hK : 0 < K := h3PathSqrtEnergyRiccatiCoefficient_pos
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hSOne : 0 < S + 1 := by linarith
  have hDen : 0 < K * (S + 1) := mul_pos hK hSOne
  let q : ℝ := 1 / (K * (S + 1))
  have hq : 0 < q := one_div_pos.mpr hDen
  have hIdentity : K * q * (S + 1) = 1 := by
    dsimp only [q]
    field_simp [ne_of_gt hK, ne_of_gt hSOne]
    <;> ring
  have hNonneg : 0 ≤ K * q := mul_nonneg (le_of_lt hK) (le_of_lt hq)
  have hBound := mul_le_mul_of_nonneg_left
    (show S ≤ S + 1 by linarith) hNonneg
  have hWindow : K * q * S < 2 := by
    linarith only [hBound, hIdentity]
  exact ⟨q, hq, hWindow⟩

/-- Hypothetical nonextension forces *all* sufficiently late times above
an arbitrary finite H3 energy cutoff, not merely a cofinal sequence. -/
theorem h3PathCanonical_energy_eventually_gt_cutoff_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (L : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      ∀ t : ℝ, t ∈ Set.Ioo c T → L < velocityH3EnergyAt u t := by
  obtain ⟨q, hq, hWindow⟩ :=
    h3PathCanonical_exists_short_terminal_gap_for_cutoff L
  let m : ℝ := h3BKMKineticTailMidpoint a T
  have hm : m ∈ Set.Ioo a T :=
    h3BKMKineticTailMidpoint_mem_Ioo hClass.terminal_start.2
  let c : ℝ := max m (T - q)
  have hc : c ∈ Set.Ioo a T := by
    exact ⟨lt_of_lt_of_le hm.1 (le_max_left m (T - q)),
      max_lt hm.2 (sub_lt_self T hq)⟩
  refine ⟨c, hc, ?_⟩
  intro t ht
  have htOld : t ∈ Set.Ioo a T :=
    ⟨lt_trans hc.1 ht.1, ht.2⟩
  have hLate : T - t < q := by
    have hCeiling : T - q ≤ c := le_max_right m (T - q)
    linarith [ht.1]
  exact h3PathCanonical_energy_gt_cutoff_of_short_terminal_gap
    hH3 hNoExtension hClass htOld hq hWindow hLate

/-- Above a fixed cutoff on a final tail, the localized high-energy moment
is exactly the full square-root H3 energy. -/
theorem h3PathCanonical_highEnergySqrtMoment_eq_sqrt_eventually_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (L : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ c : ℝ, c ∈ Set.Ioo a T ∧
      ∀ t : ℝ, t ∈ Set.Ioo c T →
        h3PathCanonicalHighEnergySqrtMoment u L t =
          Real.sqrt (velocityH3EnergyAt u t) := by
  obtain ⟨c, hc, hHigh⟩ :=
    h3PathCanonical_energy_eventually_gt_cutoff_of_noExtension
      L hH3 hNoExtension hClass
  refine ⟨c, hc, ?_⟩
  intro t ht
  have hNot : ¬ velocityH3EnergyAt u t ≤ L :=
    not_le_of_gt (hHigh t ht)
  simp [h3PathCanonicalHighEnergySqrtMoment, Set.indicator, hNot]

/-- The high-energy square-root H3 moment is nonintegrable on every strict
terminal energy-class tail under nonextension, with no kinetic-mass premise. -/
theorem h3PathCanonical_highEnergySqrtMoment_nonintegrable_without_mass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ} (L : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T) :
    ¬ IntegrableOn (h3PathCanonicalHighEnergySqrtMoment u L)
      (Set.Ioo d T) := by
  intro hMoment
  obtain ⟨c, hc, hEq⟩ :=
    h3PathCanonical_highEnergySqrtMoment_eq_sqrt_eventually_of_noExtension
      L hH3 hNoExtension hClass
  let r : ℝ := max d c
  have hr : r ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hd.1 (le_max_left d c), max_lt hd.2 hc.2⟩
  have hMomentR : IntegrableOn
      (h3PathCanonicalHighEnergySqrtMoment u L) (Set.Ioo r T) := by
    apply hMoment.mono_set
    intro t ht
    exact ⟨lt_of_le_of_lt (le_max_left d c) ht.1, ht.2⟩
  have hSqrtR : IntegrableOn
      (fun t : ℝ => Real.sqrt (velocityH3EnergyAt u t))
      (Set.Ioo r T) := by
    apply Integrable.congr hMomentR
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hEq t ⟨lt_of_le_of_lt (le_max_right d c) ht.1, ht.2⟩
  have hClassR : PreterminalH3EnergyClass u r T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hr.1) hr.2
  exact
    (not_integrableOn_sqrt_velocityH3EnergyAt_on_energyClassTail_of_noH3PathExtension
      hH3 hNoExtension hClassR) hSqrtR

/-- No kinetic positivity assumption is needed to force a high-energy
square-root moment on every terminal subtail: the Riccati clock suffices. -/
theorem h3PathCanonical_highEnergySqrtMoment_continuation_or_obstruction_without_mass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (L : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ d : ℝ, d ∈ Set.Ioo a T →
      ¬ IntegrableOn (h3PathCanonicalHighEnergySqrtMoment u L)
        (Set.Ioo d T) := by
  by_cases hExtension : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · right
    intro d hd
    exact h3PathCanonical_highEnergySqrtMoment_nonintegrable_without_mass
      L hH3 hExtension hClass hd

end Euclidean
end Bridge
end PrimeTensor
