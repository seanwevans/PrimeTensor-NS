import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCertifiedSpectralPackingLedger
import Mathlib.Tactic

/-!
# Certified signed sixth flux: quantitative low-frequency occupancy

The accepted global inverse-eleventh-power ledger charges only those kinetic
inter-window gaps equipped with ACTUAL physical annular peak/width/cost
certificates. It does not postulate adverse signed flux on every gap.

Here we count the active, physically certified gaps whose selected outer
frequency Q(k) is <= B among the first m original kinetic gaps. Each such
gap carries at least h^2/(32 K(E0) (B+1)^11) of global dissipation debt.
Consequently their number times this positive amount is no greater than
the one terminal full-H3 dissipation integral.

The count is written as a finite real-valued sum of 0/1 indicators to avoid
imposing computability of the physical activity predicate. Its value is the
ordinary finite cardinality of the selected set. No rate of Q(k) growth,
no frequency monotonicity, no terminal H3 trace, and no additional PDE
hypothesis are assumed. This is a necessary physical occupancy constraint.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open Classical
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Real-valued cardinality of physical active-gap certificates among the
first m natural gaps whose actual peak-carrying cutoff is at most B. -/
noncomputable def thirdFullKineticSignedLowMaxCertifiedLowFrequencyCount244
    (active : ℕ → Prop) (Q : ℕ → ℕ) (B m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m,
    if active k ∧ Q k ≤ B then (1 : ℝ) else 0

/-- Inverse-eleventh global packing quantitatively limits how many active
annular certificates may be assigned to a fixed frequency ceiling B.
This uses the SAME Q(k) as the previously proved physical certificate. -/
theorem thirdFullKinetic_signedLowMax_inverseEleventh_frequencyOccupancy244
    (active : ℕ → Prop) (Q : ℕ → ℕ)
    (K h Budget : ℝ) (hK : 0 < K)
    (B m : ℕ)
    (hLedger :
      (∑ k ∈ Finset.range m,
        if active k then
          (h ^ 2 / (32 * K)) / (((Q k : ℝ) + 1) ^ 11)
        else 0) ≤ Budget) :
    thirdFullKineticSignedLowMaxCertifiedLowFrequencyCount244 active Q B m *
        (h ^ 2 / (32 * K)) ≤
      ((B : ℝ) + 1) ^ 11 * Budget := by
  let c : ℝ := h ^ 2 / (32 * K)
  let P : ℝ := ((B : ℝ) + 1) ^ 11
  have hc : 0 ≤ c := by
    dsimp only [c]
    exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) hK.le)
  have hP : 0 < P := by dsimp only [P]; positivity
  have hTerm (k : ℕ) :
      (if active k ∧ Q k ≤ B then c / P else 0) ≤
      (if active k then c / (((Q k : ℝ) + 1) ^ 11) else 0) := by
    by_cases hMarked : active k ∧ Q k ≤ B
    · have hActive : active k := hMarked.1
      have hQB : Q k ≤ B := hMarked.2
      simp only [if_pos hMarked, if_pos hActive]
      have hCast : (Q k : ℝ) ≤ (B : ℝ) := Nat.cast_le.mpr hQB
      have hRad : (Q k : ℝ) + 1 ≤ (B : ℝ) + 1 := by
        linarith only [hCast]
      have hPower : ((Q k : ℝ) + 1) ^ 11 ≤ P := by
        dsimp only [P]
        exact pow_le_pow_left₀ (by positivity) hRad 11
      have hQPos : 0 < ((Q k : ℝ) + 1) ^ 11 := by positivity
      exact (div_le_div_iff₀ hP hQPos).mpr
        (mul_le_mul_of_nonneg_left hPower hc)
    · simp only [if_neg hMarked]
      by_cases ha : active k
      · simp only [if_pos ha]
        exact div_nonneg hc (by positivity)
      · simpa only [if_neg ha] using (le_refl (0 : ℝ))
  have hSum :
      (∑ k ∈ Finset.range m,
        if active k ∧ Q k ≤ B then c / P else 0) ≤ Budget := by
    calc
      _ ≤ (∑ k ∈ Finset.range m,
            if active k then c / (((Q k : ℝ) + 1) ^ 11) else 0) :=
        Finset.sum_le_sum (fun k _hk => hTerm k)
      _ ≤ Budget := by simpa only [c] using hLedger
  have hSumEq :
      (∑ k ∈ Finset.range m,
        if active k ∧ Q k ≤ B then c / P else 0) =
        thirdFullKineticSignedLowMaxCertifiedLowFrequencyCount244 active Q B m *
          (c / P) := by
    unfold thirdFullKineticSignedLowMaxCertifiedLowFrequencyCount244
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _hk
    split_ifs <;> ring
  have hCountPaid :
      thirdFullKineticSignedLowMaxCertifiedLowFrequencyCount244 active Q B m *
        (c / P) ≤ Budget := by
    rw [hSumEq] at hSum
    exact hSum
  have hScaled := mul_le_mul_of_nonneg_right hCountPaid hP.le
  change thirdFullKineticSignedLowMaxCertifiedLowFrequencyCount244 active Q B m * c ≤
    P * Budget
  calc
    thirdFullKineticSignedLowMaxCertifiedLowFrequencyCount244 active Q B m * c =
        (thirdFullKineticSignedLowMaxCertifiedLowFrequencyCount244 active Q B m *
          (c / P)) * P := by
      rw [mul_assoc, div_mul_cancel₀ c hP.ne']
    _ ≤ Budget * P := hScaled
    _ = P * Budget := by ring

/-- If every one of the first m indices is genuinely active and its physical
annular cutoff remains below B, then the global budget must pay m times
the same positive per-certificate debt. No monotone frequency selection. -/
theorem thirdFullKinetic_signedLowMax_denseLowFrequencyCost244
    (active : ℕ → Prop) (Q : ℕ → ℕ)
    (K h Budget : ℝ) (hK : 0 < K)
    (B m : ℕ)
    (hActive : ∀ k ∈ Finset.range m, active k)
    (hBound : ∀ k ∈ Finset.range m, Q k ≤ B)
    (hLedger :
      (∑ k ∈ Finset.range m,
        if active k then
          (h ^ 2 / (32 * K)) / (((Q k : ℝ) + 1) ^ 11)
        else 0) ≤ Budget) :
    (m : ℝ) * (h ^ 2 / (32 * K)) ≤
      ((B : ℝ) + 1) ^ 11 * Budget := by
  have hCount :
      thirdFullKineticSignedLowMaxCertifiedLowFrequencyCount244 active Q B m =
        (m : ℝ) := by
    unfold thirdFullKineticSignedLowMaxCertifiedLowFrequencyCount244
    calc
      (∑ k ∈ Finset.range m,
        if active k ∧ Q k ≤ B then (1 : ℝ) else 0) =
          (∑ _k ∈ Finset.range m, (1 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact if_pos ⟨hActive k hk, hBound k hk⟩
      _ = (m : ℝ) := by simp
  have hPack :=
    thirdFullKinetic_signedLowMax_inverseEleventh_frequencyOccupancy244
      active Q K h Budget hK B m hLedger
  simpa only [hCount] using hPack

/-- Physical quantitative frequency-occupancy bound: certificates carrying
actual annular peaks and gap charges cannot return too often to a bounded
outer spectral range without exhausting the ONE terminal H3 budget. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_certifiedFrequencyOccupancy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (M : ℕ → ℝ) (tau : ℕ → ℝ) (N : ℕ → ℕ)
    (delta : ℕ → ℝ) (v : ℕ → ℕ)
    (hSeparated : ∀ k l : ℕ, k < l →
      tau (v k) + delta (v k) < tau (v l))
    (hWindows : ∀ k : ℕ,
      tau (v k) ∈ Set.Ioo b T ∧
      ThirdFullKineticNaturalAnnularLocalWitness244
        hH3 b (tau (v k)) (v k) (N (v k))
        (M (v k)) (delta (v k)))
    (eta E : ℝ) (hEta : 0 < eta) (hE : 0 ≤ E)
    (active : ℕ → Prop) (R Q : ℕ → ℕ) (t w : ℕ → ℝ)
    (hCertified : ∀ k : ℕ, active k →
      ThirdFullKineticSignedLowMaxGapPackingCertificate244
        hH3 eta b tau delta v R Q t w k)
    (hEnergyCap : ∀ k : ℕ, active k →
      velocityH3EnergyAt u (t k) ≤ E)
    (hLowDensity : ∀ k : ℕ, active k →
      16 * (∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
        velocityH3DissipationAt u r ∂volume) <
      (tau (v (k + 1)) - (tau (v k) + delta (v k))) *
        thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E)
    (B m : ℕ) :
    thirdFullKineticSignedLowMaxCertifiedLowFrequencyCount244 active Q B m *
      ((thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E) ^ 2 /
        (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244
          (velocityH3Energy0At u b))) ≤
      ((B : ℝ) + 1) ^ 11 *
        (∫ r in a..T, velocityH3DissipationAt u r ∂volume) := by
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let E0 : ℝ := velocityH3Energy0At u b
  let K : ℝ := thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0
  have hK : 0 < K :=
    thirdFullKinetic_signedLowMax_criticalTwelveCoeff_pos244 E0
      (velocityH3Energy0At_nonneg u b)
  have hLedger :
      (∑ k ∈ Finset.range m,
        if active k then (h ^ 2 / (32 * K)) /
          (((Q k : ℝ) + 1) ^ 11) else 0) ≤
        ∫ r in a..T, velocityH3DissipationAt u r ∂volume := by
    exact thirdFullPhysical_kineticGaps_signedLowMax_certifiedFinitePacking244
      hH3 hClass hDInt b hb M tau N delta v hSeparated hWindows
      eta E hEta hE active R Q t w hCertified hEnergyCap hLowDensity m
  exact thirdFullKinetic_signedLowMax_inverseEleventh_frequencyOccupancy244
    active Q K h
    (∫ r in a..T, velocityH3DissipationAt u r ∂volume)
    hK B m hLedger

end
end PrimeTensor.FirstMonomialTriad
