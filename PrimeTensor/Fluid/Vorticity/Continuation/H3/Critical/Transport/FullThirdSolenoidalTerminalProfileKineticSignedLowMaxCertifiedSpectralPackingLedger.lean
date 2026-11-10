import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCertifiedFrequencyTimeCompression
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointCostSum244
import Mathlib.Tactic

/-!
# Signed sixth flux: finite global packing of certified physical annuli

The previous theorem retains a real finite-annular H3 dissipation peak, its
physical persistence width, and a gap-local eleventh-power frequency charge.
A SINGLE charged gap can have an arbitrarily large outer frequency; the
point of this module is to sum the charges on the ORIGINAL separated gaps.

We prove an actual global finite-sum bound for the intervening physical
H3 dissipation, using the established nonnegative disjoint-interval lemma.
Then, for any selection of genuinely certified adverse annuli with a fixed
positive capped physical height floor h, the inverse-eleventh-power
frequency debts obey the global L1 dissipation budget:

  sum_{k < m, active(k)} [h²/(32 K(E0) (Q(k)+1)^11)]
    <= integral_a^T D_H3(r) dr.

The certificate retains the SAME physical annulus Q(k), positive peak, exact
kinetic persistence width and in-gap charge. Only active samples pay the
debt. No assumption that adverse observations occur on every gap, no
uniformly bounded annular frequency, no terminal H3 trace, and no new PDE
axiom is made. This is a necessary summability/concentration condition,
not a contradiction with finite full-H3 dissipation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open Classical
open scoped BigOperators Interval ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The full physical H3 dissipation on the original, separated inter-window
gaps has bounded finite partial sums. This uses the actual terminal L1
hypothesis, not merely the pointwise fact D(k) tends to zero. -/
theorem thirdFullPhysical_kineticGaps_fullDissipation_finitePacking244
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
    (m : ℕ) :
    (∑ k ∈ Finset.range m,
      ∫ r in (tau (v k) + delta (v k))..tau (v (k + 1)),
        velocityH3DissipationAt u r ∂volume) ≤
      ∫ r in a..T, velocityH3DissipationAt u r ∂volume := by
  let x : ℕ → ℝ := fun k => tau (v k) + delta (v k)
  let y : ℕ → ℝ := fun k => tau (v (k + 1))
  let width : ℕ → ℝ := fun k => y k - x k
  have hxy (k : ℕ) : x k < y k :=
    hSeparated k (k + 1) (Nat.lt_succ_self k)
  have hEq (k : ℕ) : x k + width k = y k := by
    dsimp only [width]
    ring
  have hStart (k : ℕ) : a ≤ x k := by
    obtain ⟨hTime, hw⟩ := hWindows k
    rcases hw with ⟨_, hdelta, _, _, _, _⟩
    dsimp only [x]
    linarith only [hb.1, hTime.1, hdelta]
  have hWidth (k : ℕ) : 0 ≤ width k :=
    sub_nonneg.mpr (hxy k).le
  have hEnd (k : ℕ) : x k + width k ≤ T := by
    rw [hEq]
    exact (hWindows (k + 1)).1.2.le
  have hSeparate (k : ℕ) : x k + width k ≤ x (k + 1) := by
    rw [hEq]
    obtain ⟨_, hw⟩ := hWindows (k + 1)
    rcases hw with ⟨_, hdelta, _, _, _, _⟩
    dsimp only [x, y]
    linarith only [hdelta]
  have hRaw := h3Path_disjointNonnegativeWindows_finiteIntegralSum_le244
    (velocityH3DissipationAt u) a T x width
    hClass.terminal_start.2.le
    (fun r => velocityH3DissipationAt_nonneg u r)
    hDInt hStart hWidth hEnd hSeparate m
  simp only [hEq] at hRaw
  simpa only [x, y] using hRaw

/-- A certificate is not a free outer natural number: its selected annulus
has a peak in the genuine physical H3 dissipation at the selected time,
its exact in-gap persistence width, and its paid full-H3 gap charge. -/
def ThirdFullKineticSignedLowMaxGapPackingCertificate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (eta b : ℝ) (tau delta : ℕ → ℝ) (v : ℕ → ℕ)
    (R Q : ℕ → ℕ) (t w : ℕ → ℝ) (k : ℕ) : Prop :=
  let x := tau (v k) + delta (v k)
  let y := tau (v (k + 1))
  let H := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
    (R k) eta (velocityH3EnergyAt u (t k))
  let E0 := velocityH3Energy0At u b
  let D := ∫ r in x..y, velocityH3DissipationAt u r ∂volume
  t k ∈ Set.Icc x y ∧ R k ≤ Q k ∧ 0 < w k ∧
    w k = thirdFullKineticSignedLowMaxSymmetricGapWidth244
      (R k) (Q k) E0 H x y ∧
    H / 2 <
      h3PathActualLowRadialDissipation244 ((Q k : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (t k)) -
      h3PathActualLowRadialDissipation244 ((R k : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (t k)) ∧
    w k * (H / 4) ≤ D

/-- A scalar finite packing inequality for any selected subset of gaps.
The predicate can be false on arbitrary indices; consequently NO adverse
signed-flux observation is postulated on every gap. -/
theorem thirdFullKinetic_signedLowMax_inverseEleventh_finitePacking244
    (D : ℕ → ℝ) (Q : ℕ → ℕ) (active : ℕ → Prop)
    (K h : ℝ) (hD : ∀ k : ℕ, 0 ≤ D k)
    (hCharge : ∀ k : ℕ, active k →
      h ^ 2 / (32 * K) ≤ ((Q k : ℝ) + 1) ^ 11 * D k)
    (m : ℕ) :
    (∑ k ∈ Finset.range m,
      if active k then
        (h ^ 2 / (32 * K)) / (((Q k : ℝ) + 1) ^ 11)
      else 0) ≤
    ∑ k ∈ Finset.range m, D k := by
  classical
  apply Finset.sum_le_sum
  intro k hk
  by_cases ha : active k
  · simp only [if_pos ha]
    have hPow : 0 < ((Q k : ℝ) + 1) ^ 11 := by positivity
    apply (div_le_iff₀ hPow).mpr
    calc
      h ^ 2 / (32 * K) ≤ ((Q k : ℝ) + 1) ^ 11 * D k := hCharge k ha
      _ = D k * ((Q k : ℝ) + 1) ^ 11 := by ring
  · simpa only [if_neg ha] using hD k

/-- Physical global packing theorem. Every active gap must be equipped with
a certified REAL annular H3 peak/width/charge at its selected outer radius;
its height parameter is the original positive eta. The physical
height floor and positive energy cap use that same eta. The
certificate's selected Q is the one charged in the inverse-power ledger. -/
theorem thirdFullPhysical_kineticGaps_signedLowMax_certifiedFinitePacking244
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
    (m : ℕ) :
    (∑ k ∈ Finset.range m,
      if active k then
        ((thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E) ^ 2 /
          (32 * thirdFullKineticSignedLowMaxCriticalTwelveCoeff244
            (velocityH3Energy0At u b))) /
          (((Q k : ℝ) + 1) ^ 11)
      else 0) ≤
      ∫ r in a..T, velocityH3DissipationAt u r ∂volume := by
  let h : ℝ := thirdFullKineticSignedLowMaxCappedLinearHeightFloor244 eta E
  let E0 : ℝ := velocityH3Energy0At u b
  let K : ℝ := thirdFullKineticSignedLowMaxCriticalTwelveCoeff244 E0
  let x : ℕ → ℝ := fun k => tau (v k) + delta (v k)
  let y : ℕ → ℝ := fun k => tau (v (k + 1))
  let D : ℕ → ℝ := fun k =>
    ∫ r in x k..y k, velocityH3DissipationAt u r ∂volume
  have hh : 0 < h :=
    thirdFullKinetic_signedLowMax_cappedLinearFloor_pos244 eta E hEta hE
  have hE0 : 0 ≤ E0 := velocityH3Energy0At_nonneg u b
  have hxy (k : ℕ) : x k < y k :=
    hSeparated k (k + 1) (Nat.lt_succ_self k)
  have hD (k : ℕ) : 0 ≤ D k := by
    dsimp only [D]
    exact intervalIntegral.integral_nonneg (hxy k).le
      (fun r _ => velocityH3DissipationAt_nonneg u r)
  have hCharge (k : ℕ) (hk : active k) :
      h ^ 2 / (32 * K) ≤ ((Q k : ℝ) + 1) ^ 11 * D k := by
    obtain ⟨_ht, hRQ, _hwPos, hw, _hPeak, hCost⟩ := hCertified k hk
    let H : ℝ := thirdFullKineticSignedLowMaxLinearPhysicalViscousHeight244
      (R k) eta (velocityH3EnergyAt u (t k))
    have hEt0 : 0 ≤ velocityH3EnergyAt u (t k) := by
      have hOne := one_le_velocityH3EnergyAt u (t k)
      linarith only [hOne]
    have hHeight : h ≤ H :=
      thirdFullKinetic_signedLowMax_linearHeight_ge_cappedFloor244
        (R k) eta (velocityH3EnergyAt u (t k)) E
        hEta hEt0 (hEnergyCap k hk)
    have hH : 0 < H := lt_of_lt_of_le hh hHeight
    have hWidth : w k = thirdFullKineticSignedLowMaxSymmetricGapWidth244
        (R k) (Q k) E0 H (x k) (y k) := by
      simpa only [H, E0, x, y] using hw
    have hCost' : w k * (H / 4) ≤ D k := by
      simpa only [H, D, x, y] using hCost
    have hLow : 16 * D k < (y k - x k) * h := by
      simpa only [D, x, y, h] using hLowDensity k hk
    have hPaid := thirdFullKinetic_signedLowMax_certifiedWidth_eleventhCharge244
      (R k) (Q k) E0 H h (x k) (y k) (w k) (D k)
      hE0 hH hh hHeight (hxy k) hRQ (hD k) hWidth hCost'
      hLow
    simpa only [K] using hPaid
  have hLocal := thirdFullKinetic_signedLowMax_inverseEleventh_finitePacking244
    D Q active K h hD hCharge m
  have hGlobal := thirdFullPhysical_kineticGaps_fullDissipation_finitePacking244
    hH3 hClass hDInt b hb M tau N delta v hSeparated hWindows m
  change (∑ k ∈ Finset.range m,
      if active k then (h ^ 2 / (32 * K)) / ((Q k : ℝ) + 1) ^ 11 else 0) ≤
    ∫ r in a..T, velocityH3DissipationAt u r ∂volume
  exact hLocal.trans (by simpa only [D, x, y] using hGlobal)

end
end PrimeTensor.FirstMonomialTriad
