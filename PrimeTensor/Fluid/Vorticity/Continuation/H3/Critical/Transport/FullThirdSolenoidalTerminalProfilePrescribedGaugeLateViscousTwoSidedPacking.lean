import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousTrimmedClockCharge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Two-sided physical PDE-clock packing without counting overlap twice

The primary clock [r,r+eta1] and secondary clock [s,s+eta2] obey r <= s.
The established prefix ledger charges [r,min(r+eta1,s)] together with the
WHOLE secondary window. A complementary surgery charges the WHOLE primary
window together with the nonoverlapping secondary SUFFIX past r+eta1.

Let L := min eta2 (max 0 (s+eta2-(r+eta1))). The two valid charges and the
primary's original standalone charge give a sharp, overlap-safe MAX ledger:

  max (eta1*A)
      (max (min eta1 (s-r)*A + eta2*H)
           (eta1*A + L*H)) <= integral_m^T D_H3.

The second term prevents loss of all secondary information when the primary
has a long unshared prefix. The third retains the entire primary clock in
cases where the secondary interval begins at r or overlaps strongly.
Nothing is summed across intersecting intervals and no positive independent
lower bound for either clock duration is assumed. The cofinal lift retains
the original minimal first-crossing witnesses and physical H3 viscous budget.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- In the partially overlapping case, retain the FULL primary clock and
the part of the SECONDARY clock strictly to the right of the primary end.
These intervals are ordered and do not double-charge their common region. -/
theorem thirdFull_scalar_twoClocks_overlappingSecondarySuffixCharge244
    (f : ℝ → ℝ) (m T r s eta theta A H : ℝ)
    (hInt : IntervalIntegrable f volume m T)
    (hmT : m ≤ T) (hPos : ∀ x : ℝ, 0 ≤ f x)
    (hmr : m ≤ r) (hrs : r ≤ s)
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hOverlap : s ≤ r + eta) (hCross : r + eta ≤ s + theta)
    (hEnd : s + theta ≤ T)
    (hFirst : ∀ x : ℝ, x ∈ Set.Icc r (r + eta) → A ≤ f x)
    (hSecond : ∀ x : ℝ, x ∈ Set.Icc s (s + theta) → H ≤ f x) :
    eta * A + (s + theta - (r + eta)) * H ≤
      ∫ x in m..T, f x ∂volume := by
  have hEtaEnd : r + eta ≤ T := hCross.trans hEnd
  have hSuffix : 0 ≤ s + theta - (r + eta) := sub_nonneg.mpr hCross
  have hEndEq : (r + eta) + (s + theta - (r + eta)) = s + theta := by
    ring
  have hin (x y : ℝ) (hmx : m ≤ x) (hxy : x ≤ y)
      (hyT : y ≤ T) : IntervalIntegrable f volume x y := by
    apply hInt.mono_set
    intro z hz
    have hzIcc : z ∈ Set.Icc x y := by
      simpa only [Set.uIcc_of_le hxy] using hz
    have hzMain : z ∈ Set.Icc m T :=
      ⟨hmx.trans hzIcc.1, hzIcc.2.trans hyT⟩
    simpa only [Set.uIcc_of_le hmT] using hzMain
  have hFirstInt : IntervalIntegrable f volume r (r + eta) :=
    hin r (r + eta) hmr (le_add_of_nonneg_right heta) hEtaEnd
  have hSecondInt : IntervalIntegrable f volume (r + eta) (s + theta) :=
    hin (r + eta) (s + theta)
      (hmr.trans (le_add_of_nonneg_right heta)) hCross hEnd
  have hFirstCost : eta * A ≤
      ∫ x in r..(r + eta), f x ∂volume := by
    have hCompare :
        (∫ _x in r..(r + eta), A ∂volume) ≤
          ∫ x in r..(r + eta), f x ∂volume := by
      apply intervalIntegral.integral_mono_on
        (le_add_of_nonneg_right heta) intervalIntegrable_const hFirstInt
      intro x hx
      exact hFirst x hx
    calc
      eta * A = ∫ _x in r..(r + eta), A ∂volume := by
        simp <;> ring
      _ ≤ ∫ x in r..(r + eta), f x ∂volume := hCompare
  have hSecondCost : (s + theta - (r + eta)) * H ≤
      ∫ x in (r + eta)..(s + theta), f x ∂volume := by
    have hCompare :
        (∫ _x in (r + eta)..(s + theta), H ∂volume) ≤
          ∫ x in (r + eta)..(s + theta), f x ∂volume := by
      apply intervalIntegral.integral_mono_on hCross
        intervalIntegrable_const hSecondInt
      intro x hx
      exact hSecond x ⟨hOverlap.trans hx.1, hx.2⟩
    calc
      (s + theta - (r + eta)) * H =
          ∫ _x in (r + eta)..(s + theta), H ∂volume := by
        simp <;> ring
      _ ≤ ∫ x in (r + eta)..(s + theta), f x ∂volume := hCompare
  have hOrdered := thirdFull_scalar_orderedTwoWindows_additiveTailCharge244
    f m T r (r + eta) eta (s + theta - (r + eta)) A H
    hInt hmT hPos hmr heta (le_refl _) hSuffix
    (by simpa only [hEndEq] using hEnd)
    hFirstCost (by simpa only [hEndEq] using hSecondCost)
  exact hOrdered

/-- Every ordered pair of clocks has a valid *full-primary plus secondary
suffix* charge. When the secondary lies entirely inside the primary there
is no suffix; when disjoint the suffix is the whole secondary interval. -/
theorem thirdFull_scalar_orderedTwoClocks_secondarySuffixCharge244
    (f : ℝ → ℝ) (m T r s eta theta A H : ℝ)
    (hInt : IntervalIntegrable f volume m T)
    (hmT : m ≤ T) (hPos : ∀ x : ℝ, 0 ≤ f x)
    (hmr : m ≤ r) (hrs : r ≤ s)
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hEnd1 : r + eta ≤ T) (hEnd2 : s + theta ≤ T)
    (hFirst : ∀ x : ℝ, x ∈ Set.Icc r (r + eta) → A ≤ f x)
    (hSecond : ∀ x : ℝ, x ∈ Set.Icc s (s + theta) → H ≤ f x) :
    eta * A + (min theta (max 0 (s + theta - (r + eta)))) * H ≤
      ∫ x in m..T, f x ∂volume := by
  by_cases hSeparated : r + eta ≤ s
  · have hTrim := thirdFull_scalar_orderedTwoClocks_trimmedPrefixCharge244
      f m T r s eta theta A H hInt hmT hPos hmr hrs heta htheta
      hEnd2 hFirst hSecond
    have hPrefixEq : min eta (s - r) = eta :=
      min_eq_left (by linarith only [hSeparated])
    have hSecondBound : theta ≤ s + theta - (r + eta) := by
      linarith only [hSeparated]
    have hSecondNonneg : 0 ≤ s + theta - (r + eta) := by
      linarith only [hSecondBound, htheta]
    have hSuffixEq :
        min theta (max 0 (s + theta - (r + eta))) = theta := by
      rw [max_eq_right hSecondNonneg, min_eq_left hSecondBound]
    simpa only [hPrefixEq, hSuffixEq] using hTrim
  · have hOverlap : s ≤ r + eta := (lt_of_not_ge hSeparated).le
    by_cases hInside : s + theta ≤ r + eta
    · have hSub : s + theta - (r + eta) ≤ 0 := by
        linarith only [hInside]
      have hSuffixEq :
          min theta (max 0 (s + theta - (r + eta))) = 0 := by
        rw [max_eq_left hSub, min_eq_right htheta]
      have hPrimaryTrim := thirdFull_scalar_orderedTwoClocks_trimmedPrefixCharge244
        f m T r (r + eta) eta 0 A 0
        hInt hmT hPos hmr (le_add_of_nonneg_right heta)
        heta (by norm_num)
        (by simpa only [add_zero] using hEnd1)
        hFirst (fun x _ => hPos x)
      have hDiffEq : (r + eta) - r = eta := by ring
      have hPrimary : eta * A ≤ ∫ x in m..T, f x ∂volume := by
        simpa only [hDiffEq, min_self, zero_mul, add_zero] using hPrimaryTrim
      simpa only [hSuffixEq, zero_mul, add_zero] using hPrimary
    · have hCross : r + eta ≤ s + theta := le_of_not_ge hInside
      have hSuffix0 : 0 ≤ s + theta - (r + eta) := by
        linarith only [hCross]
      have hSuffixLe : s + theta - (r + eta) ≤ theta := by
        linarith only [hOverlap]
      have hSuffixEq :
          min theta (max 0 (s + theta - (r + eta))) =
            s + theta - (r + eta) := by
        rw [max_eq_right hSuffix0, min_eq_right hSuffixLe]
      have hSuffixCharge :=
        thirdFull_scalar_twoClocks_overlappingSecondarySuffixCharge244
          f m T r s eta theta A H hInt hmT hPos hmr hrs
          heta htheta hOverlap hCross hEnd2 hFirst hSecond
      simpa only [hSuffixEq] using hSuffixCharge

/-- The two overlap-safe surgeries and the standalone primary cost are all
valid lower charges on the SAME integral. Their maximum is still a charge,
not the sum of potentially overlapping three estimates. -/
theorem thirdFull_scalar_orderedTwoClocks_threeWayMaxCharge244
    (B r s eta theta A H : ℝ)
    (hPrimary : eta * A ≤ B)
    (hPrefix : min eta (s - r) * A + theta * H ≤ B)
    (hSuffix : eta * A +
      (min theta (max 0 (s + theta - (r + eta)))) * H ≤ B) :
    max (eta * A)
      (max (min eta (s - r) * A + theta * H)
        (eta * A +
          (min theta (max 0 (s + theta - (r + eta)))) * H)) ≤ B := by
  exact max_le hPrimary (max_le hPrefix hSuffix)

/-- A secondary cost using up the remaining tail forces its attaining time
near the first spike, unless every chosen primary-prefix length is paid.
This is a genuinely quantitative budget-to-temporal-geometry implication. -/
theorem thirdFull_scalar_dualClock_budget_forcesTemporalLocalization244
    (A B r s eta theta H delta : ℝ)
    (hA : 0 ≤ A) (hDelta : delta ≤ eta)
    (hTrim : min eta (s - r) * A + theta * H ≤ B) :
    s < r + delta ∨ delta * A + theta * H ≤ B := by
  by_cases hNear : s < r + delta
  · exact Or.inl hNear
  · right
    have hDeltaTravel : delta ≤ s - r := by
      have hFar := le_of_not_gt hNear
      linarith only [hFar]
    have hDeltaMin : delta ≤ min eta (s - r) :=
      le_min hDelta hDeltaTravel
    have hScale : delta * A ≤ min eta (s - r) * A :=
      mul_le_mul_of_nonneg_right hDeltaMin hA
    linarith only [hScale, hTrim]

/-- Instantiate the three-way maximum ledger on genuine Navier--Stokes
clock certificates. Both primary and secondary observed floors hold for
entire physical time intervals; no independence is assumed. -/
theorem thirdFullPhysical_retainedPrimary_secondaryClock_threeWayPacking244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (m r eta1 A sState sSource h : ℝ)
    (hm : m ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo m T)
    (heta1 : 0 < eta1) (hend1 : r + eta1 < T)
    (hFloor1 : ∀ x : ℝ, x ∈ Set.Icc r (r + eta1) →
      A < velocityH3DissipationAt u x)
    (hPrimary : eta1 * A ≤
      ∫ x in m..T, velocityH3DissipationAt u x ∂volume)
    (hsState : sState ∈ Set.Icc r (r + (T - r) / 2))
    (hsSource : sSource ∈ Set.Icc r (r + (T - r) / 2))
    (hSecondary : ThirdFullLateSecondaryPDEClock244
      hH3 m sState sSource h) :
    ∃ s eta2 : ℝ,
      (s = sState ∨ s = sSource) ∧ r ≤ s ∧
      0 < eta2 ∧ s + eta2 < T ∧
      max (eta1 * A)
        (max (min eta1 (s - r) * A + eta2 * (h / 2))
          (eta1 * A +
            (min eta2 (max 0 (s + eta2 - (r + eta1)))) * (h / 2))) ≤
        ∫ x in m..T, velocityH3DissipationAt u x ∂volume := by
  rcases hSecondary with ⟨s, hChoice, _J2, _zSource, _zState, eta2,
      _hzSource, _hzState, _hEq, heta2, hend2, hFloor2, _hCost⟩
  have hrs : r ≤ s := by
    rcases hChoice with rfl | rfl
    · exact hsState.1
    · exact hsSource.1
  have hDtail : IntervalIntegrable (velocityH3DissipationAt u) volume m T := by
    apply hDInt.mono_set
    intro x hx
    have hxIcc : x ∈ Set.Icc m T := by
      simpa only [Set.uIcc_of_le hm.2.le] using hx
    have hxMain : x ∈ Set.Icc a T :=
      ⟨hm.1.le.trans hxIcc.1, hxIcc.2⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hxMain
  have hPrefix := thirdFull_scalar_orderedTwoClocks_trimmedPrefixCharge244
    (velocityH3DissipationAt u) m T r s eta1 eta2 A (h / 2)
    hDtail hm.2.le (velocityH3DissipationAt_nonneg u)
    hr.1.le hrs heta1.le heta2.le hend2.le
    (fun x hx => (hFloor1 x hx).le)
    (fun x hx => (hFloor2 x hx).2.le)
  have hSuffix := thirdFull_scalar_orderedTwoClocks_secondarySuffixCharge244
    (velocityH3DissipationAt u) m T r s eta1 eta2 A (h / 2)
    hDtail hm.2.le (velocityH3DissipationAt_nonneg u)
    hr.1.le hrs heta1.le heta2.le hend1.le hend2.le
    (fun x hx => (hFloor1 x hx).le)
    (fun x hx => (hFloor2 x hx).2.le)
  have hPacking := thirdFull_scalar_orderedTwoClocks_threeWayMaxCharge244
    (∫ x in m..T, velocityH3DissipationAt u x ∂volume)
    r s eta1 eta2 A (h / 2) hPrimary hPrefix hSuffix
  exact ⟨s, eta2, hChoice, hrs, heta2, hend2, hPacking⟩

/-- Prescribed-gauge late alternatives with the three independent (not
summed) admissible interval charges. The common-max-time location obeys
a quantified proximity-or-prefix-cost rule at every trial distance. -/
def ThirdFullLateRetainedPrimaryTwoSidedPackingLedger244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b m r P V : ℝ) (J : ℕ)
    (sSource sState eta1 : ℝ) : Prop :=
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let R : ℝ := 96 * C0 * (((J : ℝ) + 2) ^ 5)
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ x in m..T, velocityH3DissipationAt u x ∂volume
  (T - r) * A ≤ 4 * B ∨ A ^ 2 ≤ 4 * B ∨
    (A ^ 2 ≤ R *
        (E0 + 3 * velocityH3DissipationAt u sState) *
        (E0 + 3 * velocityH3DissipationAt u sSource) * B ∧
      (4 * R * B * E0 ^ 2 < A ^ 2 →
        ∃ s eta2 : ℝ,
          (s = sState ∨ s = sSource) ∧ r ≤ s ∧
          0 < eta2 ∧ s + eta2 < T ∧
          (let H : ℝ := A / (24 * Real.sqrt (R * B))
           max (eta1 * A)
             (max (min eta1 (s - r) * A + eta2 * H)
               (eta1 * A +
                 (min eta2 (max 0 (s + eta2 - (r + eta1)))) * H)) ≤ B ∧
           (∀ delta : ℝ, delta ≤ eta1 →
             s < r + delta ∨ delta * A + eta2 * H ≤ B))))

/-- Upgrade the original retained primary trimmed ledger. The kinetic-gap
branch selects the very same two-slice physical secondary PDE clock, then
recovers the primary's unshared portion, its entire original charge, and
the secondary unshared right suffix as independent valid lower charges. -/
theorem thirdFullPhysical_retainedPrimary_ledger_to_twoSidedPacking244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (m : ℝ) (hm : m ∈ Set.Ioo b T)
    (r P V : ℝ) (J : ℕ)
    (hr : r ∈ Set.Ioo m T) (hP : 0 < P) (hV : 0 < V)
    (sSource sState eta1 : ℝ)
    (hsSource : sSource ∈ Set.Icc r (r + (T - r) / 2))
    (hsState : sState ∈ Set.Icc r (r + (T - r) / 2))
    (heta1 : 0 < eta1) (hend1 : r + eta1 < T)
    (hFloor : ∀ x : ℝ, x ∈ Set.Icc r (r + eta1) →
      V / (2 * P) < velocityH3DissipationAt u x)
    (hCharge : eta1 * (V / (2 * P)) ≤
      ∫ x in m..T, velocityH3DissipationAt u x ∂volume)
    (hLedger : ThirdFullLateRetainedPrimaryTrimmedCofinalLedger244
      hH3 b m r P V J sSource sState eta1) :
    ThirdFullLateRetainedPrimaryTwoSidedPackingLedger244
      hH3 b m r P V J sSource sState eta1 := by
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ x in m..T, velocityH3DissipationAt u x ∂volume
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let S : ℝ := (((J : ℝ) + 2) ^ 5)
  let R : ℝ := 96 * C0 * S
  change (T - r) * A ≤ 4 * B ∨ A ^ 2 ≤ 4 * B ∨
    (A ^ 2 ≤ R *
        (E0 + 3 * velocityH3DissipationAt u sState) *
        (E0 + 3 * velocityH3DissipationAt u sSource) * B ∧
      (4 * R * B * E0 ^ 2 < A ^ 2 →
        ∃ s eta2 : ℝ,
          (s = sState ∨ s = sSource) ∧ r ≤ s ∧
          0 < eta2 ∧ s + eta2 < T ∧
          (let H : ℝ := A / (24 * Real.sqrt (R * B))
           max (eta1 * A)
             (max (min eta1 (s - r) * A + eta2 * H)
               (eta1 * A +
                 (min eta2 (max 0 (s + eta2 - (r + eta1)))) * H)) ≤ B ∧
           (∀ delta : ℝ, delta ≤ eta1 →
             s < r + delta ∨ delta * A + eta2 * H ≤ B))))
  change (T - r) * A ≤ 4 * B ∨ A ^ 2 ≤ 4 * B ∨
    (A ^ 2 ≤ R *
        (E0 + 3 * velocityH3DissipationAt u sState) *
        (E0 + 3 * velocityH3DissipationAt u sSource) * B ∧
      (4 * R * B * E0 ^ 2 < A ^ 2 →
        ∃ s eta2 : ℝ,
          (s = sState ∨ s = sSource) ∧ r ≤ s ∧
          0 < eta2 ∧ s + eta2 < T ∧
          min eta1 (s - r) * A +
            eta2 * (A / (24 * Real.sqrt (R * B))) ≤ B)) at hLedger
  rcases hLedger with hTime | hTail | ⟨hRate, _hPrevious⟩
  · exact Or.inl hTime
  · exact Or.inr (Or.inl hTail)
  right; right
  refine ⟨hRate, ?_⟩
  intro hGap
  have hA : 0 < A := by dsimp only [A]; positivity
  have hC0 : 0 < C0 := by
    dsimp only [C0]
    have hCoeff := h3AuditInitialLerayEnergyCoefficient_nonneg
    linarith only [hCoeff]
  have hE0 : 0 ≤ E0 := by
    dsimp only [E0]
    have hEnergy := velocityH3Energy0At_nonneg u b
    linarith only [hEnergy]
  have hS : 0 < S := by dsimp only [S]; positivity
  have hR : 0 < R := by dsimp only [R]; positivity
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact intervalIntegral.integral_nonneg hm.2.le
      (fun x _ => velocityH3DissipationAt_nonneg u x)
  have hB : 0 < B := by
    by_contra hNot
    have hBzero : B = 0 :=
      le_antisymm (le_of_not_gt hNot) hB0
    have hRateZero : A ^ 2 ≤ 0 := by
      simpa only [hBzero, mul_zero] using hRate
    have hPosSq : 0 < A ^ 2 := by positivity
    exact (not_le_of_gt hPosSq) hRateZero
  have hmA : m ∈ Set.Ioo a T := ⟨lt_trans hb.1 hm.1, hm.2⟩
  have hHalfEnd : r + (T - r) / 2 < T := by
    linarith only [hr.2]
  have hsStateTail : sState ∈ Set.Ioo m T :=
    ⟨lt_of_lt_of_le hr.1 hsState.1,
      lt_of_le_of_lt hsState.2 hHalfEnd⟩
  have hsSourceTail : sSource ∈ Set.Ioo m T :=
    ⟨lt_of_lt_of_le hr.1 hsSource.1,
      lt_of_le_of_lt hsSource.2 hHalfEnd⟩
  obtain ⟨_hh, _hSpike, hSecondary⟩ :=
    thirdFullPhysical_twoSlice_constructiveSqrtTailPDEClock244
      hH3 hClass hDInt m sState sSource A B R E0
      hmA hsStateTail hsSourceTail hA hB hR hE0 hRate hGap
  obtain ⟨s, eta2, hWhich, hrs, heta2, hend2, hPacking⟩ :=
    thirdFullPhysical_retainedPrimary_secondaryClock_threeWayPacking244
      hH3 hClass hDInt m r eta1 A sState sSource
      (A / (12 * Real.sqrt (R * B)))
      hmA hr heta1 hend1 (by simpa only [A] using hFloor)
      (by simpa only [A, B] using hCharge)
      hsState hsSource hSecondary
  have hq : 0 < Real.sqrt (R * B) :=
    Real.sqrt_pos.2 (mul_pos hR hB)
  have hHeight :
      (A / (12 * Real.sqrt (R * B))) / 2 =
        A / (24 * Real.sqrt (R * B)) := by
    field_simp [ne_of_gt hq]
    <;> ring
  let H : ℝ := A / (24 * Real.sqrt (R * B))
  have hPackingH :
      max (eta1 * A)
        (max (min eta1 (s - r) * A + eta2 * H)
          (eta1 * A +
            (min eta2 (max 0 (s + eta2 - (r + eta1)))) * H)) ≤ B := by
    simpa only [H, hHeight] using hPacking
  have hPrefix : min eta1 (s - r) * A + eta2 * H ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hPackingH)
  have hLocation (delta : ℝ) (hDelta : delta ≤ eta1) :
      s < r + delta ∨ delta * A + eta2 * H ≤ B :=
    thirdFull_scalar_dualClock_budget_forcesTemporalLocalization244
      A B r s eta1 eta2 H delta hA.le hDelta hPrefix
  refine ⟨s, eta2, hWhich, hrs, heta2, hend2, ?_⟩
  exact ⟨hPackingH, hLocation⟩

/-- On the same original cofinal prescribed-gauge witnesses, retain THREE
non-double-counting physical clock charges and the budget-to-separation
rule on the constructive late rate branch. The spectral and source
threshold alternatives, first-crossing witnesses, frequency escape and
original disjoint viscous charges are unchanged. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_retainedTwoSidedPackingLedger244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (H : ℕ → ℝ) (hH : ∀ n : ℕ, 1 ≤ H n) :
    ∃ (U : H3PhysicalRealFinVectorL2Hilbert)
      (tau : ℕ → ℝ) (N : ℕ → ℕ) (K C delta : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => tau (v k)) atTop (𝓝 T) ∧
      (∀ k, ThirdFullProfileMinimalAttainedSourceWindow244 hH3
        (fun n : ℕ => (H n) ^ 8) tau N K C delta (v k)) ∧
      (∀ j : ℕ,
        (∑ k ∈ Finset.range j,
          delta (v k) * ((H (v k)) ^ 8 / 4)) ≤
            ∫ s in a..T, velocityH3DissipationAt u s) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / H (v k)) atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        let t := tau (v k)
        let m := (t + T) / 2
        let Q := (N (v k) : ℝ) + 2
        let F := h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
        let C0 := 3 + h3AuditInitialLerayEnergyCoefficient
        let E0 := 1 + 6 * velocityH3Energy0At u b
        let P := 168 * Q ^ 4 * (‖F‖ * C0) * (T - m)
        let V := (H (v k)) ^ 4
        V < 14 * Q ^ 4 *
          ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
        (∃ r : ℝ, r ∈ Set.Icc t m ∧
          V < 28 * Q ^ 4 *
            (‖F‖ * ((m - t) *
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖))) ∨
        V < 56 * Q ^ 4 * (‖F‖ * C0 * ((T - m) * E0)) ∨
        (∃ (r : ℝ) (J : ℕ) (sSource sState eta1 : ℝ),
          r ∈ Set.Ioo m T ∧ 0 < P ∧
          sSource ∈ Set.Icc r (r + (T - r) / 2) ∧
          sState ∈ Set.Icc r (r + (T - r) / 2) ∧
          eta1 = min ((T - r) / 4)
            ((V / (2 * P)) /
              (2 * (thirdFullLateViscousLowRadialPDERate244 J
                ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
                ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ + 1))) ∧
          0 < eta1 ∧ r + eta1 < T ∧
          (∀ s : ℝ, s ∈ Set.Icc r (r + eta1) →
            V / (2 * P) <
              h3PathActualLowRadialDissipation244 ((J : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 s) ∧
            V / (2 * P) < velocityH3DissipationAt u s) ∧
          eta1 * (V / (2 * P)) ≤
            ∫ s in m..T, velocityH3DissipationAt u s ∂volume ∧
          ThirdFullLateRetainedPrimaryTwoSidedPackingLedger244
            hH3 b m r P V J sSource sState eta1)) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_retainedTrimmedCofinalLedger244
      hH3 hClass b hb hNoTrace hDInt H hH
  have hAfter : ∀ᶠ k : ℕ in atTop, b < tau (v k) :=
    hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)
  refine ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
    hWindows, hCharges, hEscape, ?_, hViscousTail⟩
  filter_upwards [hOld, hAfter] with k hkOld hkAfter
  dsimp only at hkOld ⊢
  let t : ℝ := tau (v k)
  let m : ℝ := (t + T) / 2
  let Q : ℝ := (N (v k) : ℝ) + 2
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let P : ℝ := 168 * Q ^ 4 * (‖F‖ * C0) * (T - m)
  let V : ℝ := (H (v k)) ^ 4
  rcases hkOld with hCarrier | hSource | hClock |
      ⟨r, J, sSource, sState, eta1, hr, hP,
        hsSource, hsState, hEtaEq, heta1, hend1, hFloor, hCharge, hLedger⟩
  · exact Or.inl hCarrier
  · exact Or.inr (Or.inl hSource)
  · exact Or.inr (Or.inr (Or.inl hClock))
  · right; right; right
    have hmT : m < T := lt_trans hr.1 hr.2
    have htT : t < T := by
      dsimp only [m] at hmT
      linarith only [hmT]
    have htm : t < m := by
      dsimp only [m]
      linarith only [htT]
    have hmB : m ∈ Set.Ioo b T :=
      ⟨lt_trans hkAfter htm, hmT⟩
    have hV : 0 < V := by
      dsimp only [V]
      have hHpos : 0 < H (v k) :=
        lt_of_lt_of_le zero_lt_one (hH (v k))
      positivity
    have hPacking :=
      thirdFullPhysical_retainedPrimary_ledger_to_twoSidedPacking244
        hH3 hClass hDInt b hb m hmB r P V J hr hP hV
        sSource sState eta1 hsSource hsState heta1 hend1
        (fun x hx => (hFloor x hx).2) hCharge hLedger
    exact ⟨r, J, sSource, sState, eta1, hr, hP,
      hsSource, hsState, hEtaEq, heta1, hend1,
      hFloor, hCharge, hPacking⟩


end
end PrimeTensor.FirstMonomialTriad
