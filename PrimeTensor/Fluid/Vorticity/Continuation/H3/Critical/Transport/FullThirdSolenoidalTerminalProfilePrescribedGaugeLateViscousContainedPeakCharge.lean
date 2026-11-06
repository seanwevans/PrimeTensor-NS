import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousTwoSidedPacking
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Recover the primary tail after a contained secondary physical PDE clock

The previously established three-way maximum of two physical persistence
charges loses a genuine positive contribution if the SECONDARY interval is
contained strictly inside the first, and has the higher dissipation floor.
A three-piece partition [r,s], [s,s+theta], [s+theta,r+eta] instead yields

    eta*A + theta*(H-A) <= B

without counting the common interval twice. Combining this with the original
full-primary charge yields eta*A + theta*max 0 (H-A) <= B. This remains
valid when s=r, the case in which the older trimmed-prefix cost vanishes.

The Navier--Stokes specialization uses the SAME physical PDE clock proof and
its genuine full-H3 dissipation floors. The cofinal result retains all the
previous witness data and adds a conditional, stronger contained-peak cost.
No uniformly positive difference H-A is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Three actually disjoint portions of a contained secondary interval:
primary prefix, full secondary interval, and primary suffix. -/
theorem thirdFull_scalar_containedSecondary_threePieceTailCharge244
    (f : ℝ → ℝ) (m T r s eta theta A H : ℝ)
    (hInt : IntervalIntegrable f volume m T)
    (hmT : m ≤ T) (hPos : ∀ x : ℝ, 0 ≤ f x)
    (hmr : m ≤ r) (hrs : r ≤ s)
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hEnd : r + eta ≤ T)
    (hContained : s + theta ≤ r + eta)
    (hFirst : ∀ x : ℝ, x ∈ Set.Icc r (r + eta) → A ≤ f x)
    (hSecond : ∀ x : ℝ, x ∈ Set.Icc s (s + theta) → H ≤ f x) :
    eta * A + theta * (H - A) ≤
      ∫ x in m..T, f x ∂volume := by
  have hse : s ≤ s + theta := le_add_of_nonneg_right htheta
  have hrsEnd : r ≤ r + eta := le_add_of_nonneg_right heta
  have hms : m ≤ s := hmr.trans hrs
  have hme : m ≤ s + theta := hms.trans hse
  have hrse : r ≤ s + theta := hrs.trans hse
  have hsT : s ≤ T := hse.trans (hContained.trans hEnd)
  have hseT : s + theta ≤ T := hContained.trans hEnd
  have hin (x y : ℝ) (hmx : m ≤ x) (hxy : x ≤ y)
      (hyT : y ≤ T) : IntervalIntegrable f volume x y := by
    apply hInt.mono_set
    intro z hz
    have hzIcc : z ∈ Set.Icc x y := by
      simpa only [Set.uIcc_of_le hxy] using hz
    have hzMain : z ∈ Set.Icc m T :=
      ⟨hmx.trans hzIcc.1, hzIcc.2.trans hyT⟩
    simpa only [Set.uIcc_of_le hmT] using hzMain
  have hInt1 : IntervalIntegrable f volume r s :=
    hin r s hmr hrs hsT
  have hInt2 : IntervalIntegrable f volume s (s + theta) :=
    hin s (s + theta) hms hse hseT
  have hInt3 : IntervalIntegrable f volume (s + theta) (r + eta) :=
    hin (s + theta) (r + eta) hme hContained hEnd
  have hInt12 : IntervalIntegrable f volume r (s + theta) :=
    hin r (s + theta) hmr hrse hseT
  have hFirstBound : s ≤ r + eta := hse.trans hContained
  have hPrefix : (s - r) * A ≤
      ∫ x in r..s, f x ∂volume := by
    have hCmp : (∫ _x in r..s, A ∂volume) ≤
        ∫ x in r..s, f x ∂volume := by
      apply intervalIntegral.integral_mono_on hrs
        intervalIntegrable_const hInt1
      intro x hx
      exact hFirst x ⟨hx.1, hx.2.trans hFirstBound⟩
    calc
      (s - r) * A = ∫ _x in r..s, A ∂volume := by
        simp [mul_comm] <;> ring
      _ ≤ ∫ x in r..s, f x ∂volume := hCmp
  have hMiddle : theta * H ≤
      ∫ x in s..(s + theta), f x ∂volume := by
    have hCmp : (∫ _x in s..(s + theta), H ∂volume) ≤
        ∫ x in s..(s + theta), f x ∂volume := by
      apply intervalIntegral.integral_mono_on hse
        intervalIntegrable_const hInt2
      intro x hx
      exact hSecond x hx
    calc
      theta * H = ∫ _x in s..(s + theta), H ∂volume := by
        simp [mul_comm] <;> ring
      _ ≤ ∫ x in s..(s + theta), f x ∂volume := hCmp
  have hSuffix : (r + eta - (s + theta)) * A ≤
      ∫ x in (s + theta)..(r + eta), f x ∂volume := by
    have hCmp : (∫ _x in (s + theta)..(r + eta), A ∂volume) ≤
        ∫ x in (s + theta)..(r + eta), f x ∂volume := by
      apply intervalIntegral.integral_mono_on hContained
        intervalIntegrable_const hInt3
      intro x hx
      exact hFirst x ⟨hrse.trans hx.1, hx.2⟩
    calc
      (r + eta - (s + theta)) * A =
          ∫ _x in (s + theta)..(r + eta), A ∂volume := by
        simp [mul_comm] <;> ring
      _ ≤ ∫ x in (s + theta)..(r + eta), f x ∂volume := hCmp
  have hAdj1 : (∫ x in r..s, f x ∂volume) +
      (∫ x in s..(s + theta), f x ∂volume) =
        ∫ x in r..(s + theta), f x ∂volume :=
    intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2
  have hAdj2 : (∫ x in r..(s + theta), f x ∂volume) +
      (∫ x in (s + theta)..(r + eta), f x ∂volume) =
        ∫ x in r..(r + eta), f x ∂volume :=
    intervalIntegral.integral_add_adjacent_intervals hInt12 hInt3
  have hLocal :
      (s - r) * A + theta * H + (r + eta - (s + theta)) * A ≤
        ∫ x in r..(r + eta), f x ∂volume := by
    calc
      _ ≤ (∫ x in r..s, f x ∂volume) +
          (∫ x in s..(s + theta), f x ∂volume) +
          (∫ x in (s + theta)..(r + eta), f x ∂volume) :=
        add_le_add (add_le_add hPrefix hMiddle) hSuffix
      _ = ∫ x in r..(r + eta), f x ∂volume := by
        rw [hAdj1, hAdj2]
  have hNonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc m T)] f := by
    filter_upwards [] with x
    exact hPos x
  have hTail :
      (∫ x in r..(r + eta), f x ∂volume) ≤
        ∫ x in m..T, f x ∂volume :=
    intervalIntegral.integral_mono_interval
      hmr hrsEnd hEnd hNonneg hInt
  calc
    eta * A + theta * (H - A) =
        (s - r) * A + theta * H + (r + eta - (s + theta)) * A := by ring
    _ ≤ ∫ x in r..(r + eta), f x ∂volume := hLocal
    _ ≤ ∫ x in m..T, f x ∂volume := hTail

/-- The contained secondary clock pays only the *excess* of its height over
the original floor. If it is shorter, the primary cost remains intact. -/
theorem thirdFull_scalar_containedSecondary_positiveExcessCharge244
    (f : ℝ → ℝ) (m T r s eta theta A H : ℝ)
    (hInt : IntervalIntegrable f volume m T)
    (hmT : m ≤ T) (hPos : ∀ x : ℝ, 0 ≤ f x)
    (hmr : m ≤ r) (hrs : r ≤ s)
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hEnd : r + eta ≤ T)
    (hContained : s + theta ≤ r + eta)
    (hFirst : ∀ x : ℝ, x ∈ Set.Icc r (r + eta) → A ≤ f x)
    (hSecond : ∀ x : ℝ, x ∈ Set.Icc s (s + theta) → H ≤ f x) :
    eta * A + theta * max 0 (H - A) ≤
      ∫ x in m..T, f x ∂volume := by
  by_cases hAH : A ≤ H
  · have hExcess : 0 ≤ H - A := sub_nonneg.mpr hAH
    have hCost := thirdFull_scalar_containedSecondary_threePieceTailCharge244
      f m T r s eta theta A H hInt hmT hPos hmr hrs heta htheta
      hEnd hContained hFirst hSecond
    simpa only [max_eq_right hExcess] using hCost
  · have hExcess : H - A ≤ 0 := sub_nonpos.mpr (le_of_not_ge hAH)
    have hSecondA : ∀ x : ℝ, x ∈ Set.Icc s (s + theta) → A ≤ f x := by
      intro x hx
      have hxPrimary : x ∈ Set.Icc r (r + eta) :=
        ⟨hrs.trans hx.1, hx.2.trans hContained⟩
      exact hFirst x hxPrimary
    have hCost := thirdFull_scalar_containedSecondary_threePieceTailCharge244
      f m T r s eta theta A A hInt hmT hPos hmr hrs heta htheta
      hEnd hContained hFirst hSecondA
    simpa only [max_eq_left hExcess, sub_self, mul_zero, add_zero] using hCost

/-- The sharpened contained-secondary cost and all the already established
three-way packing estimates hold for the SAME selected secondary clock. -/
theorem thirdFullPhysical_retainedPrimary_secondaryClock_containedPeakPacking244
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
    (hSecondary : ThirdFullLateSecondaryPDEClock244 hH3 m sState sSource h) :
    ∃ s eta2 : ℝ,
      (s = sState ∨ s = sSource) ∧ r ≤ s ∧
      0 < eta2 ∧ s + eta2 < T ∧
      (max (eta1 * A)
        (max (min eta1 (s - r) * A + eta2 * (h / 2))
          (eta1 * A +
            (min eta2 (max 0 (s + eta2 - (r + eta1)))) * (h / 2))) ≤
        ∫ x in m..T, velocityH3DissipationAt u x ∂volume) ∧
      (s + eta2 ≤ r + eta1 →
        eta1 * A + eta2 * max 0 (h / 2 - A) ≤
          ∫ x in m..T, velocityH3DissipationAt u x ∂volume) := by
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
  have hUpgrade (hContained : s + eta2 ≤ r + eta1) :
      eta1 * A + eta2 * max 0 (h / 2 - A) ≤
        ∫ x in m..T, velocityH3DissipationAt u x ∂volume :=
    thirdFull_scalar_containedSecondary_positiveExcessCharge244
      (velocityH3DissipationAt u) m T r s eta1 eta2 A (h / 2)
      hDtail hm.2.le (velocityH3DissipationAt_nonneg u)
      hr.1.le hrs heta1.le heta2.le hend1.le hContained
      (fun x hx => (hFloor1 x hx).le)
      (fun x hx => (hFloor2 x hx).2.le)
  exact ⟨s, eta2, hChoice, hrs, heta2, hend2, hPacking, hUpgrade⟩

/-- Retain the entire two-sided packing ledger and a further CONDITIONAL
contained-secondary peak payment on the same first-crossing witnesses.
The strengthened branch provides the original packing and the contained
payment for the SAME chosen secondary source/state time and width. -/
def ThirdFullLateRetainedPrimaryContainedPeakCofinalLedger244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b m r P V : ℝ) (J : ℕ)
    (sSource sState eta1 : ℝ) : Prop :=
  ThirdFullLateRetainedPrimaryTwoSidedPackingLedger244
      hH3 b m r P V J sSource sState eta1 ∧
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
          (let H : ℝ := A / (24 * Real.sqrt (R * B));
            max (eta1 * A)
              (max (min eta1 (s - r) * A + eta2 * H)
                (eta1 * A +
                  (min eta2 (max 0 (s + eta2 - (r + eta1)))) * H)) ≤ B ∧
            (s + eta2 ≤ r + eta1 →
              eta1 * A + eta2 * max 0 (H - A) ≤ B))))

/-- Upgrade the original retained cofinal rate alternatives with a genuine
three-piece contained-peak charge, without changing the old witnesses. -/
theorem thirdFullPhysical_retainedPrimary_ledger_to_containedPeak244
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
    (hLedger : ThirdFullLateRetainedPrimaryTwoSidedPackingLedger244
      hH3 b m r P V J sSource sState eta1) :
    ThirdFullLateRetainedPrimaryContainedPeakCofinalLedger244
      hH3 b m r P V J sSource sState eta1 := by
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ x in m..T, velocityH3DissipationAt u x ∂volume
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let S : ℝ := (((J : ℝ) + 2) ^ 5)
  let R : ℝ := 96 * C0 * S
  change ThirdFullLateRetainedPrimaryTwoSidedPackingLedger244
      hH3 b m r P V J sSource sState eta1 ∧
    ((T - r) * A ≤ 4 * B ∨ A ^ 2 ≤ 4 * B ∨
      (A ^ 2 ≤ R *
          (E0 + 3 * velocityH3DissipationAt u sState) *
          (E0 + 3 * velocityH3DissipationAt u sSource) * B ∧
        (4 * R * B * E0 ^ 2 < A ^ 2 →
          ∃ s eta2 : ℝ,
            (s = sState ∨ s = sSource) ∧ r ≤ s ∧
            0 < eta2 ∧ s + eta2 < T ∧
            (let H : ℝ := A / (24 * Real.sqrt (R * B));
              max (eta1 * A)
                (max (min eta1 (s - r) * A + eta2 * H)
                  (eta1 * A +
                    (min eta2 (max 0 (s + eta2 - (r + eta1)))) * H)) ≤ B ∧
              (s + eta2 ≤ r + eta1 →
                eta1 * A + eta2 * max 0 (H - A) ≤ B)))))
  refine ⟨hLedger, ?_⟩
  change (T - r) * A ≤ 4 * B ∨ A ^ 2 ≤ 4 * B ∨
    (A ^ 2 ≤ R *
        (E0 + 3 * velocityH3DissipationAt u sState) *
        (E0 + 3 * velocityH3DissipationAt u sSource) * B ∧
      (4 * R * B * E0 ^ 2 < A ^ 2 →
        ∃ s eta2 : ℝ,
          (s = sState ∨ s = sSource) ∧ r ≤ s ∧
          0 < eta2 ∧ s + eta2 < T ∧
          (let H : ℝ := A / (24 * Real.sqrt (R * B));
            max (eta1 * A)
              (max (min eta1 (s - r) * A + eta2 * H)
                (eta1 * A +
                  (min eta2 (max 0 (s + eta2 - (r + eta1)))) * H)) ≤ B ∧
            (∀ delta : ℝ, delta ≤ eta1 →
              s < r + delta ∨ delta * A + eta2 * H ≤ B)))) at hLedger
  rcases hLedger with hTime | hTail | ⟨hRate, _hOld⟩
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
  obtain ⟨s, eta2, hWhich, hrs, heta2, hend2, hPacking, hUpgrade⟩ :=
    thirdFullPhysical_retainedPrimary_secondaryClock_containedPeakPacking244
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
  have hUpgradeH (hContained : s + eta2 ≤ r + eta1) :
      eta1 * A + eta2 * max 0 (H - A) ≤ B := by
    simpa only [H, hHeight] using hUpgrade hContained
  exact ⟨s, eta2, hWhich, hrs, heta2, hend2, hPackingH, hUpgradeH⟩

/-- On the same original cofinal prescribed-gauge witnesses, retain THREE
non-double-counting physical clock charges and the budget-to-separation
rule on the constructive late rate branch. The spectral and source
threshold alternatives, first-crossing witnesses, frequency escape and
original disjoint viscous charges are unchanged. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_containedPeakCofinalLedger244
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
          ThirdFullLateRetainedPrimaryContainedPeakCofinalLedger244
            hH3 b m r P V J sSource sState eta1)) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_retainedTwoSidedPackingLedger244
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
    have hContainedLedger :=
      thirdFullPhysical_retainedPrimary_ledger_to_containedPeak244
        hH3 hClass hDInt b hb m hmB r P V J hr hP hV
        sSource sState eta1 hsSource hsState heta1 hend1
        (fun x hx => (hFloor x hx).2) hCharge hLedger
    exact ⟨r, J, sSource, sState, eta1, hr, hP,
      hsSource, hsState, hEtaEq, heta1, hend1,
      hFloor, hCharge, hContainedLedger⟩



end
end PrimeTensor.FirstMonomialTriad
