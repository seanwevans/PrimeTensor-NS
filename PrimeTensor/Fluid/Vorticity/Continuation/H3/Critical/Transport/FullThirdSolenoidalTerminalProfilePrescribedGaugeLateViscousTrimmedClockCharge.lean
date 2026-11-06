import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousCofinalDualClock
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# The unshared prefix of a primary PDE clock survives secondary overlap

The secondary physical PDE spike occurs at one of the *original* compact
source/state maximizers. Thus its starting time s satisfies r <= s, where
r starts the primary clock. Even if the intervals overlap, the primary
prefix [r, min (r+eta1) s] and the WHOLE secondary clock [s,s+eta2]
are disjoint. The actual terminal H3 action therefore pays

  min eta1 (s-r) * A + eta2 * (h/2) <= B.

This is unconditional whenever both clocks are certified: no hypothesis of
separation, no duplicated overlap integral, and no extra terminal-uniform
coefficient. Applying the constructive h=A/(12 sqrt(R B)) gives the
second term eta2*A/(24 sqrt(R B)). The original prescribed-gauge cofinal
witnesses, first-crossing windows, and their disjoint sums are retained.

The possible degeneration s=r remains real; this does not prove global
Navier--Stokes continuation or a positive lower bound on either clock.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- In an ordered pair of possibly overlapping windows, shorten only the
first window to the second window's start. The retained first prefix and
all of the second window have disjoint interiors and hence additive cost. -/
theorem thirdFull_scalar_orderedTwoClocks_trimmedPrefixCharge244
    (f : ℝ → ℝ) (m T r s eta theta A H : ℝ)
    (hInt : IntervalIntegrable f volume m T)
    (hmT : m ≤ T) (hPos : ∀ x : ℝ, 0 ≤ f x)
    (hmr : m ≤ r) (hrs : r ≤ s)
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hEnd : s + theta ≤ T)
    (hFirst : ∀ x : ℝ, x ∈ Set.Icc r (r + eta) → A ≤ f x)
    (hSecond : ∀ x : ℝ, x ∈ Set.Icc s (s + theta) → H ≤ f x) :
    min eta (s - r) * A + theta * H ≤
      ∫ x in m..T, f x ∂volume := by
  let ell : ℝ := min eta (s - r)
  have hEll : 0 ≤ ell := by
    dsimp only [ell]
    exact le_min heta (sub_nonneg.mpr hrs)
  have hEllEta : ell ≤ eta := min_le_left _ _
  have hEllTravel : ell ≤ s - r := min_le_right _ _
  have hEllSep : r + ell ≤ s := by linarith only [hEllTravel]
  have hEllBound : r + ell ≤ r + eta := by
    linarith only [hEllEta]
  have hms : m ≤ s := hmr.trans hrs
  have hThetaEnd : s ≤ s + theta := le_add_of_nonneg_right htheta
  have hFirstInt : IntervalIntegrable f volume r (r + ell) := by
    apply hInt.mono_set
    intro x hx
    have hxIcc : x ∈ Set.Icc r (r + ell) := by
      simpa only [Set.uIcc_of_le (le_add_of_nonneg_right hEll)] using hx
    have hxMain : x ∈ Set.Icc m T :=
      ⟨hmr.trans hxIcc.1, hxIcc.2.trans (hEllSep.trans (hThetaEnd.trans hEnd))⟩
    simpa only [Set.uIcc_of_le hmT] using hxMain
  have hSecondInt : IntervalIntegrable f volume s (s + theta) := by
    apply hInt.mono_set
    intro x hx
    have hxIcc : x ∈ Set.Icc s (s + theta) := by
      simpa only [Set.uIcc_of_le hThetaEnd] using hx
    have hxMain : x ∈ Set.Icc m T :=
      ⟨hms.trans hxIcc.1, hxIcc.2.trans hEnd⟩
    simpa only [Set.uIcc_of_le hmT] using hxMain
  have hFirstCost : ell * A ≤
      ∫ x in r..(r + ell), f x ∂volume := by
    have hCmp :
        (∫ _x in r..(r + ell), A ∂volume) ≤
          ∫ x in r..(r + ell), f x ∂volume := by
      apply intervalIntegral.integral_mono_on
        (le_add_of_nonneg_right hEll) intervalIntegrable_const hFirstInt
      intro x hx
      exact hFirst x ⟨hx.1, hx.2.trans hEllBound⟩
    calc
      ell * A = ∫ _x in r..(r + ell), A ∂volume := by
        simp [mul_comm] <;> ring
      _ ≤ ∫ x in r..(r + ell), f x ∂volume := hCmp
  have hSecondCost : theta * H ≤
      ∫ x in s..(s + theta), f x ∂volume := by
    have hCmp :
        (∫ _x in s..(s + theta), H ∂volume) ≤
          ∫ x in s..(s + theta), f x ∂volume := by
      apply intervalIntegral.integral_mono_on hThetaEnd
        intervalIntegrable_const hSecondInt
      intro x hx
      exact hSecond x hx
    calc
      theta * H = ∫ _x in s..(s + theta), H ∂volume := by
        simp [mul_comm] <;> ring
      _ ≤ ∫ x in s..(s + theta), f x ∂volume := hCmp
  have hCharge := thirdFull_scalar_orderedTwoWindows_additiveTailCharge244
    f m T r s ell theta A H hInt hmT hPos hmr hEll
    hEllSep htheta hEnd hFirstCost hSecondCost
  simpa only [ell] using hCharge

/-- The actual secondary clock starts at one of the two primary maximizers,
both of which are at or after r. Its whole interval and the unshared
prefix of the PRIMARY clock therefore have an additive terminal cost even
when the two full clocks overlap. -/
theorem thirdFullPhysical_retainedPrimary_secondaryClock_trimmedCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (m r eta1 A sState sSource h : ℝ)
    (hm : m ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo m T)
    (heta1 : 0 < eta1)
    (hFloor1 : ∀ x : ℝ, x ∈ Set.Icc r (r + eta1) →
      A < velocityH3DissipationAt u x)
    (hsState : sState ∈ Set.Icc r (r + (T - r) / 2))
    (hsSource : sSource ∈ Set.Icc r (r + (T - r) / 2))
    (hSecondary : ThirdFullLateSecondaryPDEClock244
      hH3 m sState sSource h) :
    ∃ s eta2 : ℝ,
      (s = sState ∨ s = sSource) ∧ r ≤ s ∧
      0 < eta2 ∧ s + eta2 < T ∧
      min eta1 (s - r) * A + eta2 * (h / 2) ≤
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
  have hTrim := thirdFull_scalar_orderedTwoClocks_trimmedPrefixCharge244
    (velocityH3DissipationAt u) m T r s eta1 eta2 A (h / 2)
    hDtail hm.2.le (velocityH3DissipationAt_nonneg u)
    hr.1.le hrs heta1.le heta2.le hend2.le
    (fun x hx => (hFloor1 x hx).le)
    (fun x hx => (hFloor2 x hx).2.le)
  exact ⟨s, eta2, hChoice, hrs, heta2, hend2, hTrim⟩

/-- The three late physical alternatives with the *overlap-safe*
quantitative cost on the genuinely active two-slice rate branch. -/
def ThirdFullLateRetainedPrimaryTrimmedCofinalLedger244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b m r P V : ℝ) (J : ℕ)
    (sSource sState eta1 : ℝ) : Prop :=
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let R : ℝ := 96 * C0 * (((J : ℝ) + 2) ^ 5)
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ s in m..T, velocityH3DissipationAt u s ∂volume
  (T - r) * A ≤ 4 * B ∨ A ^ 2 ≤ 4 * B ∨
    (A ^ 2 ≤ R *
        (E0 + 3 * velocityH3DissipationAt u sState) *
        (E0 + 3 * velocityH3DissipationAt u sSource) * B ∧
      (4 * R * B * E0 ^ 2 < A ^ 2 →
        ∃ s eta2 : ℝ,
          (s = sState ∨ s = sSource) ∧ r ≤ s ∧
          0 < eta2 ∧ s + eta2 < T ∧
          min eta1 (s - r) * A +
            eta2 * (A / (24 * Real.sqrt (R * B))) ≤ B))

/-- Strengthen the OLD retained dual ledger in place: on its physical
rate branch, retain the SAME primary floor to pay an unshared prefix
and the full secondary clock. No extra mathematical hypothesis is added. -/
theorem thirdFullPhysical_retainedPrimary_ledger_to_trimmedCharge244
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
    (heta1 : 0 < eta1)
    (hFloor : ∀ x : ℝ, x ∈ Set.Icc r (r + eta1) →
      V / (2 * P) < velocityH3DissipationAt u x)
    (hLedger : ThirdFullLateRetainedPrimaryCofinalDualClockLedger244
      hH3 b m r P V J sSource sState eta1) :
    ThirdFullLateRetainedPrimaryTrimmedCofinalLedger244
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
          min eta1 (s - r) * A +
            eta2 * (A / (24 * Real.sqrt (R * B))) ≤ B))
  change (T - r) * A ≤ 4 * B ∨ A ^ 2 ≤ 4 * B ∨
    (A ^ 2 ≤ R *
        (E0 + 3 * velocityH3DissipationAt u sState) *
        (E0 + 3 * velocityH3DissipationAt u sSource) * B ∧
      (4 * R * B * E0 ^ 2 < A ^ 2 →
        ∃ s eta2 : ℝ,
          (s = sState ∨ s = sSource) ∧
          0 < eta2 ∧ s + eta2 < T ∧
          (eta1 * A + eta2 * (A / (24 * Real.sqrt (R * B))) ≤ B ∨
            (r < s + eta2 ∧ s < r + eta1)))) at hLedger
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
  have hmA : m ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hm.1, hm.2⟩
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
  obtain ⟨s, eta2, hWhich, hrs, heta2, hend2, hTrim⟩ :=
    thirdFullPhysical_retainedPrimary_secondaryClock_trimmedCharge244
      hH3 hClass hDInt m r eta1 A sState sSource
      (A / (12 * Real.sqrt (R * B)))
      hmA hr heta1 (by simpa only [A] using hFloor)
      hsState hsSource hSecondary
  have hq : 0 < Real.sqrt (R * B) :=
    Real.sqrt_pos.2 (mul_pos hR hB)
  have hHeight :
      (A / (12 * Real.sqrt (R * B))) / 2 =
        A / (24 * Real.sqrt (R * B)) := by
    field_simp [ne_of_gt hq]
    <;> ring
  refine ⟨s, eta2, hWhich, hrs, heta2, hend2, ?_⟩
  simpa only [hHeight] using hTrim

/-- The original cofinal prescribed-gauge witnesses now ALWAYS retain the
unshared-primary-prefix plus the WHOLE secondary PDE clock charge on the
constructive non-kinetic late rate branch, even if both full intervals
intersect. All preceding Fourier/kinetic alternatives and original disjoint
viscous charges remain unchanged. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_retainedTrimmedCofinalLedger244
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
          ThirdFullLateRetainedPrimaryTrimmedCofinalLedger244
            hH3 b m r P V J sSource sState eta1)) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_retainedCofinalDualClockLedger244
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
    have hTrim :=
      thirdFullPhysical_retainedPrimary_ledger_to_trimmedCharge244
        hH3 hClass hDInt b hb m hmB r P V J hr hP hV
        sSource sState eta1 hsSource hsState heta1
        (fun x hx => (hFloor x hx).2) hLedger
    exact ⟨r, J, sSource, sState, eta1, hr, hP,
      hsSource, hsState, hEtaEq, heta1, hend1,
      hFloor, hCharge, hTrim⟩

end
end PrimeTensor.FirstMonomialTriad
