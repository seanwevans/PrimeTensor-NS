import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousOverlapLedger
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Retain BOTH late physical PDE clocks on the prescribed-gauge cofinal witnesses

The original explicit finite-band PDE-clock theorem already supplies the first
real interval and its pointwise full-H³ viscous floor. Previous rate and
squared-tail consequences discarded that interval in their statements.
This module keeps it and applies the constructive two-slice argument to the
SAME first-crossing time and the SAME originally attained source/state times.

On the late branch: terminal-time compression, a pure terminal-tail charge,
or the two-slice physical source-state rate bound. In the last case, whenever
the explicit kinetic-only gap holds, the secondary clock is obtained and its
*joint* relationship with the retained primary clock is certified:

  η₁ A + η₂ A/(24 sqrt(R B)) ≤ B
     OR the two strict physical clock intervals overlap.

No independent or summed charge is asserted on overlapping intervals, and
no bound on either physical cutoff or time-dependent PDE maximum is imposed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A concise record for the three physical late alternatives, retaining
both original attained maxima and the exact *primary* persistence width.
The secondary interval is required only under the non-kinetic gap. -/
def ThirdFullLateRetainedPrimaryCofinalDualClockLedger244
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
          (s = sState ∨ s = sSource) ∧
          0 < eta2 ∧ s + eta2 < T ∧
          (eta1 * A + eta2 * (A / (24 * Real.sqrt (R * B))) ≤ B ∨
            (r < s + eta2 ∧ s < r + eta1))))

/-- No separate primary-spike hypothesis is needed once the actual first
PDE clock's pointwise floor has been retained. Its local interval integral
and the secondary actual interval integral are added only when disjoint. -/
theorem thirdFullPhysical_retainedPrimary_secondaryPDEClock_overlapLedger244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (m r eta1 A sState sSource h : ℝ)
    (hm : m ∈ Set.Ioo a T) (hr : r ∈ Set.Ioo m T)
    (heta1 : 0 < eta1) (hend1 : r + eta1 < T)
    (hFloor1 : ∀ x : ℝ, x ∈ Set.Icc r (r + eta1) →
      A < velocityH3DissipationAt u x)
    (hsState : sState ∈ Set.Ioo m T)
    (hsSource : sSource ∈ Set.Ioo m T)
    (hSecondary : ThirdFullLateSecondaryPDEClock244
      hH3 m sState sSource h) :
    ∃ s eta2 : ℝ,
      (s = sState ∨ s = sSource) ∧
      0 < eta2 ∧ s + eta2 < T ∧
      (eta1 * A + eta2 * (h / 2) ≤
        ∫ x in m..T, velocityH3DissipationAt u x ∂volume ∨
        (r < s + eta2 ∧ s < r + eta1)) := by
  let D : ℝ → ℝ := velocityH3DissipationAt u
  rcases hSecondary with ⟨s, hChoice, _J2, _zSource, _zState, eta2,
      _hzSource, _hzState, _hEtaEq, heta2, hend2, hFloor2, _hTail2⟩
  have hs : s ∈ Set.Ioo m T := by
    rcases hChoice with rfl | rfl
    · exact hsState
    · exact hsSource
  have hDtail : IntervalIntegrable D volume m T := by
    apply hDInt.mono_set
    intro x hx
    have hx' : x ∈ Set.Icc m T := by
      simpa only [Set.uIcc_of_le hm.2.le] using hx
    have hx'' : x ∈ Set.Icc a T :=
      ⟨hm.1.le.trans hx'.1, hx'.2⟩
    simpa only [Set.uIcc_of_le hClass.terminal_start.2.le] using hx''
  have hDwin (x eta : ℝ) (hmx : m ≤ x)
      (heta : 0 ≤ eta) (hend : x + eta ≤ T) :
      IntervalIntegrable D volume x (x + eta) := by
    apply hDtail.mono_set
    intro z hz
    have hz' : z ∈ Set.Icc x (x + eta) := by
      simpa only [Set.uIcc_of_le (le_add_of_nonneg_right heta)] using hz
    have hz'' : z ∈ Set.Icc m T :=
      ⟨hmx.trans hz'.1, hz'.2.trans hend⟩
    simpa only [Set.uIcc_of_le hm.2.le] using hz''
  have hCharge1 : eta1 * A ≤
      ∫ x in r..(r + eta1), D x ∂volume := by
    have hInt1 := hDwin r eta1 hr.1.le heta1.le hend1.le
    have hCmp :
        (∫ _x in r..(r + eta1), A ∂volume) ≤
          ∫ x in r..(r + eta1), D x ∂volume := by
      apply intervalIntegral.integral_mono_on
        (le_add_of_nonneg_right heta1.le)
        intervalIntegrable_const hInt1
      intro x hx
      exact (hFloor1 x hx).le
    calc
      eta1 * A = ∫ _x in r..(r + eta1), A ∂volume := by
        simp [mul_comm] <;> ring
      _ ≤ ∫ x in r..(r + eta1), D x ∂volume := hCmp
  have hCharge2 : eta2 * (h / 2) ≤
      ∫ x in s..(s + eta2), D x ∂volume := by
    have hInt2 := hDwin s eta2 hs.1.le heta2.le hend2.le
    have hCmp :
        (∫ _x in s..(s + eta2), h / 2 ∂volume) ≤
          ∫ x in s..(s + eta2), D x ∂volume := by
      apply intervalIntegral.integral_mono_on
        (le_add_of_nonneg_right heta2.le)
        intervalIntegrable_const hInt2
      intro x hx
      exact (hFloor2 x hx).2.le
    calc
      eta2 * (h / 2) = ∫ _x in s..(s + eta2), h / 2 ∂volume := by
        simp [mul_comm] <;> ring
      _ ≤ ∫ x in s..(s + eta2), D x ∂volume := hCmp
  have hBoth := thirdFull_scalar_twoWindows_overlapOrAdditiveTailCharge244
    D m T r s eta1 eta2 A (h / 2)
    hDtail hm.2.le (velocityH3DissipationAt_nonneg u)
    hr.1.le hs.1.le heta1.le heta2.le hend1.le hend2.le
    hCharge1 hCharge2
  exact ⟨s, eta2, hChoice, heta2, hend2, hBoth⟩

/-- The exact primary PDE clock either already compresses the terminal
clock, is paid by the bare tail, or pays by physical two-time viscous slices.
When the kinetic-only payment in the last alternative is too small, the
constructive secondary clock is synchronized with the RETAINED primary
interval (not reselected), giving a genuine overlap-or-additive ledger. -/
theorem thirdFullPhysical_primaryPDEClock_retains_constructiveDualLedger244
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
    (hEtaEq : eta1 = min ((T - r) / 4)
      ((V / (2 * P)) /
        (2 * (thirdFullLateViscousLowRadialPDERate244 J
          ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
          ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ + 1))))
    (heta1 : 0 < eta1) (hend1 : r + eta1 < T)
    (hFloor : ∀ x : ℝ, x ∈ Set.Icc r (r + eta1) →
      V / (2 * P) < velocityH3DissipationAt u x)
    (hCharge : eta1 * (V / (2 * P)) ≤
      ∫ x in m..T, velocityH3DissipationAt u x ∂volume) :
    ThirdFullLateRetainedPrimaryCofinalDualClockLedger244
      hH3 b m r P V J sSource sState eta1 := by
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ x in m..T, velocityH3DissipationAt u x ∂volume
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let S : ℝ := (((J : ℝ) + 2) ^ 5)
  let R : ℝ := 96 * C0 * S
  let KP : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
  let CP : ℝ := ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖
  let Lambda : ℝ := thirdFullLateViscousLowRadialPDERate244 J KP CP
  have hmA : m ∈ Set.Ioo a T := ⟨lt_trans hb.1 hm.1, hm.2⟩
  have hA : 0 < A := by dsimp only [A]; positivity
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact intervalIntegral.integral_nonneg hm.2.le
      (fun x _ => velocityH3DissipationAt_nonneg u x)
  have hLambda : 0 ≤ Lambda := by
    dsimp only [Lambda, thirdFullLateViscousLowRadialPDERate244]
    positivity
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
  have hHalf : ((T - r) / 2) / 2 = (T - r) / 4 := by ring
  have hExact : eta1 = min (((T - r) / 2) / 2)
      (A / (2 * (Lambda + 1))) := by
    rw [hHalf]
    simpa only [A, Lambda, KP, CP] using hEtaEq
  have hMin := thirdFull_scalar_minPDEClock_timeOrRate244
    A Lambda ((T - r) / 2) B eta1 hLambda hExact
    (by simpa only [A, B] using hCharge)
  have hPoly : Lambda ≤ 24 * KP * CP * S := by
    dsimp only [Lambda, S, KP, CP]
    exact thirdFull_lateLowRadialPDERate_le_quinticPhysicalProduct244
      J _ _ (norm_nonneg _) (norm_nonneg _)
  have hHalfEnd : r + (T - r) / 2 < T := by
    linarith only [hr.2]
  have hsStateTail : sState ∈ Set.Ioo m T :=
    ⟨lt_of_lt_of_le hr.1 hsState.1,
      lt_of_le_of_lt hsState.2 hHalfEnd⟩
  have hsSourceTail : sSource ∈ Set.Ioo m T :=
    ⟨lt_of_lt_of_le hr.1 hsSource.1,
      lt_of_le_of_lt hsSource.2 hHalfEnd⟩
  have hsStateB : sState ∈ Set.Ioo b T :=
    ⟨lt_trans hm.1 hsStateTail.1, hsStateTail.2⟩
  have hsSourceB : sSource ∈ Set.Ioo b T :=
    ⟨lt_trans hm.1 hsSourceTail.1, hsSourceTail.2⟩
  change (T - r) * A ≤ 4 * B ∨ A ^ 2 ≤ 4 * B ∨
    (A ^ 2 ≤ R * (E0 + 3 * velocityH3DissipationAt u sState) *
        (E0 + 3 * velocityH3DissipationAt u sSource) * B ∧
      (4 * R * B * E0 ^ 2 < A ^ 2 →
        ∃ s eta2 : ℝ,
          (s = sState ∨ s = sSource) ∧
          0 < eta2 ∧ s + eta2 < T ∧
          (eta1 * A + eta2 * (A / (24 * Real.sqrt (R * B))) ≤ B ∨
            (r < s + eta2 ∧ s < r + eta1))))
  rcases hMin with hTime | hFast
  · left
    calc
      (T - r) * A = 2 * (((T - r) / 2) * A) := by ring
      _ ≤ 2 * (2 * B) :=
        mul_le_mul_of_nonneg_left hTime (by norm_num)
      _ = 4 * B := by ring
  rcases thirdFull_scalar_lateRate_quinticProductOrTail244
      A B Lambda KP CP S hB0 hFast hPoly with hSmall | hProduct
  · exact Or.inr (Or.inl hSmall)
  right; right
  have hPhysical :=
    thirdFullPhysical_lateQuinticProduct_twoActualViscousSlices244
      hH3 hClass b hb sSource sState A B S hsSourceB hsStateB
      hB0 hS.le (by simpa only [KP, CP, S] using hProduct)
  have hRate : A ^ 2 ≤
      R * (E0 + 3 * velocityH3DissipationAt u sState) *
        (E0 + 3 * velocityH3DissipationAt u sSource) * B := by
    calc
      A ^ 2 ≤ 96 *
        (E0 + 3 * velocityH3DissipationAt u sState) *
        (C0 * (E0 + 3 * velocityH3DissipationAt u sSource)) * S * B := by
          simpa only [E0, C0] using hPhysical
      _ = R * (E0 + 3 * velocityH3DissipationAt u sState) *
          (E0 + 3 * velocityH3DissipationAt u sSource) * B := by
            dsimp only [R]
            ring
  refine ⟨hRate, ?_⟩
  intro hGap
  have hB : 0 < B := by
    by_contra hNot
    have hBzero : B = 0 :=
      le_antisymm (le_of_not_gt hNot) hB0
    have hRateZero : A ^ 2 ≤ 0 := by
      simpa only [hBzero, mul_zero] using hRate
    have hPosSq : 0 < A ^ 2 := by positivity
    exact (not_le_of_gt hPosSq) hRateZero
  obtain ⟨_hh, _hSpike, hSecondary⟩ :=
    thirdFullPhysical_twoSlice_constructiveSqrtTailPDEClock244
      hH3 hClass hDInt m sState sSource A B R E0
      hmA hsStateTail hsSourceTail hA hB hR hE0 hRate hGap
  obtain ⟨s, eta2, hWhich, heta2, hend2, hGate⟩ :=
    thirdFullPhysical_retainedPrimary_secondaryPDEClock_overlapLedger244
      hH3 hClass hDInt m r eta1 A sState sSource
      (A / (12 * Real.sqrt (R * B)))
      hmA hr heta1 hend1 (by simpa only [A] using hFloor)
      hsStateTail hsSourceTail hSecondary
  have hq : 0 < Real.sqrt (R * B) :=
    Real.sqrt_pos.2 (mul_pos hR hB)
  have hHeight : (A / (12 * Real.sqrt (R * B))) / 2 =
      A / (24 * Real.sqrt (R * B)) := by
    field_simp [ne_of_gt hq]
    <;> ring
  refine ⟨s, eta2, hWhich, heta2, hend2, ?_⟩
  simpa only [hHeight] using hGate

/-- The SAME cofinal no-terminal-H³-trace witnesses now retain the primary
low-radial PDE clock all the way through the second physical rate argument.
The late branch contains the overlap-aware dual-clock barrier rather than
silently forgetting the original positive-duration interval. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_retainedCofinalDualClockLedger244
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
          ThirdFullLateRetainedPrimaryCofinalDualClockLedger244
            hH3 b m r P V J sSource sState eta1)) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_lateExplicitPDEClock244
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
        hsSource, hsState, hEtaEq, heta1, hend1, hFloor, hCharge⟩
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
    have hLedger :=
      thirdFullPhysical_primaryPDEClock_retains_constructiveDualLedger244
        hH3 hClass hDInt b hb m hmB r P V J hr hP hV
        sSource sState eta1 hsSource hsState hEtaEq heta1 hend1
        (fun x hx => (hFloor x hx).2) hCharge
    exact ⟨r, J, sSource, sState, eta1, hr, hP,
      hsSource, hsState, hEtaEq, heta1, hend1,
      hFloor, hCharge, hLedger⟩

end
end PrimeTensor.FirstMonomialTriad
