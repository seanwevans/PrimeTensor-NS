import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousSecondaryAnnularPDECharge
import Mathlib.Tactic

/-!
# Secondary physical annular clocks: terminal compression or PDE-rate amplification

On the actual, previously selected secondary source/state observation times,
the finite-annulus Navier--Stokes persistence window has width
  δ = min ((T-x)/4) (M/(4*(Λ+1)))
and its REAL viscous charge is δ*M/2 ≤ B, B = ∫_m^T D_H3.

The prior cofinal geometry fixes x in [s,s+(T-s)/2]. In particular
T-x ≥ (T-s)/2. Therefore the SAME certified annular clock forces
  (T-s)*M ≤ 16*B  OR  M² ≤ 8*(Λ+1)*B.

The second branch is a necessary lower bound on the *actual finite-annulus
PDE rate*, not a pointwise uniform PDE rate assertion. All original witness
times, the selected cutoff J₂, the first viscous charge, and the previously
proved disjoint-window bounds survive. New annular intervals are NOT added to
previous disjoint-window sums because overlap has not been excluded.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A correctly paid right-hand finite-annulus clock either compresses the
original earlier clock or forces a large actual PDE variation coefficient.
The midpoint geometry is essential: it converts T-x into T-s with factor 2. -/
theorem thirdFull_scalar_secondaryAnnularClockOrRate244
    (T s x M Λ δ B : ℝ)
    (hM : 0 < M) (hΛ : 0 ≤ Λ)
    (hx : x ∈ Set.Icc s (s + (T - s) / 2))
    (hδ : δ = min (((T - x) / 2) / 2)
      ((M / 2) / (2 * (Λ + 1))))
    (hCost : δ * (M / 2) ≤ B) :
    (T - s) * M ≤ 16 * B ∨ M ^ 2 ≤ 8 * (Λ + 1) * B := by
  have hPlus : 0 < Λ + 1 := by linarith only [hΛ]
  have hHalf : (T - s) / 2 ≤ T - x := by
    linarith only [hx.2]
  rcases le_total (((T - x) / 2) / 2)
      ((M / 2) / (2 * (Λ + 1))) with hLeft | hRight
  · have hMin : δ = ((T - x) / 2) / 2 := by
      simpa only [min_eq_left hLeft] using hδ
    rw [hMin] at hCost
    have hFirst : (T - x) * M ≤ 8 * B := by
      calc
        (T - x) * M = 8 * (((T - x) / 2) / 2 * (M / 2)) := by ring
        _ ≤ 8 * B := mul_le_mul_of_nonneg_left hCost (by norm_num)
    have hCompare : (T - s) * M ≤ 2 * ((T - x) * M) := by
      have hTimes := mul_le_mul_of_nonneg_right hHalf hM.le
      nlinarith only [hTimes]
    exact Or.inl (by nlinarith only [hCompare, hFirst])
  · have hMin : δ = (M / 2) / (2 * (Λ + 1)) := by
      simpa only [min_eq_right hRight] using hδ
    rw [hMin] at hCost
    right
    calc
      M ^ 2 = 8 * (Λ + 1) *
          (((M / 2) / (2 * (Λ + 1))) * (M / 2)) := by
            field_simp [ne_of_gt hPlus]
            <;> ring
      _ ≤ 8 * (Λ + 1) * B :=
        mul_le_mul_of_nonneg_left hCost (by positivity)

/-- A real finite-annulus persistence-charge certificate implies a clock
compression or a concrete lower bound on its attained PDE variation rate.
The two attained maxima here are rate coefficients, not new high-dissipation
observation times. No freestanding source ceiling is assumed. -/
theorem thirdFullPhysical_secondaryAnnularCharge_clockOrRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (m s x σ M : ℝ)
    (hx : x ∈ Set.Icc s (s + (T - s) / 2))
    (hM : 0 < M)
    (hCharge : ThirdFullSecondaryHighRadialAnnularPDECharge244
      hH3 m x σ M) :
    ∃ (N : ℕ) (qSource qState : ℝ),
      (T - s) * M ≤
          16 * (∫ r in m..T, velocityH3DissipationAt u r ∂volume) ∨
      M ^ 2 ≤ 8 *
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          σ ((N : ℝ) + 1)
          ‖h3AuditActualSpectralVelocityTotal hH3 qState‖
          ‖h3PathActualProjectedMomentumSource244 hH3 qSource‖ + 1) *
        (∫ r in m..T, velocityH3DissipationAt u r ∂volume) := by
  obtain ⟨N, qSource, qState, δ, _hqSource, _hqState,
      _hMax, _hδ, hδEq, _hEnd, _hFloor, hCost⟩ := hCharge
  let Λ : ℝ := h3PathFiniteAnnulusPDEVariationCoefficient244
    σ ((N : ℝ) + 1)
    ‖h3AuditActualSpectralVelocityTotal hH3 qState‖
    ‖h3PathActualProjectedMomentumSource244 hH3 qSource‖
  have hΛ : 0 ≤ Λ := by
    dsimp only [Λ]
    exact h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
      σ ((N : ℝ) + 1)
      ‖h3AuditActualSpectralVelocityTotal hH3 qState‖
      ‖h3PathActualProjectedMomentumSource244 hH3 qSource‖
      (norm_nonneg _) (norm_nonneg _)
  have hFork := thirdFull_scalar_secondaryAnnularClockOrRate244
    T s x M Λ δ
    (∫ r in m..T, velocityH3DissipationAt u r ∂volume)
    hM hΛ hx (by simpa only [Λ] using hδEq) hCost
  exact ⟨N, qSource, qState, by simpa only [Λ] using hFork⟩

/-- Extend the PRESERVED high-radial cofinal ledger with the real annular PDE
cost and the sharp necessary midpoint-clock/rate alternative. All primary and
secondary witnesses are chosen BEFORE σ and M and are never reselected.
The finite outer N and its source/state maximizing rates may depend on σ,M. -/
def ThirdFullLateRetainedPrimarySecondaryAnnularClockRateCofinalLedger244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b m r P V : ℝ) (J : ℕ)
    (sSource sState eta1 : ℝ) : Prop :=
  ThirdFullLateRetainedPrimarySecondaryHighRadialCofinalLedger244
    hH3 b m r P V J sSource sState eta1 ∧
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let R : ℝ := 96 * C0 * (((J : ℝ) + 2) ^ 5)
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ t in m..T, velocityH3DissipationAt u t ∂volume
  (A ^ 2 ≤ R *
      (E0 + 3 * velocityH3DissipationAt u sState) *
      (E0 + 3 * velocityH3DissipationAt u sSource) * B →
    4 * R * B * E0 ^ 2 < A ^ 2 →
    48 * Real.sqrt (R * B) ≤ 1 →
    ∃ (s eta2 : ℝ) (J2 : ℕ) (zSource zState : ℝ),
      (s = sState ∨ s = sSource) ∧ r ≤ s ∧
      0 < eta2 ∧ s + eta2 < T ∧
      zSource ∈ Set.Icc s (s + (T - s) / 2) ∧
      zState ∈ Set.Icc s (s + (T - s) / 2) ∧
      (∀ (σ M : ℝ), 0 ≤ σ → 0 < M →
        192 * B * Real.sqrt (R * B) < (T - s) * A →
        576 * R * B ^ 2 *
          (96 * C0 *
            (E0 + 3 * (σ ^ 2 *
              (h3TerminalRadialSobolevWeightSquareCeiling σ *
                velocityH3Energy0At u b) + 2 * M)) ^ 2 *
              (((J2 : ℝ) + 2) ^ 5) + 4) < A ^ 2 →
        ∃ x : ℝ, (x = zState ∨ x = zSource) ∧
          ThirdFullSecondaryHighRadialAnnularPDECharge244 hH3 m x σ M ∧
          ∃ (N : ℕ) (qSource qState : ℝ),
            (T - s) * M ≤ 16 * B ∨
            M ^ 2 ≤ 8 *
              (h3PathFiniteAnnulusPDEVariationCoefficient244
                σ ((N : ℝ) + 1)
                ‖h3AuditActualSpectralVelocityTotal hH3 qState‖
                ‖h3PathActualProjectedMomentumSource244 hH3 qSource‖ + 1) * B))

/-- The previously obtained SAME-witness high-radial cofinal obstruction
now has an additional genuine terminal viscous annular charge, plus its PDE
speed fork. In particular the new rate cannot be replaced by an arbitrary
uniform-in-time constant without another mathematical argument. -/
theorem thirdFullPhysical_secondaryHighRadialLedger_to_annularClockRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (m r P V : ℝ) (J : ℕ) (sSource sState eta1 : ℝ)
    (hm : m ∈ Set.Ioo b T) (hr : r ∈ Set.Ioo m T)
    (hOld : ThirdFullLateRetainedPrimarySecondaryHighRadialCofinalLedger244
      hH3 b m r P V J sSource sState eta1) :
    ThirdFullLateRetainedPrimarySecondaryAnnularClockRateCofinalLedger244
      hH3 b m r P V J sSource sState eta1 := by
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let R : ℝ := 96 * C0 * (((J : ℝ) + 2) ^ 5)
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ t in m..T, velocityH3DissipationAt u t ∂volume
  change ThirdFullLateRetainedPrimarySecondaryHighRadialCofinalLedger244
      hH3 b m r P V J sSource sState eta1 ∧
    (A ^ 2 ≤ R *
        (E0 + 3 * velocityH3DissipationAt u sState) *
        (E0 + 3 * velocityH3DissipationAt u sSource) * B →
      4 * R * B * E0 ^ 2 < A ^ 2 →
      48 * Real.sqrt (R * B) ≤ 1 →
      ∃ (s eta2 : ℝ) (J2 : ℕ) (zSource zState : ℝ),
        (s = sState ∨ s = sSource) ∧ r ≤ s ∧
        0 < eta2 ∧ s + eta2 < T ∧
        zSource ∈ Set.Icc s (s + (T - s) / 2) ∧
        zState ∈ Set.Icc s (s + (T - s) / 2) ∧
        (∀ (σ M : ℝ), 0 ≤ σ → 0 < M →
          192 * B * Real.sqrt (R * B) < (T - s) * A →
          576 * R * B ^ 2 *
            (96 * C0 *
              (E0 + 3 * (σ ^ 2 *
                (h3TerminalRadialSobolevWeightSquareCeiling σ *
                  velocityH3Energy0At u b) + 2 * M)) ^ 2 *
                (((J2 : ℝ) + 2) ^ 5) + 4) < A ^ 2 →
          ∃ x : ℝ, (x = zState ∨ x = zSource) ∧
            ThirdFullSecondaryHighRadialAnnularPDECharge244 hH3 m x σ M ∧
            ∃ (N : ℕ) (qSource qState : ℝ),
              (T - s) * M ≤ 16 * B ∨
              M ^ 2 ≤ 8 *
                (h3PathFiniteAnnulusPDEVariationCoefficient244
                  σ ((N : ℝ) + 1)
                  ‖h3AuditActualSpectralVelocityTotal hH3 qState‖
                  ‖h3PathActualProjectedMomentumSource244 hH3 qSource‖ + 1) * B))
  refine ⟨hOld, ?_⟩
  intro hRate hGap hStrong
  obtain ⟨s, eta2, J2, zSource, zState,
      hChoice, hrs, heta2, hend2, hzSource, hzState, hRadial⟩ :=
    hOld.2 hRate hGap hStrong
  have hsT : s < T := by linarith only [heta2, hend2]
  have hHalfEnd : s + (T - s) / 2 < T := by
    linarith only [hsT]
  have hmClass : m ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hm.1, hm.2⟩
  have hzSourceTime : zSource ∈ Set.Ioo m T :=
    ⟨lt_of_lt_of_le hr.1 (le_trans hrs hzSource.1),
      lt_of_le_of_lt hzSource.2 hHalfEnd⟩
  have hzStateTime : zState ∈ Set.Ioo m T :=
    ⟨lt_of_lt_of_le hr.1 (le_trans hrs hzState.1),
      lt_of_le_of_lt hzState.2 hHalfEnd⟩
  refine ⟨s, eta2, J2, zSource, zState,
    hChoice, hrs, heta2, hend2, hzSource, hzState, ?_⟩
  intro σ M hσ hM hWide hDemand
  have hHigh := hRadial σ (2 * M) hσ hWide (by
    simpa only [E0, C0] using hDemand)
  rcases hHigh with hState | hSource
  · have hCharge :=
      thirdFullPhysical_secondaryHighRadialSpike_annularPDECharge244
        hH3 hClass hDInt m zState σ M hmClass hzStateTime hσ hM hState
    have hFork := thirdFullPhysical_secondaryAnnularCharge_clockOrRate244
      hH3 m s zState σ M hzState hM hCharge
    exact ⟨zState, Or.inl rfl, hCharge, hFork⟩
  · have hCharge :=
      thirdFullPhysical_secondaryHighRadialSpike_annularPDECharge244
        hH3 hClass hDInt m zSource σ M hmClass hzSourceTime hσ hM hSource
    have hFork := thirdFullPhysical_secondaryAnnularCharge_clockOrRate244
      hH3 m s zSource σ M hzSource hM hCharge
    exact ⟨zSource, Or.inr rfl, hCharge, hFork⟩

/-- The cofinal no-terminal-H³-trace obstruction, with its original
first-crossing minimal windows, frequency escape, disjoint viscous sum and
vanishing terminal integral, now carries the additional annular PDE
clock-or-rate alternative on its retained physical high-radial branch.
No new annular interval is falsely added to the old disjoint charge sum. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_secondaryAnnularClockRate244
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
          ThirdFullLateRetainedPrimarySecondaryAnnularClockRateCofinalLedger244
            hH3 b m r P V J sSource sState eta1)) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_secondaryHighRadial244
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
    have hPhysical :=
      thirdFullPhysical_secondaryHighRadialLedger_to_annularClockRate244
        hH3 hClass hDInt b hb m r P V J sSource sState eta1
        hmB hr hLedger
    exact ⟨r, J, sSource, sState, eta1, hr, hP,
      hsSource, hsState, hEtaEq, heta1, hend1,
      hFloor, hCharge, hPhysical⟩

end
end PrimeTensor.FirstMonomialTriad
