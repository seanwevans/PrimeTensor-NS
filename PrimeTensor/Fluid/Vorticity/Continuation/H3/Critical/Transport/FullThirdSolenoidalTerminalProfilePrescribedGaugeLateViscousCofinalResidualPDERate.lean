import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousResidualPDERate
import Mathlib.Tactic

/-!
# Cofinal physical PDE-rate obstruction after exact H³ clock overlap

The cofinal prescribed-gauge no-H³-trace witnesses already retain the first
physical PDE persistence clock and an exact two-floor overlap envelope.
The residual PDE-rate theorem previously retained the selected secondary
finite cutoff J2 and attained source/state maxima ONLY locally.

For each cofinal late first-clock witness, on the actual two-slice physical
rate condition, the constructive kinetic gap and the genuine excess regime
24 sqrt(R B) < 1 now produce a selected secondary clock with its real cutoff,
attained physical maxima, exact interval envelope and residual rate gate.

Write A=V/(2P), B=integral_m^T D_H3, R=96 C0 (J+2)^5,
H=(A/(12 sqrt(R B)))/2 and L=the secondary extension outside the primary.
Residual action E=B-eta1*A-L*A is strictly positive, and E<=B.
The actual secondary source/state/frequency product must satisfy

    (T-s)*(H-A) <= 4*E
or
    (H*(H-A)-2*E)/(48*E) <= K2*C2*(J2+2)^5.

These are NECESSARY blow-up conditions only in the genuinely activated
rate branch; no terminal-uniform cutoff, rate, or source bound is introduced.
The original cofinal witnesses, frequency escape and dissipation sums remain.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Actual constructive secondary floor, equal to half the physical
square-root-tail spike threshold. -/
noncomputable def thirdFullLateConstructiveResidualFloor244
    (A R B : ℝ) : ℝ :=
  (A / (12 * Real.sqrt (R * B))) / 2

/-- An activated residual-rate arm imposes an explicit, positive-residual
lower bound on the selected physical PDE source-state-frequency product. -/
theorem thirdFull_scalar_residualQuinticProduct_lowerBound244
    (H A E K C S : ℝ) (hE : 0 < E)
    (hRate : H * (H - A) ≤ (48 * K * C * S + 2) * E) :
    (H * (H - A) - 2 * E) / (48 * E) ≤ K * C * S := by
  have hDen : 0 < 48 * E := by positivity
  apply (div_le_iff₀ hDen).2
  nlinarith only [hRate]

/-- Retain the previous exact-overlap cofinal ledger and attach an actual
secondary cutoff, source/state maxima, and a residual-rate lower barrier
whenever the previously exposed two-slice rate, kinetic gap, and excess
activation inequalities hold. -/
def ThirdFullLateRetainedPrimaryResidualPDECofinalLedger244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b m r P V : ℝ) (J : ℕ)
    (sSource sState eta1 : ℝ) : Prop :=
  ThirdFullLateRetainedPrimaryExactOverlapCofinalLedger244
    hH3 b m r P V J sSource sState eta1 ∧
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let R : ℝ := 96 * C0 * (((J : ℝ) + 2) ^ 5)
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ x in m..T, velocityH3DissipationAt u x ∂volume
  (A ^ 2 ≤ R *
      (E0 + 3 * velocityH3DissipationAt u sState) *
      (E0 + 3 * velocityH3DissipationAt u sSource) * B →
    4 * R * B * E0 ^ 2 < A ^ 2 →
    24 * Real.sqrt (R * B) < 1 →
    ∃ (s eta2 : ℝ) (J2 : ℕ) (zSource zState : ℝ),
      (s = sState ∨ s = sSource) ∧ r ≤ s ∧
      0 < eta2 ∧ s + eta2 < T ∧
      zSource ∈ Set.Icc s (s + (T - s) / 2) ∧
      zState ∈ Set.Icc s (s + (T - s) / 2) ∧
      ThirdFullLateExactTwoClockOverlapEnvelope244 A B r s eta1 eta2
        (thirdFullLateConstructiveResidualFloor244 A R B) ∧
      0 < thirdFullLateResidualTwoClockAction244 A B r s eta1 eta2 ∧
      thirdFullLateResidualTwoClockAction244 A B r s eta1 eta2 ≤ B ∧
      ((T - s) * (thirdFullLateConstructiveResidualFloor244 A R B - A) ≤
          4 * thirdFullLateResidualTwoClockAction244 A B r s eta1 eta2 ∨
        (thirdFullLateConstructiveResidualFloor244 A R B *
              (thirdFullLateConstructiveResidualFloor244 A R B - A) -
            2 * thirdFullLateResidualTwoClockAction244 A B r s eta1 eta2) /
            (48 * thirdFullLateResidualTwoClockAction244 A B r s eta1 eta2) ≤
          ‖h3AuditActualSpectralVelocityTotal hH3 zState‖ *
            ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ *
              (((J2 : ℝ) + 2) ^ 5)))

/-- Promote the actual physical dual-clock residual-rate theorem to the
ORIGINAL prescribed-gauge late first-clock data, not a new subsequence. -/
theorem thirdFullPhysical_exactOverlapLedger_to_cofinalResidualPDE244
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
    (hOld : ThirdFullLateRetainedPrimaryExactOverlapCofinalLedger244
      hH3 b m r P V J sSource sState eta1) :
    ThirdFullLateRetainedPrimaryResidualPDECofinalLedger244
      hH3 b m r P V J sSource sState eta1 := by
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ x in m..T, velocityH3DissipationAt u x ∂volume
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let R : ℝ := 96 * C0 * (((J : ℝ) + 2) ^ 5)
  change ThirdFullLateRetainedPrimaryExactOverlapCofinalLedger244
      hH3 b m r P V J sSource sState eta1 ∧
    (A ^ 2 ≤ R *
        (E0 + 3 * velocityH3DissipationAt u sState) *
        (E0 + 3 * velocityH3DissipationAt u sSource) * B →
      4 * R * B * E0 ^ 2 < A ^ 2 →
      24 * Real.sqrt (R * B) < 1 →
      ∃ (s eta2 : ℝ) (J2 : ℕ) (zSource zState : ℝ),
        (s = sState ∨ s = sSource) ∧ r ≤ s ∧
        0 < eta2 ∧ s + eta2 < T ∧
        zSource ∈ Set.Icc s (s + (T - s) / 2) ∧
        zState ∈ Set.Icc s (s + (T - s) / 2) ∧
        ThirdFullLateExactTwoClockOverlapEnvelope244 A B r s eta1 eta2
          (thirdFullLateConstructiveResidualFloor244 A R B) ∧
        0 < thirdFullLateResidualTwoClockAction244 A B r s eta1 eta2 ∧
        thirdFullLateResidualTwoClockAction244 A B r s eta1 eta2 ≤ B ∧
        ((T - s) * (thirdFullLateConstructiveResidualFloor244 A R B - A) ≤
            4 * thirdFullLateResidualTwoClockAction244 A B r s eta1 eta2 ∨
          (thirdFullLateConstructiveResidualFloor244 A R B *
                (thirdFullLateConstructiveResidualFloor244 A R B - A) -
              2 * thirdFullLateResidualTwoClockAction244 A B r s eta1 eta2) /
              (48 * thirdFullLateResidualTwoClockAction244 A B r s eta1 eta2) ≤
            ‖h3AuditActualSpectralVelocityTotal hH3 zState‖ *
              ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ *
                (((J2 : ℝ) + 2) ^ 5)))
  refine ⟨hOld, ?_⟩
  intro hRate hGap hSmall
  have hA : 0 < A := by dsimp only [A]; positivity
  have hC0 : 0 < C0 := by
    dsimp only [C0]
    have hCoeff := h3AuditInitialLerayEnergyCoefficient_nonneg
    linarith only [hCoeff]
  have hE0 : 0 ≤ E0 := by
    dsimp only [E0]
    have hEnergy := velocityH3Energy0At_nonneg u b
    linarith only [hEnergy]
  have hR : 0 < R := by
    dsimp only [R]
    positivity
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
  have hExcess : A < (A / (12 * Real.sqrt (R * B))) / 2 :=
    thirdFull_scalar_constructiveSqrtTail_activatesResidualExcess244
      A R B hA (mul_pos hR hB) hSmall
  obtain ⟨s, eta2, J2, zSource, zState, hChoice, hrs, heta2,
      hend2, hzSource, hzState, hEnvelope, _hResidualNonneg, hPhysicalRate⟩ :=
    thirdFullPhysical_dualSelectedClock_residualPDERate244
      hH3 hClass hDInt m r eta1 A sState sSource
      (A / (12 * Real.sqrt (R * B)))
      hmA hr heta1 hend1 (by simpa only [A] using hFloor)
      (by simpa only [A, B] using hCharge)
      hsState hsSource hSecondary hExcess.le
  let H : ℝ := thirdFullLateConstructiveResidualFloor244 A R B
  let E : ℝ := thirdFullLateResidualTwoClockAction244 A B r s eta1 eta2
  have hExcess' : A < H := hExcess
  have hExact : ThirdFullLateExactTwoClockOverlapEnvelope244
      A B r s eta1 eta2 H := hEnvelope
  have hCost : eta2 * (H - A) ≤ E :=
    thirdFull_scalar_exactOverlap_residualExcessCharge244
      A B r s eta1 eta2 H hExcess'.le hExact
  have hE : 0 < E :=
    lt_of_lt_of_le (mul_pos heta2 (sub_pos.mpr hExcess')) hCost
  have hOutside : 0 ≤
      thirdFullLateSecondaryOutsidePrimaryDuration244 r s eta1 eta2 := by
    unfold thirdFullLateSecondaryOutsidePrimaryDuration244
    exact le_min heta2.le (le_max_left _ _)
  have hEUpper : E ≤ B := by
    have hFirstNonneg := mul_nonneg heta1.le hA.le
    have hOutsideNonneg := mul_nonneg hOutside hA.le
    dsimp only [E, thirdFullLateResidualTwoClockAction244]
    linarith only [hFirstNonneg, hOutsideNonneg]
  have hGate :
      (T - s) * (H - A) ≤ 4 * E ∨
        (H * (H - A) - 2 * E) / (48 * E) ≤
          ‖h3AuditActualSpectralVelocityTotal hH3 zState‖ *
            ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ *
              (((J2 : ℝ) + 2) ^ 5) := by
    rcases hPhysicalRate with hTime | hRateClock
    · exact Or.inl hTime
    · right
      exact thirdFull_scalar_residualQuinticProduct_lowerBound244
        H A E
        ‖h3AuditActualSpectralVelocityTotal hH3 zState‖
        ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖
        (((J2 : ℝ) + 2) ^ 5) hE hRateClock
  exact ⟨s, eta2, J2, zSource, zState, hChoice, hrs,
    heta2, hend2, hzSource, hzState, hExact, hE, hEUpper, hGate⟩

/-- Original cofinal minimal crossing witnesses and disjoint viscous sums,
now with the activated residual physical source-state-frequency obstruction. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_residualPDECofinalLedger244
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
          ThirdFullLateRetainedPrimaryResidualPDECofinalLedger244
            hH3 b m r P V J sSource sState eta1)) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_exactOverlapEnvelope244
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
    have hResidual :=
      thirdFullPhysical_exactOverlapLedger_to_cofinalResidualPDE244
        hH3 hClass hDInt b hb m hmB r P V J hr hP hV
        sSource sState eta1 hsSource hsState heta1 hend1
        (fun x hx => (hFloor x hx).2) hCharge hLedger
    exact ⟨r, J, sSource, sState, eta1, hr, hP,
      hsSource, hsState, hEtaEq, heta1, hend1,
      hFloor, hCharge, hResidual⟩

end
end PrimeTensor.FirstMonomialTriad
