import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousCofinalResidualPDERate
import Mathlib.Tactic

/-!
# Deep-excess physical PDE factor gate on actual cofinal residual clocks

In the terminal regime 48 sqrt(R B) <= 1, the constructive secondary
actual H3 dissipation floor H=A/(24 sqrt(R B)) obeys H-A >= H/2.
The prior residual PDE obstruction then forces one of TWO alternatives:

    (T-s) H <= 8 B,     or
    H^2 <= (96 K2 C2 (J2+2)^5 + 4) B.

The first is a scale-sensitive concentration law, significantly stronger
than the tautological fact that s -> T. The second is an explicit squared
height vs. ACTUAL attained projected source/state and finite cutoff demand.
No uniform bound on K2, C2 or J2 is inferred. The same cofinal prescribed
gauge crossing witnesses and prior exact overlap envelope are retained.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- With sufficiently small dimensionless R*B, the constructed secondary
floor exceeds TWICE the primary floor. No asymptotic assumptions on R are
needed: the smallness is an explicit pointwise conditional. -/
theorem thirdFull_scalar_deepExcess_floorAtLeastDouble244
    (A R B : ℝ) (hA : 0 < A) (hRB : 0 < R * B)
    (hSmall : 48 * Real.sqrt (R * B) ≤ 1) :
    A ≤ thirdFullLateConstructiveResidualFloor244 A R B / 2 := by
  let q : ℝ := Real.sqrt (R * B)
  let H : ℝ := thirdFullLateConstructiveResidualFloor244 A R B
  have hq : 0 < q := Real.sqrt_pos.mpr hRB
  have hH : 0 < H := by
    dsimp only [H, thirdFullLateConstructiveResidualFloor244, q]
    positivity
  have hIdentity : (24 * q) * H = A := by
    dsimp only [H, thirdFullLateConstructiveResidualFloor244, q]
    field_simp [ne_of_gt hq]
    <;> ring
  have hCoeff : 24 * q ≤ (1 : ℝ) / 2 := by
    change 24 * Real.sqrt (R * B) ≤ (1 : ℝ) / 2
    linarith only [hSmall]
  have hScale := mul_le_mul_of_nonneg_right hCoeff hH.le
  rw [hIdentity] at hScale
  change A ≤ H / 2
  linarith only [hScale]

/-- The residual min-clock alternative and the deep-excess floor force
either a normalized terminal-time compression or a SQUARED secondary
height charged by the physical source/state/frequency multiplier. -/
theorem thirdFull_scalar_deepExcess_residualClock_squaredRate244
    (A B E H T s Prod : ℝ)
    (hH : 0 ≤ H) (hHalf : A ≤ H / 2)
    (hTime : 0 ≤ T - s) (hResidual : E ≤ B)
    (hProd : 0 ≤ Prod)
    (hGate : (T - s) * (H - A) ≤ 4 * E ∨
      H * (H - A) ≤ (48 * Prod + 2) * E) :
    (T - s) * H ≤ 8 * B ∨
      H ^ 2 ≤ (96 * Prod + 4) * B := by
  have hGap : H / 2 ≤ H - A := by
    linarith only [hHalf]
  rcases hGate with hShort | hRate
  · left
    have hScale := mul_le_mul_of_nonneg_left hGap hTime
    have hBound : (T - s) * H ≤ 2 * ((T - s) * (H - A)) := by
      nlinarith only [hScale]
    have hTail : 4 * E ≤ 4 * B :=
      mul_le_mul_of_nonneg_left hResidual (by norm_num)
    nlinarith only [hBound, hShort, hTail]
  · right
    have hScale := mul_le_mul_of_nonneg_left hGap hH
    have hCoeff : 0 ≤ 48 * Prod + 2 := by
      linarith only [hProd]
    have hRateB : H * (H - A) ≤ (48 * Prod + 2) * B :=
      hRate.trans (mul_le_mul_of_nonneg_left hResidual hCoeff)
    nlinarith only [hScale, hRateB]

/-- The old, fully cofinal physical rate certificate is preserved. In the
stronger square-root-tail regime it additionally admits a concrete
squared-height/physical-source-frequency alternative at the SAME secondary
cutoff and attained source/state maxima, rather than selecting new data. -/
def ThirdFullLateRetainedPrimaryDeepExcessPDECofinalLedger244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b m r P V : ℝ) (J : ℕ)
    (sSource sState eta1 : ℝ) : Prop :=
  ThirdFullLateRetainedPrimaryResidualPDECofinalLedger244
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
    48 * Real.sqrt (R * B) ≤ 1 →
    ∃ (s eta2 : ℝ) (J2 : ℕ) (zSource zState : ℝ),
      (s = sState ∨ s = sSource) ∧ r ≤ s ∧
      0 < eta2 ∧ s + eta2 < T ∧
      zSource ∈ Set.Icc s (s + (T - s) / 2) ∧
      zState ∈ Set.Icc s (s + (T - s) / 2) ∧
      (let H : ℝ := thirdFullLateConstructiveResidualFloor244 A R B;
        (T - s) * H ≤ 8 * B ∨
        H ^ 2 ≤
          (96 * ‖h3AuditActualSpectralVelocityTotal hH3 zState‖ *
            ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ *
            (((J2 : ℝ) + 2) ^ 5) + 4) * B))

/-- Upgrade the already-retained secondary physical source/state cutoff
certificate to a dimensionless square-root-tail trilemma without changing
physical witness selection or inserting frequency-uniform estimates. -/
theorem thirdFullPhysical_residualLedger_to_deepExcessPDE244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b m r P V : ℝ) (J : ℕ) (sSource sState eta1 : ℝ)
    (hm : m ∈ Set.Ioo b T) (hP : 0 < P) (hV : 0 < V)
    (hOld : ThirdFullLateRetainedPrimaryResidualPDECofinalLedger244
      hH3 b m r P V J sSource sState eta1) :
    ThirdFullLateRetainedPrimaryDeepExcessPDECofinalLedger244
      hH3 b m r P V J sSource sState eta1 := by
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ x in m..T, velocityH3DissipationAt u x ∂volume
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let R : ℝ := 96 * C0 * (((J : ℝ) + 2) ^ 5)
  change ThirdFullLateRetainedPrimaryResidualPDECofinalLedger244
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
        (let H : ℝ := thirdFullLateConstructiveResidualFloor244 A R B;
          (T - s) * H ≤ 8 * B ∨
          H ^ 2 ≤
            (96 * ‖h3AuditActualSpectralVelocityTotal hH3 zState‖ *
              ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ *
              (((J2 : ℝ) + 2) ^ 5) + 4) * B))
  refine ⟨hOld, ?_⟩
  intro hRate hGap hStrong
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hC0 : 0 < C0 := by
    dsimp only [C0]
    have hCoeff := h3AuditInitialLerayEnergyCoefficient_nonneg
    linarith only [hCoeff]
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
  have hSmall : 24 * Real.sqrt (R * B) < 1 := by
    linarith only [hStrong]
  obtain ⟨s, eta2, J2, zSource, zState,
      hChoice, hrs, heta2, hend2, hzSource, hzState,
      _hEnvelope, hE, hEUpper, hRateGate⟩ :=
    hOld.2 hRate hGap hSmall
  let H : ℝ := thirdFullLateConstructiveResidualFloor244 A R B
  let E : ℝ := thirdFullLateResidualTwoClockAction244 A B r s eta1 eta2
  let K2 : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 zState‖
  let C2 : ℝ := ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖
  let S2 : ℝ := (((J2 : ℝ) + 2) ^ 5)
  let Prod : ℝ := K2 * C2 * S2
  have hHPos : 0 < H := by
    dsimp only [H, thirdFullLateConstructiveResidualFloor244]
    positivity
  have hHalf : A ≤ H / 2 :=
    thirdFull_scalar_deepExcess_floorAtLeastDouble244
      A R B hA (mul_pos hR hB) hStrong
  have hTime : 0 ≤ T - s := by
    linarith only [heta2, hend2]
  have hProd : 0 ≤ Prod := by
    dsimp only [Prod, K2, C2, S2]
    positivity
  have hConverted :
      (T - s) * (H - A) ≤ 4 * E ∨
        H * (H - A) ≤ (48 * Prod + 2) * E := by
    rcases hRateGate with hShort | hRatePhysical
    · exact Or.inl hShort
    · right
      have hDen : 0 < 48 * E := by positivity
      have hFrac :
          (H * (H - A) - 2 * E) / (48 * E) ≤ Prod := by
        simpa only [Prod, K2, C2, S2] using hRatePhysical
      have hCross := (div_le_iff₀ hDen).mp hFrac
      nlinarith only [hCross]
  have hStrongGate :=
    thirdFull_scalar_deepExcess_residualClock_squaredRate244
      A B E H T s Prod hHPos.le hHalf hTime hEUpper hProd hConverted
  refine ⟨s, eta2, J2, zSource, zState,
    hChoice, hrs, heta2, hend2, hzSource, hzState, ?_⟩
  simpa only [H, Prod, K2, C2, S2, mul_assoc] using hStrongGate

/-- The actual prescribed-gauge no-H3-terminal-trace cofinal witnesses
retain their frequency escape, disjoint physical viscous action and complete
residual envelope; the deep-excess branch pays in terminal distance or
requires squared-height physical source-state-frequency amplification. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_deepExcessPDE244
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
          ThirdFullLateRetainedPrimaryDeepExcessPDECofinalLedger244
            hH3 b m r P V J sSource sState eta1)) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_residualPDECofinalLedger244
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
    have hDeep :=
      thirdFullPhysical_residualLedger_to_deepExcessPDE244
        hH3 b m r P V J sSource sState eta1 hmB hP hV hLedger
    exact ⟨r, J, sSource, sState, eta1, hr, hP,
      hsSource, hsState, hEtaEq, heta1, hend1,
      hFloor, hCharge, hDeep⟩


end
end PrimeTensor.FirstMonomialTriad
