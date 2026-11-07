import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousDeepExcessPDEGate
import Mathlib.Tactic

/-!
# Normalize the cofinal deep-excess physical PDE rate by the PRIMARY H³ height

The existing deep-excess clock obstruction retains the same physical
witnesses and says that H = A / (24 sqrt (R B)) satisfies

    (T - s) * H <= 8 B
    OR H^2 <= (96 K2 C2 (J2 + 2)^5 + 4) B.

Whenever R B > 0, multiplying by 24 sqrt (R B), or its square, gives

    (T - s) * A <= 192 B sqrt (R B)
    OR A^2 <= 576 R B^2 (96 K2 C2 (J2 + 2)^5 + 4).

The second conclusion is a NECESSARY source/state/frequency amplification
condition. This file assumes no uniform bound on the physical multipliers.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Eliminate the constructed secondary height H from the true residual
physical-PDE obstruction, retaining its exact primary R, B, and witnesses. -/
theorem thirdFull_scalar_deepExcess_normalizedPrimaryRate244
    (A R B T s Prod : ℝ) (hRB : 0 < R * B)
    (hGate :
      (T - s) * thirdFullLateConstructiveResidualFloor244 A R B ≤ 8 * B ∨
      (thirdFullLateConstructiveResidualFloor244 A R B) ^ 2 ≤
        (96 * Prod + 4) * B) :
    (T - s) * A ≤ 192 * B * Real.sqrt (R * B) ∨
      A ^ 2 ≤ 576 * R * B ^ 2 * (96 * Prod + 4) := by
  let q : ℝ := Real.sqrt (R * B)
  let H : ℝ := thirdFullLateConstructiveResidualFloor244 A R B
  have hq : 0 < q := Real.sqrt_pos.mpr hRB
  have hIdentity : (24 * q) * H = A := by
    dsimp only [H, thirdFullLateConstructiveResidualFloor244, q]
    field_simp [ne_of_gt hq]
    ring
  have hqsq : q ^ 2 = R * B := by
    dsimp only [q]
    exact Real.sq_sqrt hRB.le
  have hCoeffSq : (24 * q) ^ 2 = 576 * (R * B) := by
    calc
      (24 * q) ^ 2 = 576 * q ^ 2 := by ring
      _ = 576 * (R * B) := by rw [hqsq]
  change (T - s) * H ≤ 8 * B ∨ H ^ 2 ≤ (96 * Prod + 4) * B at hGate
  rcases hGate with hShort | hRate
  · left
    calc
      (T - s) * A = (24 * q) * ((T - s) * H) := by
        rw [← hIdentity]
        ring
      _ ≤ (24 * q) * (8 * B) :=
        mul_le_mul_of_nonneg_left hShort (by positivity)
      _ = 192 * B * Real.sqrt (R * B) := by
        dsimp only [q]
        ring
  · right
    calc
      A ^ 2 = (24 * q) ^ 2 * H ^ 2 := by
        rw [← hIdentity]
        ring
      _ ≤ (24 * q) ^ 2 * ((96 * Prod + 4) * B) :=
        mul_le_mul_of_nonneg_left hRate (sq_nonneg _)
      _ = 576 * R * B ^ 2 * (96 * Prod + 4) := by
        rw [hCoeffSq]
        ring

/-- If an actual physical source-state-frequency product is capped and its
possible squared-height contribution is too small, only clock compression
can satisfy the normalized obstruction. The cap is an explicit premise. -/
theorem thirdFull_scalar_normalizedPrimary_fixedCap_forcesClock244
    (A R B T s Prod Cap : ℝ)
    (hR : 0 ≤ R) (_hB : 0 ≤ B) (hCap : Prod ≤ Cap)
    (hLarge : 576 * R * B ^ 2 * (96 * Cap + 4) < A ^ 2)
    (hGate : (T - s) * A ≤ 192 * B * Real.sqrt (R * B) ∨
      A ^ 2 ≤ 576 * R * B ^ 2 * (96 * Prod + 4)) :
    (T - s) * A ≤ 192 * B * Real.sqrt (R * B) := by
  rcases hGate with hShort | hRate
  · exact hShort
  · have hCoeff : 0 ≤ 576 * R * B ^ 2 := by positivity
    have hMultiplier : 96 * Prod + 4 ≤ 96 * Cap + 4 := by
      linarith only [hCap]
    have hScale := mul_le_mul_of_nonneg_left hMultiplier hCoeff
    have hBound : A ^ 2 ≤ 576 * R * B ^ 2 * (96 * Cap + 4) :=
      hRate.trans hScale
    exact False.elim ((not_le_of_gt hLarge) hBound)

/-- Outside the compressed-clock arm, the actual attained PDE product must
be at least the normalized primary square-height demand. -/
theorem thirdFull_scalar_normalizedPrimary_productDemand244
    (A R B T s Prod : ℝ)
    (hR : 0 < R) (hB : 0 < B)
    (hWide : 192 * B * Real.sqrt (R * B) < (T - s) * A)
    (hGate : (T - s) * A ≤ 192 * B * Real.sqrt (R * B) ∨
      A ^ 2 ≤ 576 * R * B ^ 2 * (96 * Prod + 4)) :
    A ^ 2 / (576 * R * B ^ 2) ≤ 96 * Prod + 4 := by
  rcases hGate with hShort | hRate
  · exact False.elim ((not_le_of_gt hWide) hShort)
  · have hDen : 0 < 576 * R * B ^ 2 := by positivity
    apply (div_le_iff₀ hDen).2
    calc
      A ^ 2 ≤ 576 * R * B ^ 2 * (96 * Prod + 4) := hRate
      _ = (96 * Prod + 4) * (576 * R * B ^ 2) := by ring

/-- The existing deep-excess cofinal ledger, strengthened with a normalized
primary-height alternative at the SAME attained secondary PDE witnesses. -/
def ThirdFullLateRetainedPrimaryNormalizedPDECofinalLedger244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b m r P V : ℝ) (J : ℕ)
    (sSource sState eta1 : ℝ) : Prop :=
  ThirdFullLateRetainedPrimaryDeepExcessPDECofinalLedger244
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
      ((T - s) * A ≤ 192 * B * Real.sqrt (R * B) ∨
        A ^ 2 ≤ 576 * R * B ^ 2 *
          (96 * ‖h3AuditActualSpectralVelocityTotal hH3 zState‖ *
            ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ *
            (((J2 : ℝ) + 2) ^ 5) + 4)))

/-- Convert a real cofinal residual ledger, not a newly postulated PDE
bound, into the normalized primary physical rate or terminal clock fork. -/
theorem thirdFullPhysical_deepExcessLedger_to_normalizedPrimaryPDE244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (b m r P V : ℝ) (J : ℕ) (sSource sState eta1 : ℝ)
    (hm : m ∈ Set.Ioo b T) (hP : 0 < P) (hV : 0 < V)
    (hOld : ThirdFullLateRetainedPrimaryDeepExcessPDECofinalLedger244
      hH3 b m r P V J sSource sState eta1) :
    ThirdFullLateRetainedPrimaryNormalizedPDECofinalLedger244
      hH3 b m r P V J sSource sState eta1 := by
  let A : ℝ := V / (2 * P)
  let B : ℝ := ∫ x in m..T, velocityH3DissipationAt u x ∂volume
  let C0 : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  let E0 : ℝ := 1 + 6 * velocityH3Energy0At u b
  let R : ℝ := 96 * C0 * (((J : ℝ) + 2) ^ 5)
  change ThirdFullLateRetainedPrimaryDeepExcessPDECofinalLedger244
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
        ((T - s) * A ≤ 192 * B * Real.sqrt (R * B) ∨
          A ^ 2 ≤ 576 * R * B ^ 2 *
            (96 * ‖h3AuditActualSpectralVelocityTotal hH3 zState‖ *
              ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ *
              (((J2 : ℝ) + 2) ^ 5) + 4)))
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
  obtain ⟨s, eta2, J2, zSource, zState,
      hChoice, hrs, heta2, hend2, hzSource, hzState, hGate⟩ :=
    hOld.2 hRate hGap hStrong
  let Prod : ℝ :=
    ‖h3AuditActualSpectralVelocityTotal hH3 zState‖ *
      ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ *
      (((J2 : ℝ) + 2) ^ 5)
  have hGateProd :
      (T - s) * thirdFullLateConstructiveResidualFloor244 A R B ≤ 8 * B ∨
      (thirdFullLateConstructiveResidualFloor244 A R B) ^ 2 ≤
        (96 * Prod + 4) * B := by
    simpa only [A, R, B, C0, Prod, mul_assoc] using hGate
  have hNormalized :=
    thirdFull_scalar_deepExcess_normalizedPrimaryRate244
      A R B T s Prod (mul_pos hR hB) hGateProd
  refine ⟨s, eta2, J2, zSource, zState,
    hChoice, hrs, heta2, hend2, hzSource, hzState, ?_⟩
  simpa only [A, R, B, C0, Prod, mul_assoc] using hNormalized

/-- Cofinal prescribed-gauge witnesses retain the original frequency escape,
H³ viscous charges, low-frequency alternatives and actual source/state
maxima. Only the activated deep-excess arm is normalized. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_normalizedPrimaryPDE244
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
          ThirdFullLateRetainedPrimaryNormalizedPDECofinalLedger244
            hH3 b m r P V J sSource sState eta1)) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_deepExcessPDE244
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
    have hNormalized :=
      thirdFullPhysical_deepExcessLedger_to_normalizedPrimaryPDE244
        hH3 b m r P V J sSource sState eta1 hmB hP hV hLedger
    exact ⟨r, J, sSource, sState, eta1, hr, hP,
      hsSource, hsState, hEtaEq, heta1, hend1,
      hFloor, hCharge, hNormalized⟩

end
end PrimeTensor.FirstMonomialTriad
