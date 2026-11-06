import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousConstructiveSqrtTail
import Mathlib.Tactic

/-!
# A SECOND physical PDE persistence clock forces a squared terminal H³ action

The constructive two-slice spike threshold h=A/(12 sqrt(R B)), where B is the
actual terminal H³ dissipation integral, carries its own finite-frequency
Navier--Stokes clock. Eliminate THAT clock, apply the existing quintic
finite-band physical rate bound, and clear the strictly positive denominator.

The result is a necessary three-way alternative:
  (T-s) A <= 96 B sqrt(R B),
  A² <= 2304 R B²,
  A² <= 55296 R K₂ C₂ (J₂+2)^5 B².

Crucially, the two persistence intervals may overlap. No viscous interval
costs are added or treated as independently disjoint. The extra power B²
comes from the independently certified *height* h of the SECOND spike and
its own time variation, not from falsely adding two charges.

The cutoff J₂ and attained K₂,C₂ are genuinely selected by the physical PDE.
No terminal-uniform modulus, frequency cap, or continuation is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Multiplying a SECOND physical clock/rate alternative by the positive
scale 24 sqrt(R B) produces an extra full power of the terminal action.
The factor 55296 is 576 times the verified quintic factor 96. -/
theorem thirdFull_scalar_secondarySqrtTailClock_forces_squaredBudget244
    (A B R S K C d : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R)
    (hGate :
      d * (A / (24 * Real.sqrt (R * B))) ≤ 4 * B ∨
      (A / (24 * Real.sqrt (R * B))) ^ 2 ≤ 4 * B ∨
      (A / (24 * Real.sqrt (R * B))) ^ 2 ≤
        96 * K * C * S * B) :
    d * A ≤ 96 * B * Real.sqrt (R * B) ∨
    A ^ 2 ≤ 2304 * R * B ^ 2 ∨
    A ^ 2 ≤ 55296 * R * K * C * S * B ^ 2 := by
  let q : ℝ := Real.sqrt (R * B)
  have hRB : 0 < R * B := mul_pos hR hB
  have hq : 0 < q := Real.sqrt_pos.2 hRB
  have hqSq : q ^ 2 = R * B := Real.sq_sqrt hRB.le
  have hPosScale : 0 ≤ 576 * R * B := by positivity
  have hScaleEq : 576 * R * B = (24 * q) ^ 2 := by
    calc
      576 * R * B = 576 * (R * B) := by ring
      _ = 576 * q ^ 2 := by rw [hqSq]
      _ = (24 * q) ^ 2 := by ring
  have hSquareCancel :
      (A / (24 * q)) ^ 2 * (576 * R * B) = A ^ 2 := by
    rw [hScaleEq]
    field_simp [ne_of_gt hq]
    <;> ring
  have hGate' :
      d * (A / (24 * q)) ≤ 4 * B ∨
      (A / (24 * q)) ^ 2 ≤ 4 * B ∨
      (A / (24 * q)) ^ 2 ≤ 96 * K * C * S * B := by
    simpa only [q] using hGate
  rcases hGate' with hTime | hTail | hRate
  · left
    have hMul := mul_le_mul_of_nonneg_right hTime (by positivity : 0 ≤ 24 * q)
    calc
      d * A = (d * (A / (24 * q))) * (24 * q) := by
        field_simp [ne_of_gt hq]
        <;> ring
      _ ≤ (4 * B) * (24 * q) := hMul
      _ = 96 * B * q := by ring
      _ = 96 * B * Real.sqrt (R * B) := rfl
  · right; left
    have hMul := mul_le_mul_of_nonneg_right hTail hPosScale
    calc
      A ^ 2 = (A / (24 * q)) ^ 2 * (576 * R * B) := hSquareCancel.symm
      _ ≤ (4 * B) * (576 * R * B) := hMul
      _ = 2304 * R * B ^ 2 := by ring
  · right; right
    have hMul := mul_le_mul_of_nonneg_right hRate hPosScale
    calc
      A ^ 2 = (A / (24 * q)) ^ 2 * (576 * R * B) := hSquareCancel.symm
      _ ≤ (96 * K * C * S * B) * (576 * R * B) := hMul
      _ = 55296 * R * K * C * S * B ^ 2 := by ring

/-- Second-generation terminal-tail budget, retaining the actual secondary
clock's selected time and cutoff and the physical maxima on its own window. -/
def ThirdFullLateSecondarySquaredTailBarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (sState sSource A B R : ℝ) : Prop :=
  ∃ (s : ℝ) (J2 : ℕ) (zSource zState : ℝ),
    (s = sState ∨ s = sSource) ∧
    zSource ∈ Set.Icc s (s + (T - s) / 2) ∧
    zState ∈ Set.Icc s (s + (T - s) / 2) ∧
    ((T - s) * A ≤ 96 * B * Real.sqrt (R * B) ∨
      A ^ 2 ≤ 2304 * R * B ^ 2 ∨
      A ^ 2 ≤ 55296 * R *
        ‖h3AuditActualSpectralVelocityTotal hH3 zState‖ *
        ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖ *
        (((J2 : ℝ) + 2) ^ 5) * B ^ 2)

/-- The constructive secondary finite-band clock can be eliminated without
any assertion that its interval is disjoint from the original late window.
Its SECOND positive height is A/(24 sqrt(R B)); hence the rate branches
require *two powers* of the terminal H³ viscous integral B. -/
theorem thirdFullPhysical_secondaryPDEClock_forces_squaredTailBarrier244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (m sState sSource A B R : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hR : 0 < R)
    (hBdef : B = ∫ t in m..T, velocityH3DissipationAt u t ∂volume)
    (hClock : ThirdFullLateSecondaryPDEClock244 hH3 m sState sSource
      (A / (12 * Real.sqrt (R * B)))) :
    ThirdFullLateSecondarySquaredTailBarrier244
      hH3 sState sSource A B R := by
  rcases hClock with ⟨s, hChoice, J2, zSource, zState, eta,
      hzSource, hzState, hEtaEq, hEtaPos, hEtaEnd, hFloor, hCost⟩
  let K : ℝ := ‖h3AuditActualSpectralVelocityTotal hH3 zState‖
  let C : ℝ := ‖h3PathActualProjectedMomentumSource244 hH3 zSource‖
  let Lambda : ℝ := thirdFullLateViscousLowRadialPDERate244 J2 K C
  let S : ℝ := (((J2 : ℝ) + 2) ^ 5)
  let a2 : ℝ := A / (24 * Real.sqrt (R * B))
  have hLambda : 0 ≤ Lambda := by
    dsimp only [Lambda, thirdFullLateViscousLowRadialPDERate244]
    positivity
  have hq : 0 < Real.sqrt (R * B) :=
    Real.sqrt_pos.2 (mul_pos hR hB)
  have hSmallEq :
      (A / (12 * Real.sqrt (R * B))) / 2 = a2 := by
    dsimp only [a2]
    field_simp [ne_of_gt hq]
    <;> ring
  have hQuarter : ((T - s) / 2) / 2 = (T - s) / 4 := by ring
  have hClockEq : eta = min (((T - s) / 2) / 2)
      (a2 / (2 * (Lambda + 1))) := by
    rw [hQuarter]
    simpa only [hSmallEq, Lambda, K, C] using hEtaEq
  have hCost' : eta * a2 ≤ B := by
    rw [hBdef]
    simpa only [hSmallEq] using hCost
  have hMinGate := thirdFull_scalar_minPDEClock_timeOrRate244
    a2 Lambda ((T - s) / 2) B eta hLambda hClockEq hCost'
  have hCutoffRate : Lambda ≤ 24 * K * C * S := by
    dsimp only [Lambda, S]
    exact thirdFull_lateLowRadialPDERate_le_quinticPhysicalProduct244
      J2 K C (norm_nonneg _) (norm_nonneg _)
  have hGate :
      (T - s) * a2 ≤ 4 * B ∨
      a2 ^ 2 ≤ 4 * B ∨
      a2 ^ 2 ≤ 96 * K * C * S * B := by
    rcases hMinGate with hTime | hRate
    · left
      calc
        (T - s) * a2 = 2 * (((T - s) / 2) * a2) := by ring
        _ ≤ 2 * (2 * B) :=
          mul_le_mul_of_nonneg_left hTime (by norm_num)
        _ = 4 * B := by ring
    · right
      exact thirdFull_scalar_lateRate_quinticProductOrTail244
        a2 B Lambda K C S hB.le hRate hCutoffRate
  have hScaledGate :
      (T - s) * A ≤ 96 * B * Real.sqrt (R * B) ∨
      A ^ 2 ≤ 2304 * R * B ^ 2 ∨
      A ^ 2 ≤ 55296 * R * K * C * S * B ^ 2 := by
    apply thirdFull_scalar_secondarySqrtTailClock_forces_squaredBudget244
      A B R S K C (T - s) hA hB hR
    simpa only [a2] using hGate
  unfold ThirdFullLateSecondarySquaredTailBarrier244
  refine ⟨s, J2, zSource, zState, hChoice, hzSource, hzState, ?_⟩
  simpa only [K, C, S] using hScaledGate


/-- Same prescribed-gauge first-crossing witnesses and terminal viscous
charge limit, now with the SECOND finite-band PDE clock converted into a
necessary *squared* terminal-tail budget on the constructive non-kinetic
branch. This does not add overlapping physical interval charges. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_lateSecondarySquaredTailGate244
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
        let B := ∫ s in m..T, velocityH3DissipationAt u s ∂volume
        V < 14 * Q ^ 4 *
          ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
        (∃ r : ℝ, r ∈ Set.Icc t m ∧
          V < 28 * Q ^ 4 *
            (‖F‖ * ((m - t) *
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖))) ∨
        V < 56 * Q ^ 4 * (‖F‖ * C0 * ((T - m) * E0)) ∨
        (∃ (r : ℝ) (J : ℕ) (sSource sState : ℝ),
          r ∈ Set.Ioo m T ∧ 0 < P ∧
          sSource ∈ Set.Icc r (r + (T - r) / 2) ∧
          sState ∈ Set.Icc r (r + (T - r) / 2) ∧
          ((T - r) * (V / (2 * P)) ≤ 4 * B ∨
          (V / (2 * P)) ^ 2 ≤ 4 * B ∨
          ((V / (2 * P)) ^ 2 ≤
            96 * (E0 + 3 * velocityH3DissipationAt u sState) *
              (C0 * (E0 + 3 * velocityH3DissipationAt u sSource)) *
              (((J : ℝ) + 2) ^ 5) * B ∧
            (∀ h : ℝ, 0 < h →
              96 * C0 * (((J : ℝ) + 2) ^ 5) * (E0 + 3 * h) ^ 2 * B <
                (V / (2 * P)) ^ 2 →
              ThirdFullLateSecondaryPDEClock244 hH3 m sState sSource h) ∧
            (4 * (96 * C0 * (((J : ℝ) + 2) ^ 5)) * B * E0 ^ 2 <
                (V / (2 * P)) ^ 2 →
              ThirdFullLateSecondaryPDEClock244 hH3 m sState sSource
                ((V / (2 * P)) /
                  (12 * Real.sqrt ((96 * C0 * (((J : ℝ) + 2) ^ 5)) * B))) ∧
              (∃ J2 : ℕ,
                ((V / (2 * P)) /
                    (12 * Real.sqrt ((96 * C0 * (((J : ℝ) + 2) ^ 5)) * B))) / 2 <
                  4 * velocityH3Energy0At u b * (((J2 : ℝ) + 1) ^ 8)) ∧
              ThirdFullLateSecondarySquaredTailBarrier244 hH3 sState sSource
                (V / (2 * P)) B
                (96 * C0 * (((J : ℝ) + 2) ^ 5))))))) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_lateConstructiveSqrtTailGate244
      hH3 hClass b hb hNoTrace hDInt H hH
  refine ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
    hWindows, hCharges, hEscape, ?_, hViscousTail⟩
  filter_upwards [hOld] with k hkOld
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
  let B : ℝ := ∫ s in m..T, velocityH3DissipationAt u s ∂volume
  rcases hkOld with hCarrier | hSource | hClock |
      ⟨r, J, sSource, sState, hr, hP, hsSource, hsState, hGate⟩
  · exact Or.inl hCarrier
  · exact Or.inr (Or.inl hSource)
  · exact Or.inr (Or.inr (Or.inl hClock))
  · right; right; right
    rcases hGate with hTime | hTail | ⟨hRate, hAll, hConstructive⟩
    · exact ⟨r, J, sSource, sState, hr, hP, hsSource, hsState,
        Or.inl hTime⟩
    · exact ⟨r, J, sSource, sState, hr, hP, hsSource, hsState,
        Or.inr (Or.inl hTail)⟩
    · refine ⟨r, J, sSource, sState, hr, hP, hsSource, hsState,
        Or.inr (Or.inr ⟨hRate, hAll, ?_⟩)⟩
      intro hGap
      obtain ⟨hSecondary, hCutoff⟩ := hConstructive hGap
      let A : ℝ := V / (2 * P)
      let S : ℝ := (((J : ℝ) + 2) ^ 5)
      let R : ℝ := 96 * C0 * S
      have hA : 0 < A := by
        dsimp only [A, V]
        have hHpos : 0 < H (v k) :=
          lt_of_lt_of_le zero_lt_one (hH (v k))
        positivity
      have hC0 : 0 < C0 := by
        dsimp only [C0]
        have hCoeff := h3AuditInitialLerayEnergyCoefficient_nonneg
        linarith only [hCoeff]
      have hS : 0 < S := by
        dsimp only [S]
        positivity
      have hR : 0 < R := by
        dsimp only [R]
        positivity
      have hmT : m < T := lt_trans hr.1 hr.2
      have hB0 : 0 ≤ B := by
        dsimp only [B]
        exact intervalIntegral.integral_nonneg hmT.le
          (fun s _ => velocityH3DissipationAt_nonneg u s)
      have hB : 0 < B := by
        by_contra hNot
        have hBzero : B = 0 :=
          le_antisymm (le_of_not_gt hNot) hB0
        have hRateZero : A ^ 2 ≤ 0 := by
          have hRateB : A ^ 2 ≤
              96 * (E0 + 3 * velocityH3DissipationAt u sState) *
                (C0 * (E0 + 3 * velocityH3DissipationAt u sSource)) *
                S * B := by
            exact hRate
          simpa only [hBzero, mul_zero] using hRateB
        have hAPosSq : 0 < A ^ 2 := by positivity
        exact (not_le_of_gt hAPosSq) hRateZero
      have hSecondary' : ThirdFullLateSecondaryPDEClock244
          hH3 m sState sSource (A / (12 * Real.sqrt (R * B))) := by
        simpa only [A, R, S] using hSecondary
      have hSquared : ThirdFullLateSecondarySquaredTailBarrier244
          hH3 sState sSource A B R :=
        thirdFullPhysical_secondaryPDEClock_forces_squaredTailBarrier244
          hH3 m sState sSource A B R hA hB hR rfl hSecondary'
      refine ⟨hSecondary, hCutoff, ?_⟩
      simpa only [A, R, S] using hSquared

end
end PrimeTensor.FirstMonomialTriad
