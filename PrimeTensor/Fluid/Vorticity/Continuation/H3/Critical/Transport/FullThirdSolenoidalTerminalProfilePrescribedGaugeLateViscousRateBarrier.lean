import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousExplicitPDEClock
import Mathlib.Tactic

/-!
# The actual late-viscous PDE clock forces terminal-time compression or a physical rate barrier

The exact physical-PDE persistence width in the preceding module is

  eta = min ((T-r)/4) (A/(2*(Lambda+1))),
  eta*A <= B,

with A=H(vk)^4/(2*P), B the actual terminal H^3 viscous integral, and Lambda
the finite-cutoff projected-Navier--Stokes variation rate computed from the
attained source and spectral-state maxima. Eliminating eta gives either

  (T-r)*A <= 4*B, or A^2 <= 2*(Lambda+1)*B.

This separates *physical terminal-clock compression* from an explicit
*source/state-dependent PDE rate payment*. The old quartic Fourier carrier,
early attained source peak, kinetic clock, minimal first-crossing annuli,
disjoint physical viscous charges and prescribed-gauge outer-frequency escape
are retained on the SAME cofinal witnesses. No terminal-uniform coefficient
bound or Navier--Stokes continuation conclusion is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Eliminate the min-clock from its actual integrated cost. Either the
available time width is itself charged to the terminal integral, or the
squared spike height must be paid by the physical PDE variation rate.
There is no sign assumption on A or the budget B. -/
theorem thirdFull_scalar_minPDEClock_timeOrRate244
    (A Lambda d B eta : ℝ) (hLambda : 0 ≤ Lambda)
    (hClock : eta = min (d / 2) (A / (2 * (Lambda + 1))))
    (hCost : eta * A ≤ B) :
    d * A ≤ 2 * B ∨ A ^ 2 ≤ 2 * (Lambda + 1) * B := by
  by_cases hFirst : d / 2 ≤ A / (2 * (Lambda + 1))
  · have hEta : eta = d / 2 := by
      rw [hClock, min_eq_left hFirst]
    have hSmall : (d / 2) * A ≤ B := by
      simpa only [hEta] using hCost
    left
    calc
      d * A = 2 * ((d / 2) * A) := by ring
      _ ≤ 2 * B := mul_le_mul_of_nonneg_left hSmall (by norm_num)
  · have hSecond : A / (2 * (Lambda + 1)) ≤ d / 2 :=
      (lt_of_not_ge hFirst).le
    have hEta : eta = A / (2 * (Lambda + 1)) := by
      rw [hClock, min_eq_right hSecond]
    have hSmall : (A / (2 * (Lambda + 1))) * A ≤ B := by
      simpa only [hEta] using hCost
    have hPos : 0 < 2 * (Lambda + 1) := by
      linarith only [hLambda]
    right
    calc
      A ^ 2 = (A / (2 * (Lambda + 1))) * A *
          (2 * (Lambda + 1)) := by
            field_simp [ne_of_gt hPos]
            <;> ring
      _ ≤ B * (2 * (Lambda + 1)) :=
        mul_le_mul_of_nonneg_right hSmall hPos.le
      _ = 2 * (Lambda + 1) * B := by ring

/-- The prescribed-gauge first-crossing witnesses now carry a FOUR-way
physical rate gate. On the late-viscous branch the exact clock eta has been
eliminated: the actual remaining time times the normalized fourth-power
amplitude must be small, OR the square of that amplitude is paid by the
actual finite-band PDE variation coefficient times terminal H^3 dissipation.
Neither rate nor state/source maxima are substituted by an artificial bound. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_lateRateOrCompression244
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
            (V / (2 * P)) ^ 2 ≤
              2 * (thirdFullLateViscousLowRadialPDERate244 J
                ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
                ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ + 1) * B))) ∧
      Tendsto (fun k : ℕ =>
        ∫ s in ((tau (v k) + T) / 2)..T,
          velocityH3DissipationAt u s ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hOld, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_lateExplicitPDEClock244
      hH3 hClass b hb hNoTrace hDInt H hH
  have hNew : ∀ᶠ k : ℕ in atTop,
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
          (V / (2 * P)) ^ 2 ≤
            2 * (thirdFullLateViscousLowRadialPDERate244 J
              ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
              ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ + 1) * B)) := by
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
      ⟨r, J, sSource, sState, eta, hr, hP, hsSource, hsState,
        hEta, _hEtaPos, _hEnd, _hFloor, hCost⟩
    · exact Or.inl hCarrier
    · exact Or.inr (Or.inl hSource)
    · exact Or.inr (Or.inr (Or.inl hClock))
    · right; right; right
      let A : ℝ := V / (2 * P)
      let Lambda : ℝ := thirdFullLateViscousLowRadialPDERate244 J
        ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
        ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖
      have hLambda : 0 ≤ Lambda := by
        dsimp only [Lambda, thirdFullLateViscousLowRadialPDERate244]
        positivity
      have hQuarter : ((T - r) / 2) / 2 = (T - r) / 4 := by
        ring
      have hExact : eta = min (((T - r) / 2) / 2)
          (A / (2 * (Lambda + 1))) := by
        rw [hQuarter]
        simpa only [A, Lambda, V] using hEta
      have hRealCharge : eta * A ≤ B := by
        simpa only [A, B, V] using hCost
      have hGate := thirdFull_scalar_minPDEClock_timeOrRate244
        A Lambda ((T - r) / 2) B eta hLambda hExact hRealCharge
      have hGate' : (T - r) * A ≤ 4 * B ∨
          A ^ 2 ≤ 2 * (Lambda + 1) * B := by
        rcases hGate with hShort | hFast
        · left
          calc
            (T - r) * A = 2 * (((T - r) / 2) * A) := by ring
            _ ≤ 2 * (2 * B) :=
              mul_le_mul_of_nonneg_left hShort (by norm_num)
            _ = 4 * B := by ring
        · exact Or.inr hFast
      refine ⟨r, J, sSource, sState, hr, hP, hsSource, hsState, ?_⟩
      simpa only [A, Lambda, B, V] using hGate'
  exact ⟨U, tau, N, K, C, delta, v, hMono, hLimit,
    hWindows, hCharges, hEscape, hNew, hViscousTail⟩

end
end PrimeTensor.FirstMonomialTriad
