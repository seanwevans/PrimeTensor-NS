import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeDelayedViscousTail
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Actual late viscous time spikes from prescribed-gauge terminal source escape

The previous four-way physical obstruction leaves an actual terminal
H³-dissipation INTEGRAL, weighted by the selected outer Fourier frequency.
Here the strict late integral branch is upgraded to an actual observation
of the physical H³ dissipation on the delayed terminal half interval.

This is a genuine time of observation (not a separately postulated cutoff
or source ceiling). The alternative now distinguishes:

1. fixed terminal physical Fourier highpass;
2. an attained physical projected-source peak on the early half;
3. a terminal kinetic clock multiplied by the selected outer radius;
4. an actual late physical H³-dissipation spike, with inverse terminal
   half-width scaling.

The gauge-dependent minimal annulus, disjoint full-viscous charges, cofinal
terminal times, and outer/gauge escape are unchanged. A peak in the last
branch is compatible with finite dissipation because its time duration may
shrink rapidly. No upper bound on the selected outer frequency is proved.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- Strict integrated cost on a genuine interval yields an actual *interior*
time at which the value exceeds its averaged threshold. No endpoint value
of the time-dependent function is used; the prefactor may be any real. -/
theorem thirdFull_strictIntegralCost_forces_actualTimePeak244
    (D : ℝ → ℝ) (m T K R : ℝ)
    (hm : m < T)
    (hD : IntervalIntegrable D volume m T)
    (hLarge : R < K * (∫ r in m..T, D r ∂volume)) :
    ∃ r : ℝ, r ∈ Set.Ioo m T ∧ R < K * (T - m) * D r := by
  by_contra hNot
  have hWidth : 0 < T - m := sub_pos.mpr hm
  have hAtMost (r : ℝ) (hr : r ∈ Set.Ioo m T) :
      K * (T - m) * D r ≤ R := by
    by_contra hNo
    exact hNot ⟨r, hr, lt_of_not_ge hNo⟩
  have hPointwise (r : ℝ) (hr : r ∈ Set.Ioo m T) :
      K * D r ≤ R / (T - m) := by
    apply (le_div_iff₀ hWidth).2
    calc
      K * D r * (T - m) = K * (T - m) * D r := by ring
      _ ≤ R := hAtMost r hr
  have hCompare :
      (∫ r in m..T, K * D r ∂volume) ≤
        (∫ _r in m..T, R / (T - m) ∂volume) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      hm.le (hD.const_mul K) intervalIntegrable_const
    intro r hr
    exact hPointwise r hr
  have hConstant :
      (∫ _r in m..T, R / (T - m) ∂volume) = R := by
    calc
      _ = (T - m) * (R / (T - m)) := by
        simp <;> ring
      _ = R := by field_simp [ne_of_gt hWidth]
  have hBound : K * (∫ r in m..T, D r ∂volume) ≤ R := by
    calc
      _ = ∫ r in m..T, K * D r ∂volume := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ _r in m..T, R / (T - m) ∂volume := hCompare
      _ = R := hConstant
  exact (not_lt_of_ge hBound) hLarge

/-- On the SAME minimal Navier--Stokes crossing witnesses, a late viscous
integral channel forces a genuine interior pointwise H³-dissipation spike.
The early source channel likewise has an actual attained observation time.
No peak-to-area estimate is inferred in either direction. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_actualLateViscousPeak244
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
      (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k, ThirdFullProfileMinimalAttainedSourceWindow244 hH3
        (fun n : ℕ => (H n) ^ 8) τ N K C δ (v k)) ∧
      (∀ j : ℕ,
        (∑ k ∈ Finset.range j,
          δ (v k) * ((H (v k)) ^ 8 / 4)) ≤
            ∫ r in a..T, velocityH3DissipationAt u r) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / H (v k)) atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        let t := τ (v k)
        let m := (t + T) / 2
        let Q := (N (v k) : ℝ) + 2
        let F := h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
        let C₀ := 3 + h3AuditInitialLerayEnergyCoefficient
        let E₀ := 1 + 6 * velocityH3Energy0At u b
        (H (v k)) ^ 4 < 14 * Q ^ 4 *
          ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
        (∃ r : ℝ, r ∈ Set.Icc t m ∧
          (H (v k)) ^ 4 < 28 * Q ^ 4 *
            (‖F‖ * ((m - t) *
              ‖h3PathActualProjectedMomentumSource244 hH3 r‖))) ∨
        (H (v k)) ^ 4 < 56 * Q ^ 4 *
          (‖F‖ * C₀ * ((T - m) * E₀)) ∨
        (∃ r : ℝ, r ∈ Set.Ioo m T ∧
          (H (v k)) ^ 4 < 168 * Q ^ 4 *
            (‖F‖ * C₀ * (T - m) * velocityH3DissipationAt u r))) ∧
      Tendsto (fun k : ℕ =>
        ∫ r in ((τ (v k) + T) / 2)..T,
          velocityH3DissipationAt u r ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨U, τ, N, K, C, δ, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hFour, hViscousTail⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_fourPhysicalChannels244
      hH3 hClass b hb hNoTrace hDInt H hH
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  let C₀ : ℝ := 3 + h3AuditInitialLerayEnergyCoefficient
  have hAfter : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)
  have hPeaks : ∀ᶠ k : ℕ in atTop,
      let t := τ (v k)
      let m := (t + T) / 2
      let Q := (N (v k) : ℝ) + 2
      let F := h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
      let C₀ := 3 + h3AuditInitialLerayEnergyCoefficient
      let E₀ := 1 + 6 * velocityH3Energy0At u b
      (H (v k)) ^ 4 < 14 * Q ^ 4 *
        ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
      (∃ r : ℝ, r ∈ Set.Icc t m ∧
        (H (v k)) ^ 4 < 28 * Q ^ 4 *
          (‖F‖ * ((m - t) *
            ‖h3PathActualProjectedMomentumSource244 hH3 r‖))) ∨
      (H (v k)) ^ 4 < 56 * Q ^ 4 *
        (‖F‖ * C₀ * ((T - m) * E₀)) ∨
      (∃ r : ℝ, r ∈ Set.Ioo m T ∧
        (H (v k)) ^ 4 < 168 * Q ^ 4 *
          (‖F‖ * C₀ * (T - m) * velocityH3DissipationAt u r)) := by
    filter_upwards [hFour, hAfter] with k hkFour hkAfter
    dsimp only at hkFour ⊢
    let t : ℝ := τ (v k)
    let m : ℝ := (t + T) / 2
    let Q : ℝ := (N (v k) : ℝ) + 2
    have ht0 : 0 < t := by
      dsimp only [t]
      exact lt_trans hClass.terminal_start.1
        (lt_trans hb.1 hkAfter)
    have hEnd : t < T := by
      rcases (hWindows k).1.1 with
        ⟨_, _, _, hδ, _, hEnd, _, _, _, _, _, _, _⟩
      dsimp only [t]
      linarith only [hδ, hEnd]
    have htm : t < m := by
      dsimp only [m]
      linarith only [hEnd]
    have hmT : m < T := by
      dsimp only [m]
      linarith only [hEnd]
    rcases hkFour with hCarrier | hEarly | hClock | hViscous
    · exact Or.inl hCarrier
    · right; left
      obtain ⟨r, hr, _hMax, hEq⟩ :=
        h3Path_actualSourceWindowEnvelope_attained244
          hH3 ht0 htm hmT
      refine ⟨r, hr, ?_⟩
      simpa only [t, m, Q, F, hEq] using hEarly
    · exact Or.inr (Or.inr (Or.inl hClock))
    · right; right; right
      have hm : m ∈ Set.Ioo a T := by
        dsimp only [m, t]
        constructor <;> linarith only [hb.1, hkAfter, hEnd]
      have hDtail : IntervalIntegrable
          (velocityH3DissipationAt u) volume m T := by
        apply hDInt.mono_set
        intro r hr
        have hr' : r ∈ Set.Icc m T := by
          simpa only [Set.uIcc_of_le hm.2.le] using hr
        have hr'' : r ∈ Set.Icc a T :=
          ⟨hm.1.le.trans hr'.1, hr'.2⟩
        simpa only [Set.uIcc_of_le hClass.terminal_start.2.le]
          using hr''
      have hStrict : (H (v k)) ^ 4 <
          (168 * Q ^ 4 * (‖F‖ * C₀)) *
            (∫ r in m..T, velocityH3DissipationAt u r ∂volume) := by
        convert hViscous using 1 <;> ring
      obtain ⟨r, hr, hPeak⟩ :=
        thirdFull_strictIntegralCost_forces_actualTimePeak244
          (velocityH3DissipationAt u) m T
          (168 * Q ^ 4 * (‖F‖ * C₀)) ((H (v k)) ^ 4)
          hmT hDtail hStrict
      refine ⟨r, hr, ?_⟩
      convert hPeak using 1 <;> ring
  exact ⟨U, τ, N, K, C, δ, v, hMono, hLimit,
    hWindows, hCharges, hEscape, hPeaks, hViscousTail⟩

end
end PrimeTensor.FirstMonomialTriad
