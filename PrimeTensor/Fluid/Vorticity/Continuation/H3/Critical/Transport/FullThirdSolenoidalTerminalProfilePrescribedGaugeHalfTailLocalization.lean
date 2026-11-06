import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfilePrescribedGaugeTwoChannelBarrier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Localized physical projected-source alternatives at prescribed Fourier gauges

The terminal-source branch in the genuine same-witness quartic moment
obstruction is refined by an exact *time* decomposition. On the anchored
half-terminal interval the actual physical source has an attained norm
maximum, not merely an arbitrary PDE coefficient. Its earlier action is
bounded by this maximum times the available half-terminal time. All other
source action is confined to the later terminal half.

Consequently each sufficiently late minimal first-crossing window has one
of three distinct physical payments: terminal Fourier carrier, attained
compact-time source intensity, or delayed physical source tail. This keeps
the original disjoint viscous charges and prescribed-gauge outer-frequency
escape. It does not exclude the delayed source branch or prove continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A strict quartic source payment, decomposed into two nonnegative
contributions, forces either contribution to pay with factor 28. -/
theorem thirdFull_quartic_sourceTail_twoPiece244
    (R Q S E L : ℝ) (hQ : 0 ≤ Q)
    (hSource : R < 14 * Q ^ 4 * S)
    (hSplit : S ≤ E + L) :
    R < 28 * Q ^ 4 * E ∨ R < 28 * Q ^ 4 * L := by
  have hCoef : 0 ≤ 14 * Q ^ 4 := by positivity
  have hBound : R < 14 * Q ^ 4 * (E + L) :=
    hSource.trans_le (mul_le_mul_of_nonneg_left hSplit hCoef)
  have hAdd : R < (14 * Q ^ 4 * E) + (14 * Q ^ 4 * L) := by
    convert hBound using 1 <;> ring
  by_cases hEarly : R < 28 * Q ^ 4 * E
  · exact Or.inl hEarly
  · right
    have hEarlyLe : 28 * Q ^ 4 * E ≤ R := le_of_not_gt hEarly
    nlinarith only [hAdd, hEarlyLe]

/-- The *actual* Bochner source L1 action splits at an intermediate time;
the first portion is controlled by a genuine physical norm envelope. -/
theorem thirdFull_projectedSource_firstPiece_le_maxPlusTail244
    (G : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (t m T E : ℝ) (htm : t ≤ m) (hmT : m ≤ T)
    (hInt : IntervalIntegrable G volume t T)
    (hMax : ∀ r : ℝ, r ∈ Set.Icc t m → ‖G r‖ ≤ E) :
    (∫ r in t..T, ‖G r‖ ∂volume) ≤
      (m - t) * E + (∫ r in m..T, ‖G r‖ ∂volume) := by
  have hFirst : IntervalIntegrable (fun r : ℝ => ‖G r‖) volume t m := by
    apply hInt.norm.mono_set
    intro r hr
    have hr' : r ∈ Set.Icc t m := by
      simpa only [Set.uIcc_of_le htm] using hr
    have hr'' : r ∈ Set.Icc t T :=
      ⟨hr'.1, hr'.2.trans hmT⟩
    simpa only [Set.uIcc_of_le (htm.trans hmT)] using hr''
  have hSecond : IntervalIntegrable (fun r : ℝ => ‖G r‖) volume m T := by
    apply hInt.norm.mono_set
    intro r hr
    have hr' : r ∈ Set.Icc m T := by
      simpa only [Set.uIcc_of_le hmT] using hr
    have hr'' : r ∈ Set.Icc t T :=
      ⟨htm.trans hr'.1, hr'.2⟩
    simpa only [Set.uIcc_of_le (htm.trans hmT)] using hr''
  have hBefore :
      (∫ r in t..m, ‖G r‖ ∂volume) ≤
        (m - t) * E := by
    calc
      (∫ r in t..m, ‖G r‖ ∂volume) ≤
          (∫ _r in t..m, E ∂volume) :=
        intervalIntegral.integral_mono_on htm hFirst intervalIntegrable_const
          (fun r hr => hMax r hr)
      _ = (m - t) * E := by simp [mul_comm]
  have hAdjacent :=
    intervalIntegral.integral_add_adjacent_intervals hFirst hSecond
  calc
    (∫ r in t..T, ‖G r‖ ∂volume) =
        (∫ r in t..m, ‖G r‖ ∂volume) +
        (∫ r in m..T, ‖G r‖ ∂volume) := hAdjacent.symm
    _ ≤ (m - t) * E + (∫ r in m..T, ‖G r‖ ∂volume) :=
      add_le_add_left hBefore _

/-- Same-witness, three-channel terminal obstruction: actual terminal
Fourier highpass, attained half-terminal source envelope, or delayed
projected-source action after the halfway point. The original gauge,
minimal PDE windows, disjoint viscous charges, and radius escape remain. -/
theorem thirdFullPhysical_noH3Trace_prescribedGauge_halfTailThreeChannel244
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
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          δ (v k) * ((H (v k)) ^ 8 / 4)) ≤
            ∫ r in a..T, velocityH3DissipationAt u r) ∧
      Tendsto (fun k : ℕ =>
        ((N (v k) : ℝ) + 2) / H (v k)) atTop atTop ∧
      (∀ᶠ k : ℕ in atTop,
        let t := τ (v k)
        let m := (t + T) / 2
        let Q := (N (v k) : ℝ) + 2
        let F := h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
        let G := h3PathActualProjectedMomentumSource244 hH3
        (H (v k)) ^ 4 < 14 * Q ^ 4 *
          ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
        (H (v k)) ^ 4 < 28 * Q ^ 4 *
          (‖F‖ * ((m - t) *
            h3PathActualProjectedSourceWindowEnvelope244 hH3 t m)) ∨
        (H (v k)) ^ 4 < 28 * Q ^ 4 *
          (‖F‖ * (∫ r in m..T, ‖G r‖ ∂volume))) := by
  obtain ⟨U, τ, N, K, C, δ, v, hMono, hLimit,
      hWindows, hCharges, hEscape, hSplit, _hAmplitude⟩ :=
    thirdFullPhysical_noH3Trace_prescribedGauge_twoChannel244
      hH3 hClass b hb hNoTrace hDInt H hH
  let F : H3PhysicalRealFinVectorL2Hilbert →L[ℝ] H3SpectralVelocityState :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
  let G : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3
  have hG : IntervalIntegrable G volume b T :=
    h3Critical_projected_source_integrable_of_finite_dissipation
      hH3 hClass hDInt b hb
  have hAfter : ∀ᶠ k : ℕ in atTop, b < τ (v k) :=
    hLimit.eventually (isOpen_Ioi.mem_nhds hb.2)
  have hThree : ∀ᶠ k : ℕ in atTop,
      let t := τ (v k)
      let m := (t + T) / 2
      let Q := (N (v k) : ℝ) + 2
      let F := h3PhysicalRealFinVectorL2HilbertRawFourierRealContinuousLinearMap
      let G := h3PathActualProjectedMomentumSource244 hH3
      (H (v k)) ^ 4 < 14 * Q ^ 4 *
        ‖thirdFullSpectralVelocityHighRadialApply244 (v k) (F U)‖ ∨
      (H (v k)) ^ 4 < 28 * Q ^ 4 *
        (‖F‖ * ((m - t) *
          h3PathActualProjectedSourceWindowEnvelope244 hH3 t m)) ∨
      (H (v k)) ^ 4 < 28 * Q ^ 4 *
        (‖F‖ * (∫ r in m..T, ‖G r‖ ∂volume)) := by
    filter_upwards [hAfter] with k hk
    dsimp only
    let t : ℝ := τ (v k)
    let m : ℝ := (t + T) / 2
    let Q : ℝ := (N (v k) : ℝ) + 2
    let E : ℝ := h3PathActualProjectedSourceWindowEnvelope244 hH3 t m
    have hEnd : t < T := by
      rcases (hWindows k).1.1 with
        ⟨_, _, _, hδ, _, hEnd, _, _, _, _, _, _, _⟩
      linarith only [hδ, hEnd]
    have htm : t < m := by dsimp only [m]; linarith only [hEnd]
    have hmT : m < T := by dsimp only [m]; linarith only [hEnd]
    have ht0 : 0 < t := lt_trans hClass.terminal_start.1 (lt_trans hb.1 hk)
    have hInt : IntervalIntegrable G volume t T := by
      apply hG.mono_set
      intro r hr
      have hr' : r ∈ Set.Icc t T := by
        simpa only [Set.uIcc_of_le hEnd.le] using hr
      have hr'' : r ∈ Set.Icc b T :=
        ⟨le_trans hk.le hr'.1, hr'.2⟩
      simpa only [Set.uIcc_of_le hb.2.le] using hr''
    have hEnvelope (r : ℝ) (hr : r ∈ Set.Icc t m) : ‖G r‖ ≤ E := by
      exact h3Path_actualSourceWindowEnvelope_pointwise_le244
        hH3 ht0 htm hmT r hr
    have hSourceBound :
        (∫ r in t..T, ‖G r‖ ∂volume) ≤
          (m - t) * E + (∫ r in m..T, ‖G r‖ ∂volume) :=
      thirdFull_projectedSource_firstPiece_le_maxPlusTail244
        G t m T E htm.le hmT.le hInt hEnvelope
    rcases hSplit k with hCarrier | hSource
    · exact Or.inl hCarrier
    · right
      have hSource' :
          (H (v k)) ^ 4 < 14 * Q ^ 4 *
            (‖F‖ * (∫ r in t..T, ‖G r‖ ∂volume)) := by
        simpa only [F, G, Q, t] using hSource
      have hSub : ‖F‖ * (∫ r in t..T, ‖G r‖ ∂volume) ≤
          (‖F‖ * ((m - t) * E)) +
            (‖F‖ * (∫ r in m..T, ‖G r‖ ∂volume)) := by
        calc
          _ ≤ ‖F‖ * ((m - t) * E +
                (∫ r in m..T, ‖G r‖ ∂volume)) :=
            mul_le_mul_of_nonneg_left hSourceBound (norm_nonneg F)
          _ = _ := by ring
      have hFinal := thirdFull_quartic_sourceTail_twoPiece244
        ((H (v k)) ^ 4) Q
        (‖F‖ * (∫ r in t..T, ‖G r‖ ∂volume))
        (‖F‖ * ((m - t) * E))
        (‖F‖ * (∫ r in m..T, ‖G r‖ ∂volume))
        (by dsimp only [Q]; positivity) hSource' hSub
      simpa only [F, G, Q, t, m, E] using hFinal
  exact ⟨U, τ, N, K, C, δ, v, hMono, hLimit,
    hWindows, hCharges, hEscape, hThree⟩

end
end PrimeTensor.FirstMonomialTriad
