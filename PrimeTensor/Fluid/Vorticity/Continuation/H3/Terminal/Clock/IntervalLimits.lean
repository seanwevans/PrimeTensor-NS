import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Clock.Synchronized

/-! Named terminal-interval limits, with a compatibility equivalence and
transport along one common subsequence. -/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter
open scoped Topology

/-- Four normalized limits on the same three sequences. No witness is chosen here. -/
structure H3TerminalIntervalLimits (T : ℝ) (s τ σ : ℕ → ℝ) : Prop where
  elapsed : Tendsto (fun n : ℕ => (τ n - s n) / (T - s n)) atTop (𝓝 1)
  width : Tendsto (fun n : ℕ => (σ n - s n) / (T - s n)) atTop (𝓝 1)
  terminalGap : Tendsto (fun n : ℕ => (T - σ n) / (T - s n)) atTop (𝓝 0)
  sampleGap : Tendsto (fun n : ℕ => (σ n - τ n) / (T - s n)) atTop (𝓝 0)

/-- The named bundle has exactly the original conjunction's content. -/
theorem h3TerminalIntervalLimits_iff (T : ℝ) (s τ σ : ℕ → ℝ) :
    H3TerminalIntervalLimits T s τ σ ↔
    Tendsto (fun n : ℕ => (τ n - s n) / (T - s n)) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => (σ n - s n) / (T - s n)) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => (T - σ n) / (T - s n)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (σ n - τ n) / (T - s n)) atTop (𝓝 0) := by
  constructor
  · intro h
    exact ⟨h.elapsed, h.width, h.terminalGap, h.sampleGap⟩
  · rintro ⟨hElapsed, hWidth, hTerminalGap, hSampleGap⟩
    exact ⟨hElapsed, hWidth, hTerminalGap, hSampleGap⟩

/-- Restrict all four limits along the same cofinal sequence. -/
theorem H3TerminalIntervalLimits.comp
    {T : ℝ} {s τ σ : ℕ → ℝ}
    (h : H3TerminalIntervalLimits T s τ σ)
    {v : ℕ → ℕ} (hv : Tendsto v atTop atTop) :
    H3TerminalIntervalLimits T
      (fun n => s (v n)) (fun n => τ (v n)) (fun n => σ (v n)) := by
  exact ⟨h.elapsed.comp hv, h.width.comp hv,
    h.terminalGap.comp hv, h.sampleGap.comp hv⟩

/-- Clock collapse makes the elapsed interval fill the left terminal clock. -/
theorem h3Terminal_elapsedRatio_tendsto_one_of_clockRatio_zero
    (T : ℝ) (s τ : ℕ → ℝ)
    (hs : ∀ n : ℕ, s n < T)
    (hRatio : Tendsto (fun n : ℕ => (T - τ n) / (T - s n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (τ n - s n) / (T - s n)) atTop (𝓝 1) := by
  have hEq :
      (fun n : ℕ => (τ n - s n) / (T - s n)) =
        (fun n : ℕ => 1 - (T - τ n) / (T - s n)) := by
    funext n
    have hDen : T - s n ≠ 0 := ne_of_gt (sub_pos.mpr (hs n))
    field_simp [hDen] <;> ring
  rw [hEq]
  have hLimit :
      Tendsto (fun n : ℕ => (1 : ℝ) - (T - τ n) / (T - s n))
        atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hRatio
  simpa only [sub_zero] using hLimit

/-- The containing forward interval has the same normalized width. -/
theorem h3Terminal_intervalLimits_of_sampleClockRatio_zero
    (T : ℝ) (s τ σ : ℕ → ℝ)
    (hs : ∀ n : ℕ, s n < T)
    (hOrder : ∀ n : ℕ, τ n ≤ σ n)
    (hσ : ∀ n : ℕ, σ n < T)
    (hRatio : Tendsto (fun n : ℕ => (T - τ n) / (T - s n)) atTop (𝓝 0)) :
    H3TerminalIntervalLimits T s τ σ := by
  have hDen : ∀ n : ℕ, 0 < T - s n := fun n => sub_pos.mpr (hs n)
  have hUpper : ∀ n : ℕ,
      (T - σ n) / (T - s n) ≤ (T - τ n) / (T - s n) := by
    intro n
    apply (div_le_div_iff₀ (hDen n) (hDen n)).2
    exact mul_le_mul_of_nonneg_right (sub_le_sub_left (hOrder n) T) (hDen n).le
  have hSigmaZero :
      Tendsto (fun n : ℕ => (T - σ n) / (T - s n)) atTop (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro b hb
      exact Filter.Eventually.of_forall (fun n : ℕ =>
        lt_of_lt_of_le hb (div_nonneg (sub_pos.mpr (hσ n)).le (hDen n).le))
    · intro b hb
      filter_upwards [(tendsto_order.1 hRatio).2 b hb] with n hn
      exact lt_of_le_of_lt (hUpper n) hn
  have hElapsed := h3Terminal_elapsedRatio_tendsto_one_of_clockRatio_zero T s τ hs hRatio
  have hWidth := h3Terminal_elapsedRatio_tendsto_one_of_clockRatio_zero T s σ hs hSigmaZero
  have hRemaining :
      Tendsto (fun n : ℕ => (σ n - τ n) / (T - s n)) atTop (𝓝 0) := by
    have hEq :
        (fun n : ℕ => (σ n - τ n) / (T - s n)) =
          (fun n : ℕ => (σ n - s n) / (T - s n) - (τ n - s n) / (T - s n)) := by
      funext n
      ring
    rw [hEq]
    simpa only [sub_self] using hWidth.sub hElapsed
  exact ⟨hElapsed, hWidth, hSigmaZero, hRemaining⟩

end Euclidean
end Bridge
end PrimeTensor
