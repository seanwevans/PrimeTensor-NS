import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalCancellationShareCluster

/-!
# Relative cancellation and actual transport-growth rates on a direct terminal clock

On the positive full-dissipation transport excess branch, the normalized
cancellation share and actual-growth share partition the same positive budget.
The previous compactness theorem supplies a physical terminal-clock subsequence
with share limits `theta` and `1 - theta`, while both the unnormalized actual
excess and the spectral shortfall tend to `+infinity`.

This module sharpens the asymptotic classification without asserting any
transport estimate: when `theta < 1`, the ratio of cancellation slack to actual
excess has a finite limit `theta/(1-theta)`; when `theta = 1`, the reciprocal
ratio of actual excess to cancellation slack tends to zero. The latter case
still permits absolute actual excess to diverge.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- The relative cancellation-to-growth quotient is exactly the ratio of
their shares whenever actual normalized excess is positive. -/
theorem h3PathCanonical_cancellationToGrowth_eq_shareRatio
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (hCancel : 0 ≤ h3PathCanonicalTransportCancellationGap u t)
    (hActual : 0 < h3PathCanonicalMarginExcessRate u 0 t) :
    h3PathCanonicalTransportCancellationGap u t /
      h3PathCanonicalMarginExcessRate u 0 t =
    h3PathCanonicalCancellationBudgetShare u t /
      h3PathCanonicalActualGrowthBudgetShare u t := by
  have hDen : 0 < h3PathCanonicalTransportCancellationGap u t +
      h3PathCanonicalMarginExcessRate u 0 t := by
    linarith only [hCancel, hActual]
  unfold h3PathCanonicalCancellationBudgetShare
    h3PathCanonicalActualGrowthBudgetShare
  field_simp [ne_of_gt hActual, ne_of_gt hDen]
  <;> ring

/-- The reverse quotient is the reverse ratio of shares when both budget
components are strictly positive. -/
theorem h3PathCanonical_growthToCancellation_eq_shareRatio
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ)
    (hCancel : 0 < h3PathCanonicalTransportCancellationGap u t)
    (hActual : 0 < h3PathCanonicalMarginExcessRate u 0 t) :
    h3PathCanonicalMarginExcessRate u 0 t /
      h3PathCanonicalTransportCancellationGap u t =
    h3PathCanonicalActualGrowthBudgetShare u t /
      h3PathCanonicalCancellationBudgetShare u t := by
  have hDen : 0 < h3PathCanonicalTransportCancellationGap u t +
      h3PathCanonicalMarginExcessRate u 0 t := by
    linarith only [hCancel, hActual]
  unfold h3PathCanonicalCancellationBudgetShare
    h3PathCanonicalActualGrowthBudgetShare
  field_simp [ne_of_gt hCancel, ne_of_gt hDen]
  <;> ring

/-- A cancellation-share cluster strictly below one forces a finite relative
cancellation-to-actual-growth ratio, even though both original energy-scale
quantities may diverge. -/
theorem h3PathCanonical_cancellationToGrowth_tendsto_of_shareLimit_lt_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {τ : ℕ → ℝ} {θ : ℝ}
    (hθ : θ < 1)
    (hActual : ∀ n : ℕ, 0 < h3PathCanonicalMarginExcessRate u 0 (τ n))
    (hCancel : ∀ n : ℕ, 0 ≤ h3PathCanonicalTransportCancellationGap u (τ n))
    (hShare : Tendsto (fun n : ℕ =>
      h3PathCanonicalCancellationBudgetShare u (τ n)) atTop (𝓝 θ))
    (hGrowth : Tendsto (fun n : ℕ =>
      h3PathCanonicalActualGrowthBudgetShare u (τ n)) atTop (𝓝 (1 - θ))) :
    Tendsto (fun n : ℕ =>
      h3PathCanonicalTransportCancellationGap u (τ n) /
        h3PathCanonicalMarginExcessRate u 0 (τ n))
      atTop (𝓝 (θ / (1 - θ))) := by
  have hDen : (1 - θ : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hLimit := hShare.div hGrowth hDen
  apply hLimit.congr'
  filter_upwards [] with n
  exact (h3PathCanonical_cancellationToGrowth_eq_shareRatio
    u (τ n) (hCancel n) (hActual n)).symm

/-- A positive limiting cancellation share eventually has positive absolute
cancellation slack, permitting a reciprocal-growth quotient. -/
theorem h3PathCanonical_growthToCancellation_tendsto_of_positive_shareLimit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {τ : ℕ → ℝ} {θ : ℝ}
    (hθ : 0 < θ)
    (hActual : ∀ n : ℕ, 0 < h3PathCanonicalMarginExcessRate u 0 (τ n))
    (hCancel : ∀ n : ℕ, 0 ≤ h3PathCanonicalTransportCancellationGap u (τ n))
    (hShare : Tendsto (fun n : ℕ =>
      h3PathCanonicalCancellationBudgetShare u (τ n)) atTop (𝓝 θ))
    (hGrowth : Tendsto (fun n : ℕ =>
      h3PathCanonicalActualGrowthBudgetShare u (τ n)) atTop (𝓝 (1 - θ))) :
    Tendsto (fun n : ℕ =>
      h3PathCanonicalMarginExcessRate u 0 (τ n) /
        h3PathCanonicalTransportCancellationGap u (τ n))
      atTop (𝓝 ((1 - θ) / θ)) := by
  have hSharePos : ∀ᶠ n : ℕ in atTop,
      0 < h3PathCanonicalCancellationBudgetShare u (τ n) :=
    (tendsto_order.1 hShare).1 0 hθ
  have hLimit := hGrowth.div hShare (ne_of_gt hθ)
  apply hLimit.congr'
  filter_upwards [hSharePos] with n hn
  have hCancelPos : 0 < h3PathCanonicalTransportCancellationGap u (τ n) := by
    by_contra hNot
    have hZero : h3PathCanonicalTransportCancellationGap u (τ n) = 0 :=
      le_antisymm (le_of_not_gt hNot) (hCancel n)
    have hShareZero : h3PathCanonicalCancellationBudgetShare u (τ n) = 0 := by
      simp [h3PathCanonicalCancellationBudgetShare, hZero]
    linarith only [hn, hShareZero]
  exact (h3PathCanonical_growthToCancellation_eq_shareRatio
    u (τ n) hCancelPos (hActual n)).symm

/-- A precise neutral two-regime cluster of relative *actual* and cancellation
rates. On both branches actual excess and spectral shortfall still diverge.
The endpoint `theta = 1` is relative dominance, not bounded actual growth. -/
theorem h3PathCanonical_exists_direct_cancellationRelative_cluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ∃ σ : ℕ → ℝ, ∃ k : ℕ → ℕ, ∃ θ : ℝ,
      StrictMono k ∧ θ ∈ Set.Icc (0 : ℝ) 1 ∧
      (∀ n : ℕ,
        h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ n) =
            h3PathCanonicalKineticTransportCoefficient u (σ n) ∧
        h3ExactAdaptiveSelectedAbsorbedCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ n) = 0) ∧
      Tendsto (fun n : ℕ => σ (k n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalMarginExcessRate u 0 (σ (k n))) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalNonlinearDissipationShortfall u (σ (k n))) atTop atTop ∧
      ((θ = 1 ∧ Tendsto (fun n : ℕ =>
          h3PathCanonicalMarginExcessRate u 0 (σ (k n)) /
            h3PathCanonicalTransportCancellationGap u (σ (k n)))
            atTop (𝓝 0)) ∨
        (θ < 1 ∧ Tendsto (fun n : ℕ =>
          h3PathCanonicalTransportCancellationGap u (σ (k n)) /
            h3PathCanonicalMarginExcessRate u 0 (σ (k n)))
            atTop (𝓝 (θ / (1 - θ))))) := by
  obtain ⟨σ, k, θ, hkMono, hθ, hSamples, hClock, hActualTop,
    hSpectralTop, hShareTop, hGrowthTop⟩ :=
    h3PathCanonical_exists_direct_cancellationShare_cluster
      hH3 hNoExtension hClass hMass
  have hActualPos : ∀ n : ℕ,
      0 < h3PathCanonicalMarginExcessRate u 0 (σ (k n)) := by
    intro n
    obtain ⟨_, _, _, _, hActual, _, _⟩ := hSamples (k n)
    exact lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ (k n : ℝ)) hActual
  have hCancelNonneg : ∀ n : ℕ,
      0 ≤ h3PathCanonicalTransportCancellationGap u (σ (k n)) := by
    intro n
    obtain ⟨_, _, _, _, _, _, hCancel⟩ := hSamples (k n)
    exact hCancel
  refine ⟨σ, k, θ, hkMono, hθ, ?_, hClock, hActualTop,
    hSpectralTop, ?_⟩
  · intro n
    obtain ⟨_, _, hDirect, hAbsorbed, _, _, _⟩ := hSamples n
    exact ⟨hDirect, hAbsorbed⟩
  · by_cases hOne : θ = 1
    · left
      refine ⟨hOne, ?_⟩
      have hθPos : 0 < θ := by rw [hOne]; norm_num
      have hLimit :=
        h3PathCanonical_growthToCancellation_tendsto_of_positive_shareLimit
          hθPos hActualPos hCancelNonneg hShareTop hGrowthTop
      simpa only [hOne, sub_self, zero_div] using hLimit
    · right
      have hBelow : θ < 1 := lt_of_le_of_ne hθ.2 hOne
      exact ⟨hBelow,
        h3PathCanonical_cancellationToGrowth_tendsto_of_shareLimit_lt_one
          hBelow hActualPos hCancelNonneg hShareTop hGrowthTop⟩

/-- Exhaustive nonextension-relative-rate alternative, with the prior direct
terminal-clock witness retained on the nonextension branch. -/
theorem h3PathCanonical_extension_or_direct_cancellationRelative_cluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, 0 < velocityH3Energy0At u b →
      ∃ σ : ℕ → ℝ, ∃ k : ℕ → ℕ, ∃ θ : ℝ,
        StrictMono k ∧ θ ∈ Set.Icc (0 : ℝ) 1 ∧
        Tendsto (fun n : ℕ => σ (k n)) atTop (𝓝 T) ∧
        Tendsto (fun n : ℕ =>
          h3PathCanonicalMarginExcessRate u 0 (σ (k n))) atTop atTop ∧
        Tendsto (fun n : ℕ =>
          h3PathCanonicalNonlinearDissipationShortfall u (σ (k n))) atTop atTop ∧
        ((θ = 1 ∧ Tendsto (fun n : ℕ =>
            h3PathCanonicalMarginExcessRate u 0 (σ (k n)) /
              h3PathCanonicalTransportCancellationGap u (σ (k n)))
              atTop (𝓝 0)) ∨
          (θ < 1 ∧ Tendsto (fun n : ℕ =>
            h3PathCanonicalTransportCancellationGap u (σ (k n)) /
              h3PathCanonicalMarginExcessRate u 0 (σ (k n)))
              atTop (𝓝 (θ / (1 - θ))))) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro b hMass
    obtain ⟨σ, k, θ, hkMono, hθ, _hDirect, hClock,
      hActualTop, hSpectralTop, hRegime⟩ :=
      h3PathCanonical_exists_direct_cancellationRelative_cluster
        hH3 hExt hClass hMass
    exact ⟨σ, k, θ, hkMono, hθ, hClock,
      hActualTop, hSpectralTop, hRegime⟩

end Euclidean
end Bridge
end PrimeTensor
