import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalCancellationRelativeCluster

/-!
# Quantitative actual-versus-spectral H3 budget rates on the direct clock

The exact positive-excess cancellation budget is

  Delta(t) + q0(t) = 4422 + S(t),

where `Delta` is nonnegative commutator cancellation slack, `q0` is actual
positive normalized transport growth after both copies of dissipation, and
`S` is the baseline-free commutator/dissipation shortfall.

The previously obtained compact cluster fixes the limiting cancellation share
`theta` while retaining a physical-time subsequence on which both `q0` and
`S` diverge. This file upgrades the share limits to strict quantitative
comparisons against the actual spectral budget:

* when `theta < 1`, actual growth eventually exceeds every positive fraction
  strictly below `1 - theta` of the spectral budget;
* when `theta = 1`, actual growth is eventually below every positive fraction
  of that budget, although actual growth still diverges absolutely.

Neither branch is excluded. These statements are necessary conditions on the
hypothetical nonextension branch, not new nonlinear PDE inequalities.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- A strict lower bound on the actual-growth share gives a strict lower
bound on the actual growth relative to the **exact** spectral budget. -/
theorem h3PathCanonical_actualExcess_gt_fraction_spectralBudget
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t η : ℝ)
    (hCancel : 0 ≤ h3PathCanonicalTransportCancellationGap u t)
    (hActual : 0 < h3PathCanonicalMarginExcessRate u 0 t)
    (hShare : η < h3PathCanonicalActualGrowthBudgetShare u t) :
    η * (4422 + h3PathCanonicalNonlinearDissipationShortfall u t) <
      h3PathCanonicalMarginExcessRate u 0 t := by
  have hDen : 0 < h3PathCanonicalTransportCancellationGap u t +
      h3PathCanonicalMarginExcessRate u 0 t := by
    linarith only [hCancel, hActual]
  have hScaled : η * (h3PathCanonicalTransportCancellationGap u t +
      h3PathCanonicalMarginExcessRate u 0 t) <
      h3PathCanonicalMarginExcessRate u 0 t := by
    exact (lt_div_iff₀ hDen).1
      (show η < h3PathCanonicalMarginExcessRate u 0 t /
        (h3PathCanonicalTransportCancellationGap u t +
          h3PathCanonicalMarginExcessRate u 0 t) by
        simpa only [h3PathCanonicalActualGrowthBudgetShare] using hShare)
  rw [h3PathCanonical_cancellationBudget_denominator_eq_spectral
    u t hActual] at hScaled
  exact hScaled

/-- A strict upper bound on the actual-growth share gives the corresponding
strict upper bound on the actual growth relative to the spectral budget. -/
theorem h3PathCanonical_actualExcess_lt_fraction_spectralBudget
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t η : ℝ)
    (hCancel : 0 ≤ h3PathCanonicalTransportCancellationGap u t)
    (hActual : 0 < h3PathCanonicalMarginExcessRate u 0 t)
    (hShare : h3PathCanonicalActualGrowthBudgetShare u t < η) :
    h3PathCanonicalMarginExcessRate u 0 t <
      η * (4422 + h3PathCanonicalNonlinearDissipationShortfall u t) := by
  have hDen : 0 < h3PathCanonicalTransportCancellationGap u t +
      h3PathCanonicalMarginExcessRate u 0 t := by
    linarith only [hCancel, hActual]
  have hScaled : h3PathCanonicalMarginExcessRate u 0 t <
      η * (h3PathCanonicalTransportCancellationGap u t +
        h3PathCanonicalMarginExcessRate u 0 t) := by
    exact (div_lt_iff₀ hDen).1
      (show h3PathCanonicalMarginExcessRate u 0 t /
        (h3PathCanonicalTransportCancellationGap u t +
          h3PathCanonicalMarginExcessRate u 0 t) < η by
        simpa only [h3PathCanonicalActualGrowthBudgetShare] using hShare)
  rw [h3PathCanonical_cancellationBudget_denominator_eq_spectral
    u t hActual] at hScaled
  exact hScaled

/-- Every fraction strictly below the positive limiting actual-growth share
is eventually retained by the *actual* PDE transport excess. -/
theorem h3PathCanonical_actualExcess_eventually_gt_spectral_fraction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {τ : ℕ → ℝ} {θ : ℝ}
    (hActual : ∀ n : ℕ, 0 < h3PathCanonicalMarginExcessRate u 0 (τ n))
    (hCancel : ∀ n : ℕ, 0 ≤ h3PathCanonicalTransportCancellationGap u (τ n))
    (hGrowth : Tendsto (fun n : ℕ =>
      h3PathCanonicalActualGrowthBudgetShare u (τ n)) atTop (𝓝 (1 - θ)))
    (η : ℝ) (hη : η < 1 - θ) :
    ∀ᶠ n : ℕ in atTop,
      η * (4422 + h3PathCanonicalNonlinearDissipationShortfall u (τ n)) <
        h3PathCanonicalMarginExcessRate u 0 (τ n) := by
  have hShare : ∀ᶠ n : ℕ in atTop,
      η < h3PathCanonicalActualGrowthBudgetShare u (τ n) :=
    (tendsto_order.1 hGrowth).1 η hη
  filter_upwards [hShare] with n hn
  exact h3PathCanonical_actualExcess_gt_fraction_spectralBudget
    u (τ n) η (hCancel n) (hActual n) hn

/-- At the full-cancellation-fraction cluster, actual growth is relatively
small compared with the spectral budget for every prescribed positive rate.
This does not imply that the actual excess is bounded. -/
theorem h3PathCanonical_actualExcess_eventually_lt_spectral_fraction_of_share_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {τ : ℕ → ℝ} {θ : ℝ}
    (hθ : θ = 1)
    (hActual : ∀ n : ℕ, 0 < h3PathCanonicalMarginExcessRate u 0 (τ n))
    (hCancel : ∀ n : ℕ, 0 ≤ h3PathCanonicalTransportCancellationGap u (τ n))
    (hGrowth : Tendsto (fun n : ℕ =>
      h3PathCanonicalActualGrowthBudgetShare u (τ n)) atTop (𝓝 (1 - θ)))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalMarginExcessRate u 0 (τ n) <
        η * (4422 + h3PathCanonicalNonlinearDissipationShortfall u (τ n)) := by
  have hBelow : 1 - θ < η := by
    rw [hθ]
    linarith only [hη]
  have hShare : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalActualGrowthBudgetShare u (τ n) < η :=
    (tendsto_order.1 hGrowth).2 η hBelow
  filter_upwards [hShare] with n hn
  exact h3PathCanonical_actualExcess_lt_fraction_spectralBudget
    u (τ n) η (hCancel n) (hActual n) hn

/-- The nonextension physical-clock witnesses have an exhaustive and
quantitative transport/spectral comparison along a single cofinal subsequence.
The actual excess and the spectral shortfall diverge on **both** branches. -/
theorem h3PathCanonical_exists_direct_actualSpectral_fraction_regime
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
      ((θ = 1 ∧ ∀ η : ℝ, 0 < η →
          ∀ᶠ n : ℕ in atTop,
            h3PathCanonicalMarginExcessRate u 0 (σ (k n)) <
              η * (4422 + h3PathCanonicalNonlinearDissipationShortfall
                u (σ (k n)))) ∨
        (θ < 1 ∧ ∀ η : ℝ, 0 < η → η < 1 - θ →
          ∀ᶠ n : ℕ in atTop,
            η * (4422 + h3PathCanonicalNonlinearDissipationShortfall
              u (σ (k n))) <
                h3PathCanonicalMarginExcessRate u 0 (σ (k n)))) := by
  obtain ⟨σ, k, θ, hkMono, hθ, hSamples, hClock, hActualTop,
    hSpectralTop, _hShareTop, hGrowthTop⟩ :=
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
      intro η hη
      exact h3PathCanonical_actualExcess_eventually_lt_spectral_fraction_of_share_one
        hOne hActualPos hCancelNonneg hGrowthTop η hη
    · right
      have hBelow : θ < 1 := lt_of_le_of_ne hθ.2 hOne
      refine ⟨hBelow, ?_⟩
      intro η _hη hηBelow
      exact h3PathCanonical_actualExcess_eventually_gt_spectral_fraction
        hActualPos hCancelNonneg hGrowthTop η hηBelow

/-- Neutral terminal alternative preserving the quantitative relative
actual/spectral fraction regime on one direct terminal subsequence. -/
theorem h3PathCanonical_extension_or_direct_actualSpectral_fraction_regime
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
        ((θ = 1 ∧ ∀ η : ℝ, 0 < η →
            ∀ᶠ n : ℕ in atTop,
              h3PathCanonicalMarginExcessRate u 0 (σ (k n)) <
                η * (4422 + h3PathCanonicalNonlinearDissipationShortfall
                  u (σ (k n)))) ∨
          (θ < 1 ∧ ∀ η : ℝ, 0 < η → η < 1 - θ →
            ∀ᶠ n : ℕ in atTop,
              η * (4422 + h3PathCanonicalNonlinearDissipationShortfall
                u (σ (k n))) <
                  h3PathCanonicalMarginExcessRate u 0 (σ (k n)))) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro b hMass
    obtain ⟨σ, k, θ, hkMono, hθ, _hDirect, hClock,
      hActualTop, hSpectralTop, hRegime⟩ :=
      h3PathCanonical_exists_direct_actualSpectral_fraction_regime
        hH3 hExt hClass hMass
    exact ⟨σ, k, θ, hkMono, hθ, hClock,
      hActualTop, hSpectralTop, hRegime⟩

end Euclidean
end Bridge
end PrimeTensor
