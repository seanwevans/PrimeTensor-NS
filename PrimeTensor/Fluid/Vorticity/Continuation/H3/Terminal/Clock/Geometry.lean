import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Clock.IntervalLimits

/-!
# Terminal interval geometry on the synchronized radial witness

Clock collapse `(T - tau) / (T - s) -> 0` gives
`(tau - s) / (T - s) -> 1`.
If `tau <= sigma < T`, then also
`(sigma - s) / (T - s) -> 1`,
`(T - sigma) / (T - s) -> 0`, and
`(sigma - tau) / (T - s) -> 0`.

These limits are retained on the same radial witness as the positive floor
and divergent higher moment. The forcing alternative keeps energy escape;
sampling-clock normalized vanishing remains an explicit hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/-- The containing forward interval has the same normalized width. -/
theorem h3Terminal_intervalGeometry_of_sampleClockRatio_zero
    (T : ℝ) (s τ σ : ℕ → ℝ)
    (hs : ∀ n : ℕ, s n < T)
    (hOrder : ∀ n : ℕ, τ n ≤ σ n)
    (hσ : ∀ n : ℕ, σ n < T)
    (hRatio : Tendsto (fun n : ℕ => (T - τ n) / (T - s n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (τ n - s n) / (T - s n)) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => (σ n - s n) / (T - s n)) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => (T - σ n) / (T - s n)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (σ n - τ n) / (T - s n)) atTop (𝓝 0) := by
  exact (h3TerminalIntervalLimits_iff T s τ σ).1
    (h3Terminal_intervalLimits_of_sampleClockRatio_zero T s τ σ hs hOrder hσ hRatio)

/-- One radial witness retains its analytic bounds and terminal interval limits. -/
def H3TerminalHigherRadialPositiveFloorAndTerminalIntervalGeometry
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (s σ : ℕ → ℝ) (radialOrder : ℕ) (C : ℝ) : Prop :=
  0 < C ∧
  ∃ v : ℕ → ℕ,
    StrictMono v ∧
    Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T) ∧
    (∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal C ≤
        ENNReal.ofReal (Real.sqrt ((T - s (v n)))) *
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass radialOrder (τ (v n)) (hτ (v n))) ∧
    (¬ Tendsto
      (fun n : ℕ =>
        ENNReal.ofReal (Real.sqrt ((T - s (v n)))) *
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass radialOrder (τ (v n)) (hτ (v n)))
      atTop (𝓝 0)) ∧
    Tendsto
      (fun n : ℕ =>
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass radialOrder (τ (v n)) (hτ (v n)))
      atTop (𝓝 ∞) ∧
    Tendsto
      (fun n : ℕ =>
        ENNReal.ofReal (Real.sqrt (T - τ (v n))) *
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass radialOrder (τ (v n)) (hτ (v n)))
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (T - τ (v n)) / (T - s (v n))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (τ (v n) - s (v n)) / (T - s (v n))) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => (σ (v n) - s (v n)) / (T - s (v n))) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => (T - σ (v n)) / (T - s (v n))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (σ (v n) - τ (v n)) / (T - s (v n))) atTop (𝓝 0)

/-- Preserve the original radial subsequence while adding its interval geometry. -/
theorem h3TerminalHigherRadial_intervalGeometry_of_synchronized_collapse
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (s σ : ℕ → ℝ) (radialOrder : ℕ) (C : ℝ)
    (hs : ∀ n : ℕ, s n < T)
    (hOrder : ∀ n : ℕ, τ n ≤ σ n)
    (hσ : ∀ n : ℕ, σ n < T)
    (hWitness : H3TerminalHigherRadialPositiveFloorAndSampleClockCollapse
      hH3 hClass τ hτ (fun n : ℕ => T - s n) radialOrder C) :
    H3TerminalHigherRadialPositiveFloorAndTerminalIntervalGeometry
      hH3 hClass τ hτ s σ radialOrder C := by
  obtain ⟨hC, v, hMono, hTau, hLower, hNonzero, hHigher, hZero, hRatio⟩ := hWitness
  have hGeometry :=
    h3Terminal_intervalLimits_of_sampleClockRatio_zero T
      (fun n : ℕ => s (v n)) (fun n : ℕ => τ (v n)) (fun n : ℕ => σ (v n))
      (fun n : ℕ => hs (v n)) (fun n : ℕ => hOrder (v n)) (fun n : ℕ => hσ (v n))
      hRatio
  exact ⟨hC, v, hMono, hTau, hLower, hNonzero, hHigher, hZero, hRatio,
    hGeometry.elapsed, hGeometry.width, hGeometry.terminalGap, hGeometry.sampleGap⟩

/-- Under sampled normalized vanishing, retain energy escape or a radial witness
with the normalized terminal interval geometry. -/
theorem resolvedCanonicalForcing_energy_or_terminalIntervalGeometry
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (s σ : ℕ → ℝ) (δ : ℝ)
    (hs : ∀ n : ℕ, s n < T)
    (hOrder : ∀ n : ℕ, τ n ≤ σ n)
    (hσ : ∀ n : ℕ, σ n < T)
    (hBranch : H3TerminalResolvedCanonicalForcingSqrtWidthPositiveFloorBranch
      hH3 hClass τ hτ δ (fun n : ℕ => T - s n))
    (hSecondZero : ∀ qRadial : Fin 2,
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal (Real.sqrt (T - τ n)) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass (h3TerminalForcingThirdQHigherRadialShift qRadial)
              (τ n) (hτ n))
        atTop (𝓝 0))
    (hFourthZero : ∀ qRadial : Fin 2,
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal (Real.sqrt (T - τ n)) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass (h3TerminalForcingFourthQHigherRadialShift qRadial)
              (τ n) (hτ n))
        atTop (𝓝 0)) :
    (∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ (v n))) atTop atTop) ∨
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialPositiveFloorAndTerminalIntervalGeometry
        hH3 hClass τ hτ s σ
        (h3TerminalForcingThirdQHigherRadialShift qRadial)
        (h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient δ qRadial)) ∨
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialPositiveFloorAndTerminalIntervalGeometry
        hH3 hClass τ hτ s σ
        (h3TerminalForcingFourthQHigherRadialShift qRadial)
        (h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient δ qRadial)) := by
  rcases resolvedCanonicalForcing_energy_or_synchronized_sampleClock_collapse
      hH3 hClass τ hτ (fun n : ℕ => T - s n) δ
      (fun n : ℕ => sub_pos.mpr (hs n)) hBranch hSecondZero hFourthZero with
    hEnergy | hSecond | hFourth
  · exact Or.inl hEnergy
  · obtain ⟨qRadial, hWitness⟩ := hSecond
    exact Or.inr (Or.inl ⟨qRadial,
      h3TerminalHigherRadial_intervalGeometry_of_synchronized_collapse
        hH3 hClass τ hτ s σ _ _ hs hOrder hσ hWitness⟩)
  · obtain ⟨qRadial, hWitness⟩ := hFourth
    exact Or.inr (Or.inr ⟨qRadial,
      h3TerminalHigherRadial_intervalGeometry_of_synchronized_collapse
        hH3 hClass τ hτ s σ _ _ hs hOrder hσ hWitness⟩)

end

end Euclidean
end Bridge
end PrimeTensor
