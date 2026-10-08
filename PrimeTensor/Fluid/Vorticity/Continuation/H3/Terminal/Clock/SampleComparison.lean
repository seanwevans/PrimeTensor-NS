import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Clock.PhysicalClock

/-!
# Transfer a physical left-clock floor to the sampling clock

If `c * left ≤ right` eventually for a fixed `c > 0`, a selected positive
`sqrt left * moment` floor `C` transfers to the floor `sqrt c * C` for
`sqrt right * moment`, on the same radial subsequence.

Specializing to `left n = T - s n` and `right n = T - tau n` isolates the
additional clock comparison required to reach the actual sampling time.
The comparison is a hypothesis, not a consequence of interval ordering.

When both sampling-clock normalized radial families vanish and energy escape
is excluded, every eventual positive comparison fails. This records a remaining
clock obstruction without asserting a new PDE estimate or a collapse rate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/-- Transfer a selected floor through eventual positive clock comparability. -/
theorem h3TerminalHigherRadialSqrtWidthPositiveFloor_of_eventual_clock_comparison
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (left right : ℕ → ℝ)
    (radialOrder : ℕ) (C c : ℝ)
    (hc : 0 < c)
    (hCompare : ∀ᶠ n : ℕ in atTop, c * left n ≤ right n)
    (hFloor : H3TerminalHigherRadialSqrtWidthPositiveFloor
      hH3 hClass τ hτ left radialOrder C) :
    H3TerminalHigherRadialSqrtWidthPositiveFloor
      hH3 hClass τ hτ right radialOrder (Real.sqrt c * C) := by
  obtain ⟨hC, v, hMono, hTau, hLower, _hNonzero, hHigher⟩ := hFloor
  have hNewC : 0 < Real.sqrt c * C := mul_pos (Real.sqrt_pos.2 hc) hC
  have hNewLower :
      ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (Real.sqrt c * C) ≤
          ENNReal.ofReal (Real.sqrt (right (v n))) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass radialOrder (τ (v n)) (hτ (v n)) := by
    filter_upwards [hLower, hMono.tendsto_atTop.eventually hCompare] with n hn hComp
    have hSqrt :
        Real.sqrt c * Real.sqrt (left (v n)) ≤ Real.sqrt (right (v n)) := by
      rw [← Real.sqrt_mul hc.le]
      exact Real.sqrt_le_sqrt hComp
    have hScale :
        ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal (Real.sqrt (left (v n))) ≤
          ENNReal.ofReal (Real.sqrt (right (v n))) := by
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
      exact ENNReal.ofReal_le_ofReal hSqrt
    calc
      ENNReal.ofReal (Real.sqrt c * C) =
          ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal C :=
        ENNReal.ofReal_mul (Real.sqrt_nonneg c)
      _ ≤ ENNReal.ofReal (Real.sqrt c) *
          (ENNReal.ofReal (Real.sqrt (left (v n))) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass radialOrder (τ (v n)) (hτ (v n))) := by
        gcongr 1 <;> exact hn
      _ = (ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal (Real.sqrt (left (v n)))) *
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass radialOrder (τ (v n)) (hτ (v n)) := by
        rw [mul_assoc]
      _ ≤ ENNReal.ofReal (Real.sqrt (right (v n))) *
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass radialOrder (τ (v n)) (hτ (v n)) := by
        gcongr 1 <;> exact hScale
  exact ⟨hNewC, v, hMono, hTau, hNewLower,
    h3Terminal_not_tendsto_zero_of_eventually_ofReal_pos_le hNewC hNewLower,
    hHigher⟩

/-- Energy escape or a quantitative floor at the actual sampling clock. -/
theorem resolvedCanonicalForcing_energy_or_sampleClockPositiveFloor_of_comparison
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (s : ℕ → ℝ) (δ c : ℝ)
    (hc : 0 < c)
    (hCompare : ∀ᶠ n : ℕ in atTop, c * (T - s n) ≤ T - τ n)
    (hBranch : H3TerminalResolvedCanonicalForcingSqrtWidthPositiveFloorBranch
      hH3 hClass τ hτ δ (fun n : ℕ => T - s n)) :
    (∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ (v n))) atTop atTop) ∨
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialSqrtWidthPositiveFloor
        hH3 hClass τ hτ (fun n : ℕ => T - τ n)
        (h3TerminalForcingThirdQHigherRadialShift qRadial)
        (Real.sqrt c * h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient δ qRadial)) ∨
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialSqrtWidthPositiveFloor
        hH3 hClass τ hτ (fun n : ℕ => T - τ n)
        (h3TerminalForcingFourthQHigherRadialShift qRadial)
        (Real.sqrt c * h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient δ qRadial)) := by
  rcases hBranch with hEnergy | hSecond | hFourth
  · exact Or.inl hEnergy
  · obtain ⟨qRadial, hFloor⟩ := hSecond
    exact Or.inr (Or.inl ⟨qRadial,
      h3TerminalHigherRadialSqrtWidthPositiveFloor_of_eventual_clock_comparison
        hH3 hClass τ hτ (fun n : ℕ => T - s n) (fun n : ℕ => T - τ n)
        _ _ c hc hCompare hFloor⟩)
  · obtain ⟨qRadial, hFloor⟩ := hFourth
    exact Or.inr (Or.inr ⟨qRadial,
      h3TerminalHigherRadialSqrtWidthPositiveFloor_of_eventual_clock_comparison
        hH3 hClass τ hτ (fun n : ℕ => T - s n) (fun n : ℕ => T - τ n)
        _ _ c hc hCompare hFloor⟩)

/-- Comparable clocks and vanishing sampled normalized moments select energy escape. -/
theorem resolvedCanonicalForcing_energyEscape_of_sampleClock_comparison_and_vanishing
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (s : ℕ → ℝ) (δ c : ℝ)
    (hc : 0 < c)
    (hCompare : ∀ᶠ n : ℕ in atTop, c * (T - s n) ≤ T - τ n)
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
    ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ (v n))) atTop atTop := by
  rcases resolvedCanonicalForcing_energy_or_sampleClockPositiveFloor_of_comparison
      hH3 hClass τ hτ s δ c hc hCompare hBranch with
    hEnergy | hSecond | hFourth
  · exact hEnergy
  · obtain ⟨qRadial, _hC, v, hMono, _hTau, _hLower, hNonzero, _hHigher⟩ := hSecond
    exact False.elim (hNonzero ((hSecondZero qRadial).comp hMono.tendsto_atTop))
  · obtain ⟨qRadial, _hC, v, hMono, _hTau, _hLower, hNonzero, _hHigher⟩ := hFourth
    exact False.elim (hNonzero ((hFourthZero qRadial).comp hMono.tendsto_atTop))

/-- With energy excluded and sampled normalized moments vanishing, every eventual
positive comparison of the left clock to the sample clock fails. -/
theorem resolvedCanonicalForcing_no_eventual_sampleClock_comparison_of_vanishing
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (s : ℕ → ℝ) (δ : ℝ)
    (hBranch : H3TerminalResolvedCanonicalForcingSqrtWidthPositiveFloorBranch
      hH3 hClass τ hτ δ (fun n : ℕ => T - s n))
    (hNoEnergy : ¬ (∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ (v n))) atTop atTop))
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
    ¬ ∃ c : ℝ, 0 < c ∧
      (∀ᶠ n : ℕ in atTop, c * (T - s n) ≤ T - τ n) := by
  rintro ⟨c, hc, hCompare⟩
  apply hNoEnergy
  exact resolvedCanonicalForcing_energyEscape_of_sampleClock_comparison_and_vanishing
    hH3 hClass τ hτ s δ c hc hCompare hBranch hSecondZero hFourthZero

/-- Under the same conditional hypotheses, the sample clock is frequently
smaller than every fixed positive fraction of the left clock. -/
theorem resolvedCanonicalForcing_frequently_small_sampleClock_of_vanishing
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (s : ℕ → ℝ) (δ : ℝ)
    (hBranch : H3TerminalResolvedCanonicalForcingSqrtWidthPositiveFloorBranch
      hH3 hClass τ hτ δ (fun n : ℕ => T - s n))
    (hNoEnergy : ¬ (∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ (v n))) atTop atTop))
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
    ∀ c : ℝ, 0 < c →
      ∃ᶠ n : ℕ in atTop, T - τ n < c * (T - s n) := by
  have hNoCompare :=
    resolvedCanonicalForcing_no_eventual_sampleClock_comparison_of_vanishing
      hH3 hClass τ hτ s δ hBranch hNoEnergy hSecondZero hFourthZero
  intro c hc
  change ¬ (∀ᶠ n : ℕ in atTop, ¬ (T - τ n < c * (T - s n)))
  intro hNotSmall
  apply hNoCompare
  refine ⟨c, hc, ?_⟩
  filter_upwards [hNotSmall] with n hn
  exact le_of_not_gt hn


end

end Euclidean
end Bridge
end PrimeTensor
