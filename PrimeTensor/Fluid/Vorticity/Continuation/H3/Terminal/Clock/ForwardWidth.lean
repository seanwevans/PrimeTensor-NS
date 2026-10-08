import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Clock.Geometry

/-!
# Rebase the radial witness to its actual forward width

Since `(sigma - s) / (T - s) -> 1`, normalized limits relative to the left
terminal clock transfer to the forward width `sigma - s`.
For every fixed `0 < c < 1`, the positive floor also transfers with coefficient
`sqrt c * C`. This does not assert that the exact coefficient `C` transfers.

The same radial witness retains all previous limits and bounds. The forcing
alternative preserves energy escape and the sampled normalized vanishing
hypotheses. Strict forward separation is explicit.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/-- Rebase a normalized limit through a width whose ratio tends to one. -/
theorem h3Terminal_ratio_tendsto_rebased_of_widthRatio_one
    (left width value : ℕ → ℝ) (L : ℝ)
    (hLeft : ∀ n : ℕ, left n ≠ 0)
    (hWidth : ∀ n : ℕ, width n ≠ 0)
    (hValue : Tendsto (fun n : ℕ => value n / left n) atTop (𝓝 L))
    (hWidthRatio : Tendsto (fun n : ℕ => width n / left n) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => value n / width n) atTop (𝓝 L) := by
  have hEq :
      (fun n : ℕ => value n / width n) =
        (fun n : ℕ => (value n / left n) / (width n / left n)) := by
    funext n
    field_simp [hLeft n, hWidth n] <;> ring
  rw [hEq]
  have hDiv := hValue.div hWidthRatio (by norm_num : (1 : ℝ) ≠ 0)
  have hPointwise :
      ((fun n : ℕ => value n / left n) / (fun n : ℕ => width n / left n)) =
        (fun n : ℕ => (value n / left n) / (width n / left n)) := by
    funext n
    simp only [Pi.div_apply]
  rw [hPointwise] at hDiv
  simpa only [div_one] using hDiv

/-- Any fixed coefficient loss is eventually available at an asymptotically equal width. -/
theorem h3Terminal_forwardWidth_floor_of_widthRatio_one
    (left width : ℕ → ℝ) (M : ℕ → ℝ≥0∞) (C : ℝ)
    (hLeft : ∀ n : ℕ, 0 < left n)
    (hLower : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal C ≤ ENNReal.ofReal (Real.sqrt (left n)) * M n)
    (hWidthRatio : Tendsto (fun n : ℕ => width n / left n) atTop (𝓝 1)) :
    ∀ c : ℝ, 0 < c → c < 1 →
      ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (Real.sqrt c * C) ≤
          ENNReal.ofReal (Real.sqrt (width n)) * M n := by
  intro c hc hcOne
  have hCompare : ∀ᶠ n : ℕ in atTop, c < width n / left n :=
    (tendsto_order.1 hWidthRatio).1 c hcOne
  filter_upwards [hLower, hCompare] with n hn hcn
  have hScale : c * left n ≤ width n := ((lt_div_iff₀ (hLeft n)).1 hcn).le
  exact h3Terminal_scaledFloor_of_clock_comparison hc hScale hn

/-- One witness carries both left-clock and forward-width geometry and floors. -/
def H3TerminalHigherRadialPositiveFloorAndForwardWidthGeometry
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
    Tendsto (fun n : ℕ => (σ (v n) - τ (v n)) / (T - s (v n))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (T - τ (v n)) / (σ (v n) - s (v n))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (τ (v n) - s (v n)) / (σ (v n) - s (v n))) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => (T - σ (v n)) / (σ (v n) - s (v n))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (σ (v n) - τ (v n)) / (σ (v n) - s (v n))) atTop (𝓝 0) ∧
    (∀ c : ℝ, 0 < c → c < 1 →
      ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (Real.sqrt c * C) ≤
          ENNReal.ofReal (Real.sqrt (σ (v n) - s (v n))) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass radialOrder (τ (v n)) (hτ (v n)))

/-- Rebase the existing selected radial witness without another extraction. -/
theorem h3TerminalHigherRadial_forwardWidthGeometry_of_terminalIntervalGeometry
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (s σ : ℕ → ℝ) (radialOrder : ℕ) (C : ℝ)
    (hs : ∀ n : ℕ, s n < T)
    (hForward : ∀ n : ℕ, s n < σ n)
    (hWitness : H3TerminalHigherRadialPositiveFloorAndTerminalIntervalGeometry
      hH3 hClass τ hτ s σ radialOrder C) :
    H3TerminalHigherRadialPositiveFloorAndForwardWidthGeometry
      hH3 hClass τ hτ s σ radialOrder C := by
  obtain ⟨hC, v, hMono, hTau, hLower, hNonzero, hHigher, hZero, hRatio,
    hElapsed, hWidth, hSigmaZero, hRemaining⟩ := hWitness
  have hLeftPos : ∀ n : ℕ, 0 < T - s (v n) :=
    fun n => sub_pos.mpr (hs (v n))
  have hLeftNe : ∀ n : ℕ, T - s (v n) ≠ 0 := fun n => ne_of_gt (hLeftPos n)
  have hWidthNe : ∀ n : ℕ, σ (v n) - s (v n) ≠ 0 :=
    fun n => ne_of_gt (sub_pos.mpr (hForward (v n)))
  have hSampleWidth :=
    h3Terminal_ratio_tendsto_rebased_of_widthRatio_one
      (fun n : ℕ => T - s (v n)) (fun n : ℕ => σ (v n) - s (v n))
      (fun n : ℕ => T - τ (v n)) 0 hLeftNe hWidthNe hRatio hWidth
  have hElapsedWidth :=
    h3Terminal_ratio_tendsto_rebased_of_widthRatio_one
      (fun n : ℕ => T - s (v n)) (fun n : ℕ => σ (v n) - s (v n))
      (fun n : ℕ => τ (v n) - s (v n)) 1 hLeftNe hWidthNe hElapsed hWidth
  have hSigmaWidth :=
    h3Terminal_ratio_tendsto_rebased_of_widthRatio_one
      (fun n : ℕ => T - s (v n)) (fun n : ℕ => σ (v n) - s (v n))
      (fun n : ℕ => T - σ (v n)) 0 hLeftNe hWidthNe hSigmaZero hWidth
  have hRemainingWidth :=
    h3Terminal_ratio_tendsto_rebased_of_widthRatio_one
      (fun n : ℕ => T - s (v n)) (fun n : ℕ => σ (v n) - s (v n))
      (fun n : ℕ => σ (v n) - τ (v n)) 0 hLeftNe hWidthNe hRemaining hWidth
  have hFloors :=
    h3Terminal_forwardWidth_floor_of_widthRatio_one
      (fun n : ℕ => T - s (v n)) (fun n : ℕ => σ (v n) - s (v n))
      (fun n : ℕ => h3TerminalPhysicalExtendedHigherRadialMomentAt
        hH3 hClass radialOrder (τ (v n)) (hτ (v n))) C hLeftPos hLower hWidth
  exact ⟨hC, v, hMono, hTau, hLower, hNonzero, hHigher, hZero, hRatio,
    hElapsed, hWidth, hSigmaZero, hRemaining,
    hSampleWidth, hElapsedWidth, hSigmaWidth, hRemainingWidth, hFloors⟩

/-- Energy escape or a radial witness with forward-width normalized geometry. -/
theorem resolvedCanonicalForcing_energy_or_forwardWidthGeometry
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (s σ : ℕ → ℝ) (δ : ℝ)
    (hs : ∀ n : ℕ, s n < T)
    (hForward : ∀ n : ℕ, s n < σ n)
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
      H3TerminalHigherRadialPositiveFloorAndForwardWidthGeometry
        hH3 hClass τ hτ s σ
        (h3TerminalForcingThirdQHigherRadialShift qRadial)
        (h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient δ qRadial)) ∨
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialPositiveFloorAndForwardWidthGeometry
        hH3 hClass τ hτ s σ
        (h3TerminalForcingFourthQHigherRadialShift qRadial)
        (h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient δ qRadial)) := by
  rcases resolvedCanonicalForcing_energy_or_terminalIntervalGeometry
      hH3 hClass τ hτ s σ δ hs hOrder hσ hBranch hSecondZero hFourthZero with
    hEnergy | hSecond | hFourth
  · exact Or.inl hEnergy
  · obtain ⟨qRadial, hWitness⟩ := hSecond
    exact Or.inr (Or.inl ⟨qRadial,
      h3TerminalHigherRadial_forwardWidthGeometry_of_terminalIntervalGeometry
        hH3 hClass τ hτ s σ _ _ hs hForward hWitness⟩)
  · obtain ⟨qRadial, hWitness⟩ := hFourth
    exact Or.inr (Or.inr ⟨qRadial,
      h3TerminalHigherRadial_forwardWidthGeometry_of_terminalIntervalGeometry
        hH3 hClass τ hτ s σ _ _ hs hForward hWitness⟩)

end

end Euclidean
end Bridge
end PrimeTensor
