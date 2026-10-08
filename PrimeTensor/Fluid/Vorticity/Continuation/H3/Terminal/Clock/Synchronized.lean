import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Clock.SampleCollapse

/-!
# Synchronize clock collapse with the positive radial floor

A positive normalized left-clock floor and vanishing sampled-clock normalized
moments force the sample/left clock ratio to zero on that same sequence.
This argument retains the full selected radial witness: its positive floor,
terminal convergence, and higher-moment divergence.

Applied to the forcing branch, sampled normalized vanishing yields an energy
alternative or a radial floor with synchronized clock collapse. Energy escape
is retained as an explicit alternative. No new PDE vanishing estimate is proved.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/-- Pointwise positive clock comparison transfers the normalized lower bound. -/
theorem h3Terminal_scaledFloor_of_clock_comparison
    {left sample c C : ℝ} {M : ℝ≥0∞}
    (hc : 0 < c)
    (hCompare : c * left ≤ sample)
    (hFloor : ENNReal.ofReal C ≤ ENNReal.ofReal (Real.sqrt left) * M) :
    ENNReal.ofReal (Real.sqrt c * C) ≤ ENNReal.ofReal (Real.sqrt sample) * M := by
  have hSqrt : Real.sqrt c * Real.sqrt left ≤ Real.sqrt sample := by
    rw [← Real.sqrt_mul hc.le]
    exact Real.sqrt_le_sqrt hCompare
  have hScale :
      ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal (Real.sqrt left) ≤
        ENNReal.ofReal (Real.sqrt sample) := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
    exact ENNReal.ofReal_le_ofReal hSqrt
  calc
    ENNReal.ofReal (Real.sqrt c * C) =
        ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal C :=
      ENNReal.ofReal_mul (Real.sqrt_nonneg c)
    _ ≤ ENNReal.ofReal (Real.sqrt c) * (ENNReal.ofReal (Real.sqrt left) * M) := by
      gcongr 1 <;> exact hFloor
    _ = (ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal (Real.sqrt left)) * M := by
      rw [mul_assoc]
    _ ≤ ENNReal.ofReal (Real.sqrt sample) * M := by
      gcongr 1 <;> exact hScale

/-- Sampled normalized vanishing forces clock collapse along the existing floor. -/
theorem h3Terminal_clockRatio_tendsto_zero_of_floor_and_sample_vanishing
    (left sample : ℕ → ℝ) (M : ℕ → ℝ≥0∞) (C : ℝ)
    (hLeft : ∀ n : ℕ, 0 < left n)
    (hSample : ∀ n : ℕ, 0 < sample n)
    (hC : 0 < C)
    (hLower : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal C ≤ ENNReal.ofReal (Real.sqrt (left n)) * M n)
    (hZero : Tendsto
      (fun n : ℕ => ENNReal.ofReal (Real.sqrt (sample n)) * M n)
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => sample n / left n) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall
      (fun n : ℕ => lt_trans hb (div_pos (hSample n) (hLeft n)))
  · intro ε hε
    have hCoeff : (0 : ℝ≥0∞) < ENNReal.ofReal (Real.sqrt ε * C) :=
      ENNReal.ofReal_pos.mpr (mul_pos (Real.sqrt_pos.2 hε) hC)
    have hTiny : ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (Real.sqrt (sample n)) * M n <
          ENNReal.ofReal (Real.sqrt ε * C) :=
      (tendsto_order.1 hZero).2 _ hCoeff
    filter_upwards [hLower, hTiny] with n hn hTinyN
    apply (div_lt_iff₀ (hLeft n)).2
    by_contra hNot
    have hCompare : ε * left n ≤ sample n := le_of_not_gt hNot
    have hTransferred := h3Terminal_scaledFloor_of_clock_comparison hε hCompare hn
    exact (not_le_of_gt hTinyN) hTransferred

/-- One radial witness retains its floor and divergence and carries sample-clock collapse. -/
def H3TerminalHigherRadialPositiveFloorAndSampleClockCollapse
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (left : ℕ → ℝ) (radialOrder : ℕ) (C : ℝ) : Prop :=
  0 < C ∧
  ∃ v : ℕ → ℕ,
    StrictMono v ∧
    Tendsto (fun n : ℕ => τ (v n)) atTop (𝓝 T) ∧
    (∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal C ≤
        ENNReal.ofReal (Real.sqrt (left (v n))) *
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass radialOrder (τ (v n)) (hτ (v n))) ∧
    (¬ Tendsto
      (fun n : ℕ =>
        ENNReal.ofReal (Real.sqrt (left (v n))) *
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
    Tendsto (fun n : ℕ => (T - τ (v n)) / left (v n)) atTop (𝓝 0)

/-- Strengthen the existing selected floor, preserving its original subsequence. -/
theorem h3TerminalHigherRadial_floorAndSampleClockCollapse_of_sample_vanishing
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (left : ℕ → ℝ) (radialOrder : ℕ) (C : ℝ)
    (hLeft : ∀ n : ℕ, 0 < left n)
    (hFloor : H3TerminalHigherRadialSqrtWidthPositiveFloor
      hH3 hClass τ hτ left radialOrder C)
    (hZero : Tendsto
      (fun n : ℕ =>
        ENNReal.ofReal (Real.sqrt (T - τ n)) *
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass radialOrder (τ n) (hτ n))
      atTop (𝓝 0)) :
    H3TerminalHigherRadialPositiveFloorAndSampleClockCollapse
      hH3 hClass τ hτ left radialOrder C := by
  obtain ⟨hC, v, hMono, hTau, hLower, hNonzero, hHigher⟩ := hFloor
  have hZeroSub := hZero.comp hMono.tendsto_atTop
  have hRatio :
      Tendsto (fun n : ℕ => (T - τ (v n)) / left (v n)) atTop (𝓝 0) :=
    h3Terminal_clockRatio_tendsto_zero_of_floor_and_sample_vanishing
      (fun n : ℕ => left (v n))
      (fun n : ℕ => T - τ (v n))
      (fun n : ℕ => h3TerminalPhysicalExtendedHigherRadialMomentAt
        hH3 hClass radialOrder (τ (v n)) (hτ (v n))) C
      (fun n : ℕ => hLeft (v n))
      (fun n : ℕ => sub_pos.mpr (hτ (v n)).2)
      hC hLower hZeroSub
  exact ⟨hC, v, hMono, hTau, hLower, hNonzero, hHigher, hZeroSub, hRatio⟩

/-- Retain energy escape or a radial witness with synchronized sample-clock collapse. -/
theorem resolvedCanonicalForcing_energy_or_synchronized_sampleClock_collapse
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (left : ℕ → ℝ) (δ : ℝ)
    (hLeft : ∀ n : ℕ, 0 < left n)
    (hBranch : H3TerminalResolvedCanonicalForcingSqrtWidthPositiveFloorBranch
      hH3 hClass τ hτ δ left)
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
      H3TerminalHigherRadialPositiveFloorAndSampleClockCollapse
        hH3 hClass τ hτ left
        (h3TerminalForcingThirdQHigherRadialShift qRadial)
        (h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient δ qRadial)) ∨
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialPositiveFloorAndSampleClockCollapse
        hH3 hClass τ hτ left
        (h3TerminalForcingFourthQHigherRadialShift qRadial)
        (h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient δ qRadial)) := by
  rcases hBranch with hEnergy | hSecond | hFourth
  · exact Or.inl hEnergy
  · obtain ⟨qRadial, hFloor⟩ := hSecond
    exact Or.inr (Or.inl ⟨qRadial,
      h3TerminalHigherRadial_floorAndSampleClockCollapse_of_sample_vanishing
        hH3 hClass τ hτ left _ _ hLeft hFloor (hSecondZero qRadial)⟩)
  · obtain ⟨qRadial, hFloor⟩ := hFourth
    exact Or.inr (Or.inr ⟨qRadial,
      h3TerminalHigherRadial_floorAndSampleClockCollapse_of_sample_vanishing
        hH3 hClass τ hτ left _ _ hLeft hFloor (hFourthZero qRadial)⟩)

end

end Euclidean
end Bridge
end PrimeTensor
