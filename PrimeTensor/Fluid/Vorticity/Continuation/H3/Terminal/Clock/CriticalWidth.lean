import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Clock.ForwardWidth

/-!
# Critical coefficient for the forward-width normalized moment

The family of eventual lower bounds `ofReal (sqrt c * C)`, for `0 < c < 1`,
gives an eventual lower bound `ofReal D` for every fixed `0 < D < C`.
It rules out every eventual nonnegative finite ceiling strictly below `C`,
and every finite nonnegative limit must be at least `C`.

All conclusions are added to the same selected radial witness. They assert
neither convergence of the normalized moment nor an eventual bound by `C`
itself. The forcing alternative retains its existing hypotheses and energy branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

/-- Recover every strict subcritical threshold from the square-root coefficient family. -/
theorem h3Terminal_eventual_threshold_of_sqrt_coefficient_floors
    (F : ℕ → ℝ≥0∞) (C : ℝ)
    (hC : 0 < C)
    (hFloors : ∀ c : ℝ, 0 < c → c < 1 →
      ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.sqrt c * C) ≤ F n) :
    ∀ D : ℝ, 0 < D → D < C →
      ∀ᶠ n : ℕ in atTop, ENNReal.ofReal D ≤ F n := by
  intro D hD hDC
  have hRatioPos : 0 < D / C := div_pos hD hC
  have hRatioOne : D / C < 1 := by
    apply (div_lt_iff₀ hC).2
    simpa only [one_mul] using hDC
  have hcPos : 0 < (D / C) ^ 2 := by positivity
  have hcOne : (D / C) ^ 2 < 1 := by
    have hProduct := mul_pos hRatioPos (sub_pos.mpr hRatioOne)
    nlinarith
  have hCoeff : Real.sqrt ((D / C) ^ 2) * C = D := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hRatioPos]
    field_simp [ne_of_gt hC] <;> ring
  simpa only [hCoeff] using hFloors ((D / C) ^ 2) hcPos hcOne

/-- A strict subcritical eventual ceiling contradicts the threshold family. -/
theorem h3Terminal_no_subcritical_ceiling_of_eventual_thresholds
    (F : ℕ → ℝ≥0∞) (C : ℝ)
    (hC : 0 < C)
    (hThreshold : ∀ D : ℝ, 0 < D → D < C →
      ∀ᶠ n : ℕ in atTop, ENNReal.ofReal D ≤ F n) :
    ∀ D : ℝ, 0 ≤ D → D < C →
      ¬ (∀ᶠ n : ℕ in atTop, F n ≤ ENNReal.ofReal D) := by
  intro D hD hDC hCeiling
  have hMidPos : 0 < (D + C) / 2 := by linarith
  have hMidLt : (D + C) / 2 < C := by linarith
  obtain ⟨n, hLower, hUpper⟩ :=
    ((hThreshold ((D + C) / 2) hMidPos hMidLt).and hCeiling).exists
  have hMidLe : (D + C) / 2 ≤ D :=
    (ENNReal.ofReal_le_ofReal_iff hD).1 (le_trans hLower hUpper)
  linarith

/-- Any finite nonnegative limit is at least the critical coefficient. -/
theorem h3Terminal_coefficient_le_finite_limit_of_eventual_thresholds
    (F : ℕ → ℝ≥0∞) (C : ℝ)
    (hC : 0 < C)
    (hThreshold : ∀ D : ℝ, 0 < D → D < C →
      ∀ᶠ n : ℕ in atTop, ENNReal.ofReal D ≤ F n) :
    ∀ L : ℝ, 0 ≤ L → Tendsto F atTop (𝓝 (ENNReal.ofReal L)) → C ≤ L := by
  intro L hL hLimit
  by_contra hNot
  have hLC : L < C := lt_of_not_ge hNot
  have hMidPos : 0 < (L + C) / 2 := by linarith
  have hMidLt : (L + C) / 2 < C := by linarith
  have hLe : ENNReal.ofReal ((L + C) / 2) ≤ ENNReal.ofReal L :=
    ge_of_tendsto hLimit (hThreshold ((L + C) / 2) hMidPos hMidLt)
  have hMidLe : (L + C) / 2 ≤ L := (ENNReal.ofReal_le_ofReal_iff hL).1 hLe
  linarith

/-- The forward-width witness carries its full critical threshold family. -/
def H3TerminalHigherRadialForwardWidthCriticalThreshold
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
              hH3 hClass radialOrder (τ (v n)) (hτ (v n))) ∧
    (∀ D : ℝ, 0 < D → D < C →
      ∀ᶠ n : ℕ in atTop, ENNReal.ofReal D ≤
        ENNReal.ofReal (Real.sqrt (σ (v n) - s (v n))) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass radialOrder (τ (v n)) (hτ (v n))) ∧
    (∀ D : ℝ, 0 ≤ D → D < C →
      ¬ (∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (Real.sqrt (σ (v n) - s (v n))) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass radialOrder (τ (v n)) (hτ (v n)) ≤ ENNReal.ofReal D)) ∧
    (∀ L : ℝ, 0 ≤ L →
      Tendsto (fun n : ℕ =>
        ENNReal.ofReal (Real.sqrt (σ (v n) - s (v n))) *
            h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass radialOrder (τ (v n)) (hτ (v n))) atTop (𝓝 (ENNReal.ofReal L)) → C ≤ L)

/-- Recover critical thresholds while retaining the same selected witness. -/
theorem h3TerminalHigherRadial_criticalThreshold_of_forwardWidthGeometry
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (s σ : ℕ → ℝ) (radialOrder : ℕ) (C : ℝ)
    (hWitness : H3TerminalHigherRadialPositiveFloorAndForwardWidthGeometry
      hH3 hClass τ hτ s σ radialOrder C) :
    H3TerminalHigherRadialForwardWidthCriticalThreshold
      hH3 hClass τ hτ s σ radialOrder C := by
  obtain ⟨hC, v, hMono, hTau, hLower, hNonzero, hHigher, hZero, hRatio,
    hElapsed, hWidth, hSigmaZero, hRemaining,
    hSampleWidth, hElapsedWidth, hSigmaWidth, hRemainingWidth, hFloors⟩ := hWitness
  let F : ℕ → ℝ≥0∞ := fun n : ℕ =>
    ENNReal.ofReal (Real.sqrt (σ (v n) - s (v n))) *
      h3TerminalPhysicalExtendedHigherRadialMomentAt
        hH3 hClass radialOrder (τ (v n)) (hτ (v n))
  have hThreshold := h3Terminal_eventual_threshold_of_sqrt_coefficient_floors F C hC hFloors
  have hNoCeiling := h3Terminal_no_subcritical_ceiling_of_eventual_thresholds F C hC hThreshold
  have hFiniteLimit := h3Terminal_coefficient_le_finite_limit_of_eventual_thresholds F C hC hThreshold
  exact ⟨hC, v, hMono, hTau, hLower, hNonzero, hHigher, hZero, hRatio,
    hElapsed, hWidth, hSigmaZero, hRemaining,
    hSampleWidth, hElapsedWidth, hSigmaWidth, hRemainingWidth, hFloors,
    hThreshold, hNoCeiling, hFiniteLimit⟩

/-- Retain energy escape or a radial witness with the critical coefficient threshold. -/
theorem resolvedCanonicalForcing_energy_or_forwardWidthCriticalThreshold
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
      H3TerminalHigherRadialForwardWidthCriticalThreshold
        hH3 hClass τ hτ s σ
        (h3TerminalForcingThirdQHigherRadialShift qRadial)
        (h3TerminalForcingSecondQInverseSqrtWidthHigherCoefficient δ qRadial)) ∨
    (∃ qRadial : Fin 2,
      H3TerminalHigherRadialForwardWidthCriticalThreshold
        hH3 hClass τ hτ s σ
        (h3TerminalForcingFourthQHigherRadialShift qRadial)
        (h3TerminalForcingFourthQInverseSqrtWidthHigherCoefficient δ qRadial)) := by
  rcases resolvedCanonicalForcing_energy_or_forwardWidthGeometry
      hH3 hClass τ hτ s σ δ hs hForward hOrder hσ hBranch hSecondZero hFourthZero with
    hEnergy | hSecond | hFourth
  · exact Or.inl hEnergy
  · obtain ⟨qRadial, hWitness⟩ := hSecond
    exact Or.inr (Or.inl ⟨qRadial,
      h3TerminalHigherRadial_criticalThreshold_of_forwardWidthGeometry
        hH3 hClass τ hτ s σ _ _ hWitness⟩)
  · obtain ⟨qRadial, hWitness⟩ := hFourth
    exact Or.inr (Or.inr ⟨qRadial,
      h3TerminalHigherRadial_criticalThreshold_of_forwardWidthGeometry
        hH3 hClass τ hτ s σ _ _ hWitness⟩)

end

end Euclidean
end Bridge
end PrimeTensor
