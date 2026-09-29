import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeSelectedEnstrophyClockRate
import PrimeTensor.Fluid.Vorticity.L1Linf.Control

/-!
# Vorticity-envelope square clock forces selected clock collapse rate

A componentwise vorticity envelope controls the pointwise enstrophy density by
three times the square of the envelope. Therefore an eventual bound on

`(T - τ n) * g (τ n)^2`

along the native witness supplies the physical-enstrophy ceiling required by
the quantitative selected-clock theorem. Under hypothetical nonextension and
the selected raw ceiling, the resulting selected endpoint gap is consequently
`O(1 / n^2)`.

This remains conditional on the square-clock envelope bound; vorticity
`L¹_t L∞_x` control by itself does not supply that pointwise-in-time rate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A common componentwise vorticity envelope bounds the pointwise real
enstrophy density by three times the square of the envelope. -/
theorem realEnstrophyDensity_le_three_mul_sq_of_vorticityEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (x : Point3) :
    realEnstrophyDensity
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x
      ≤
    3 * (g t) ^ 2 := by
  have hX := (hEnvelope x).1
  have hY := (hEnvelope x).2.1
  have hZ := (hEnvelope x).2.2
  have hg : 0 ≤ g t :=
    (abs_nonneg
      (realVorticityX
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x)).trans hX
  have hXSq :
      (realVorticityX
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x) ^ 2
        ≤ (g t) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hg).2 hX
    simpa only [sq_abs] using h
  have hYSq :
      (realVorticityY
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x) ^ 2
        ≤ (g t) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hg).2 hY
    simpa only [sq_abs] using h
  have hZSq :
      (realVorticityZ
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x) ^ 2
        ≤ (g t) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hg).2 hZ
    simpa only [sq_abs] using h
  unfold realEnstrophyDensity
  nlinarith

/-- A square-clock bound for a common vorticity envelope implies the physical
pointwise-enstrophy ceiling on the same native witness. -/
theorem boundedPhysicalVorticityEnvelopeSquareClock_implies_boundedPhysicalEnstrophy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    {g : ℝ → ℝ}
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hEnvelope : ∀ j : ℕ, VorticityEnvelope u g (τ j))
    (hSquareClock : ∃ B : ℝ,
      ∀ᶠ j : ℕ in atTop,
        (T - τ j) * (g (τ j)) ^ 2 ≤ B) :
    ∃ C : ℝ,
      ∀ᶠ j : ℕ in atTop, ∀ x : Point3,
        (T - τ j) *
          realEnstrophyDensity
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ j) x ≤ C := by
  obtain ⟨B, hBound⟩ := hSquareClock
  refine ⟨3 * B, ?_⟩
  filter_upwards [hBound] with j hj
  intro x
  have hGap : 0 ≤ T - τ j :=
    sub_nonneg.mpr (hData.1 j).1.2.le
  have hEnstrophy :=
    realEnstrophyDensity_le_three_mul_sq_of_vorticityEnvelope
      (hEnvelope j) x
  calc
    (T - τ j) *
        realEnstrophyDensity
          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          (τ j) x
        ≤
      (T - τ j) * (3 * (g (τ j)) ^ 2) :=
        mul_le_mul_of_nonneg_left hEnstrophy hGap
    _ = 3 * ((T - τ j) * (g (τ j)) ^ 2) := by ring
    _ ≤ 3 * B :=
      mul_le_mul_of_nonneg_left hj (by norm_num)

/-- Under hypothetical nonextension, a selected raw ceiling, and a bounded
physical square-clock for a common vorticity envelope along the native
witness, the selected dimensionless clock is `O(1/n)` and the physical
endpoint gap is `O(1/n^2)`. -/
theorem positiveGrowth_native_clockRate_of_boundedVorticityEnvelopeSquareClock
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hRawCeiling : H3TerminalNativeRawSubexponentialCeilingOnWitness u τ)
    (hEnvelope : ∀ j : ℕ, VorticityEnvelope u g (τ j))
    (hSquareClock : ∃ B : ℝ,
      ∀ᶠ j : ℕ in atTop,
        (T - τ j) * (g (τ j)) ^ 2 ≤ B) :
    ∃ i : Fin 3, ∃ m : ℕ → ℕ, ∃ z : ℕ → Point3, ∃ C : ℝ,
      0 ≤ C ∧
      (∀ n : ℕ, n ≤ m n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (m n)) (fun n => y (m n)) ∧
      Tendsto
        (fun n : ℕ =>
          (1 + |h3NativeActualVorticityComponentAt u i
            (τ (m n)) (z n)|) ^ 2 / ((m n : ℝ) + 1))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          realEnstrophyDensity
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ (m n)) (z n) / ((m n : ℝ) + 1))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          ((m n : ℝ) + 1) * (T - τ (m n)))
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ᶠ n : ℕ in atTop,
        (n : ℝ) *
            (((m n : ℝ) + 1) * (T - τ (m n))) ≤ C) ∧
      (∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ 2 * (T - τ (m n)) ≤ C) := by
  have hPhysicalCeiling : ∃ B : ℝ,
      ∀ᶠ j : ℕ in atTop, ∀ x : Point3,
        (T - τ j) *
          realEnstrophyDensity
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ j) x ≤ B :=
    boundedPhysicalVorticityEnvelopeSquareClock_implies_boundedPhysicalEnstrophy
      hData hEnvelope hSquareClock
  exact
    positiveGrowth_native_clockRate_of_boundedPhysicalEnstrophy
      hH3 hNoExtension hClass hb hData hRawCeiling hPhysicalCeiling

end

end Euclidean
end Bridge
end PrimeTensor
