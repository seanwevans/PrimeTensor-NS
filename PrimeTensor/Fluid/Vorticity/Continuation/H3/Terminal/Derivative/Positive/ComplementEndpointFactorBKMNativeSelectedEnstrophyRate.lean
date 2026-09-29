import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeSelectedFixedActualVorticityRatio
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.EnstrophySequence

/-!
# Pointwise enstrophy on a selected native witness

The squared magnitude of any actual vorticity component is bounded by
pointwise real enstrophy. A fixed-component normalized rate therefore
forces a normalized pointwise enstrophy rate at the same selected
spatial points and native times. This is a statement about sampled
values, with no time-integrated enstrophy conclusion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Any fixed logged vorticity component has square no larger than
the pointwise real enstrophy density. -/
theorem native_actualVorticityComponent_sq_le_realEnstrophy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (i : Fin 3) (t : ℝ) (x : Point3) :
    (h3NativeActualVorticityComponentAt u i t x) ^ 2 ≤
      realEnstrophyDensity
        (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x := by
  let X : ℝ :=
    |realVorticityX (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x|
  let Y : ℝ :=
    |realVorticityY (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x|
  let Z : ℝ :=
    |realVorticityZ (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x|
  have hAbsLe :
      |h3NativeActualVorticityComponentAt u i t x| ≤
        h3NativeActualVorticityComponentMaxAt u t x := by
    by_cases hX : i = 0
    · simpa [h3NativeActualVorticityComponentAt,
        h3NativeActualVorticityComponentMaxAt, hX, X, Y, Z] using
        (le_max_left X (max Y Z))
    by_cases hY : i = 1
    · simpa [h3NativeActualVorticityComponentAt,
        h3NativeActualVorticityComponentMaxAt, hX, hY, X, Y, Z] using
        ((le_max_left Y Z).trans (le_max_right X (max Y Z)))
    · simpa [h3NativeActualVorticityComponentAt,
        h3NativeActualVorticityComponentMaxAt, hX, hY, X, Y, Z] using
        ((le_max_right Y Z).trans (le_max_right X (max Y Z)))
  have hMaxNonneg :
      0 ≤ h3NativeActualVorticityComponentMaxAt u t x := by
    unfold h3NativeActualVorticityComponentMaxAt
    exact (abs_nonneg _).trans (le_max_left _ _)
  have hSquare :
      (h3NativeActualVorticityComponentAt u i t x) ^ 2 ≤
        (h3NativeActualVorticityComponentMaxAt u t x) ^ 2 := by
    have hSquareAbs :=
      (sq_le_sq₀ (abs_nonneg _) hMaxNonneg).2 hAbsLe
    simpa only [sq_abs] using hSquareAbs
  exact hSquare.trans
    (sq_vorticityComponentMax_le_realEnstrophyDensity
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x)

/-- The offset normalized component square is bounded by a constant
plus twice the normalized pointwise enstrophy. -/
theorem native_actualVorticity_offsetRatio_le_enstrophyRatio
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (i : Fin 3) (t : ℝ) (x : Point3) (j : ℕ) :
    (1 + |h3NativeActualVorticityComponentAt u i t x|) ^ 2 /
        ((j : ℝ) + 1) ≤
      2 + 2 *
        (realEnstrophyDensity
          (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x /
            ((j : ℝ) + 1)) := by
  let A : ℝ := |h3NativeActualVorticityComponentAt u i t x|
  let E : ℝ :=
    realEnstrophyDensity
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) t x
  let D : ℝ := (j : ℝ) + 1
  have hASquare : A ^ 2 ≤ E := by
    simpa only [A, E, sq_abs] using
      native_actualVorticityComponent_sq_le_realEnstrophy u i t x
  have hOffset : (1 + A) ^ 2 ≤ 2 * (1 + A ^ 2) := by
    nlinarith [sq_nonneg (A - 1)]
  have hDenPos : 0 < D := by dsimp [D]; positivity
  have hDenOne : 1 ≤ D := by
    dsimp [D]
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hOffsetDiv :
      (1 + A) ^ 2 / D ≤ 2 * (1 / D) + 2 * (A ^ 2 / D) := by
    calc
      (1 + A) ^ 2 / D ≤ (2 * (1 + A ^ 2)) / D :=
        div_le_div_of_nonneg_right hOffset (le_of_lt hDenPos)
      _ = 2 * (1 / D) + 2 * (A ^ 2 / D) := by ring
  have hSquareDiv : A ^ 2 / D ≤ E / D :=
    div_le_div_of_nonneg_right hASquare (le_of_lt hDenPos)
  have hOneDiv : 1 / D ≤ 1 :=
    (div_le_iff₀ hDenPos).2 (by nlinarith [hDenOne])
  change (1 + A) ^ 2 / D ≤ 2 + 2 * (E / D)
  linarith

/-- A ceiling on one native witness gives a cofinal quantitative
sequence with a fixed actual component and divergent normalized
pointwise enstrophy at the same spatial points. -/
theorem positiveGrowth_native_pointwiseEnstrophyRatio_of_selectedRawCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hRawCeiling : H3TerminalNativeRawSubexponentialCeilingOnWitness u τ) :
    ∃ i : Fin 3, ∃ m : ℕ → ℕ, ∃ z : ℕ → Point3,
      (∀ n : ℕ, n ≤ m n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (m n)) (fun n => y (m n)) ∧
      (∀ n : ℕ,
        (n : ℝ) / 4 <
          (1 + |h3NativeActualVorticityComponentAt u i
            (τ (m n)) (z n)|) ^ 2 / ((m n : ℝ) + 1)) ∧
      Tendsto
        (fun n : ℕ =>
          (1 + |h3NativeActualVorticityComponentAt u i
            (τ (m n)) (z n)|) ^ 2 / ((m n : ℝ) + 1))
        atTop atTop ∧
      (∀ n : ℕ,
        (n : ℝ) / 8 - 1 <
          realEnstrophyDensity
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ (m n)) (z n) / ((m n : ℝ) + 1)) ∧
      Tendsto
        (fun n : ℕ =>
          realEnstrophyDensity
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ (m n)) (z n) / ((m n : ℝ) + 1))
        atTop atTop := by
  obtain ⟨i, m, z, hm, hNative, _hApprox, _hCompare,
    hQuarter, hComponentTop⟩ :=
    positiveGrowth_native_fixedActualVorticityRatio_of_selectedRawCeiling
      hH3 hNoExtension hClass hb hData hRawCeiling
  have hOffset : ∀ n : ℕ,
      (1 + |h3NativeActualVorticityComponentAt u i
        (τ (m n)) (z n)|) ^ 2 / ((m n : ℝ) + 1) ≤
        2 + 2 *
          (realEnstrophyDensity
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ (m n)) (z n) / ((m n : ℝ) + 1)) := by
    intro n
    exact native_actualVorticity_offsetRatio_le_enstrophyRatio
      u i (τ (m n)) (z n) (m n)
  have hEnstrophyRate : ∀ n : ℕ,
      (n : ℝ) / 8 - 1 <
        realEnstrophyDensity
          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          (τ (m n)) (z n) / ((m n : ℝ) + 1) := by
    intro n
    linarith [hQuarter n, hOffset n]
  have hEnstrophyTop :
      Tendsto
        (fun n : ℕ =>
          realEnstrophyDensity
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ (m n)) (z n) / ((m n : ℝ) + 1))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro C
    filter_upwards
      [hComponentTop.eventually (eventually_ge_atTop (2 + 2 * C))]
      with n hn
    linarith [hOffset n]
  exact ⟨i, m, z, hm, hNative, hQuarter, hComponentTop,
    hEnstrophyRate, hEnstrophyTop⟩

end

end Euclidean
end Bridge
end PrimeTensor
