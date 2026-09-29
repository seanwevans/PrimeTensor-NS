import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeSelectedEnstrophyEnvelopeClockRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFixedActualVorticityEnvelopeEscape

/-!
# Selected native rate transferred to a vorticity envelope

A common vorticity envelope bounds every actual vorticity component.  Hence the
fixed actual component selected under the raw native ceiling transfers its
normalized square growth directly to any supplied envelope along the same
cofinal native extraction.

The conclusion is pointwise along the selected witness: the envelope square,
divided by the original selected native index, tends to positive infinity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The offset square of a selected actual vorticity component is controlled by
an absolute constant plus twice the normalized square of any common vorticity
envelope. -/
theorem native_actualVorticity_offsetRatio_le_vorticityEnvelopeSquareRatio
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (i : Fin 3) (x : Point3) (j : ℕ) :
    (1 + |h3NativeActualVorticityComponentAt u i t x|) ^ 2 /
        ((j : ℝ) + 1) ≤
      2 + 2 * ((g t) ^ 2 / ((j : ℝ) + 1)) := by
  let A : ℝ := |h3NativeActualVorticityComponentAt u i t x|
  let G : ℝ := g t
  let D : ℝ := (j : ℝ) + 1
  have hAG : A ≤ G := by
    simpa only [A, G] using
      h3NativeActualVorticityComponentAt_le_vorticityEnvelope
        hEnvelope i x
  have hGNonneg : 0 ≤ G :=
    (abs_nonneg (h3NativeActualVorticityComponentAt u i t x)).trans hAG
  have hASquare : A ^ 2 ≤ G ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hGNonneg).2 hAG
  have hOffset : (1 + A) ^ 2 ≤ 2 * (1 + A ^ 2) := by
    nlinarith [sq_nonneg (A - 1)]
  have hDenPos : 0 < D := by
    dsimp [D]
    positivity
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
  have hSquareDiv : A ^ 2 / D ≤ G ^ 2 / D :=
    div_le_div_of_nonneg_right hASquare (le_of_lt hDenPos)
  have hOneDiv : 1 / D ≤ 1 :=
    (div_le_iff₀ hDenPos).2 (by nlinarith [hDenOne])
  change (1 + A) ^ 2 / D ≤ 2 + 2 * (G ^ 2 / D)
  linarith

/-- Under the selected raw native ceiling, every supplied common vorticity
envelope inherits a divergent normalized square rate along the same selected
fixed-component extraction. -/
theorem positiveGrowth_native_vorticityEnvelopeSquareRatio_of_selectedRawCeiling
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
    (hEnvelope : ∀ j : ℕ, VorticityEnvelope u g (τ j)) :
    ∃ i : Fin 3, ∃ m : ℕ → ℕ, ∃ z : ℕ → Point3,
      (∀ n : ℕ, n ≤ m n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (m n)) (fun n => y (m n)) ∧
      (∀ n : ℕ,
        (n : ℝ) / 8 - 1 <
          (g (τ (m n))) ^ 2 / ((m n : ℝ) + 1)) ∧
      Tendsto
        (fun n : ℕ =>
          (g (τ (m n))) ^ 2 / ((m n : ℝ) + 1))
        atTop atTop := by
  obtain ⟨i, m, z, hm, hNative, _hApprox, _hCompare,
    hQuarter, hComponentTop⟩ :=
    positiveGrowth_native_fixedActualVorticityRatio_of_selectedRawCeiling
      hH3 hNoExtension hClass hb hData hRawCeiling
  have hOffset : ∀ n : ℕ,
      (1 + |h3NativeActualVorticityComponentAt u i
        (τ (m n)) (z n)|) ^ 2 / ((m n : ℝ) + 1) ≤
        2 + 2 *
          ((g (τ (m n))) ^ 2 / ((m n : ℝ) + 1)) := by
    intro n
    exact native_actualVorticity_offsetRatio_le_vorticityEnvelopeSquareRatio
      (hEnvelope (m n)) i (z n) (m n)
  have hEnvelopeRate : ∀ n : ℕ,
      (n : ℝ) / 8 - 1 <
        (g (τ (m n))) ^ 2 / ((m n : ℝ) + 1) := by
    intro n
    linarith [hQuarter n, hOffset n]
  have hEnvelopeTop :
      Tendsto
        (fun n : ℕ =>
          (g (τ (m n))) ^ 2 / ((m n : ℝ) + 1))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro C
    filter_upwards
      [hComponentTop.eventually (eventually_ge_atTop (2 + 2 * C))]
      with n hn
    linarith [hOffset n]
  exact ⟨i, m, z, hm, hNative, hEnvelopeRate, hEnvelopeTop⟩

end

end Euclidean
end Bridge
end PrimeTensor
