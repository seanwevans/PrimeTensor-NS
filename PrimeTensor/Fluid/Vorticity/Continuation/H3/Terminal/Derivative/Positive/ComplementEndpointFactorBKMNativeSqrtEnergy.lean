import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementCanonicalEndpointRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointLogFactorSynchronization

/-!
# A square-root energy cost on every native endpoint witness

The native gradient exceeds the selected index. If the squared vorticity
factor is at most linear in that index, the actual-gradient BKM estimate
forces the squared logarithmic energy factor to be at least linear. This
estimate needs no relative-ratio escape and applies to all complement
branches. The vorticity ceiling remains an explicit hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- An index-sized product and a linear ceiling on the square of its first
factor force an index-sized square of the second factor. -/
theorem indexed_product_square_lower
    (V L : ℕ → ℝ) (B C : ℝ)
    (hRate : ∀ n : ℕ, (n : ℝ) + 1 < B * V n * L n)
    (hCeiling : ∀ᶠ n : ℕ in atTop,
      (V n) ^ 2 / ((n : ℝ) + 1) ≤ C) :
    ∃ D : ℝ, 0 < D ∧
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) + 1 < D * (L n) ^ 2 := by
  let D : ℝ := max (B ^ 2 * C) 0 + 1
  have hDPos : 0 < D := by
    dsimp [D]
    linarith [le_max_right (B ^ 2 * C) 0]
  refine ⟨D, hDPos, ?_⟩
  filter_upwards [hCeiling] with n hn
  let S : ℝ := (n : ℝ) + 1
  have hSPos : 0 < S := by dsimp [S]; positivity
  have hVCeiling : (V n) ^ 2 ≤ C * S := by
    apply (div_le_iff₀ hSPos).mp
    exact hn
  have hProductPos : 0 < B * V n * L n :=
    lt_trans hSPos (hRate n)
  have hRateSq : S ^ 2 < (B * V n * L n) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr (hRate n))
      (add_pos hProductPos hSPos)]
  have hUpperSq :
      (B * V n * L n) ^ 2 ≤ (B ^ 2 * C) * S * (L n) ^ 2 := by
    calc
      (B * V n * L n) ^ 2 = (B ^ 2 * (L n) ^ 2) * (V n) ^ 2 := by ring
      _ ≤ (B ^ 2 * (L n) ^ 2) * (C * S) :=
        mul_le_mul_of_nonneg_left hVCeiling (by positivity)
      _ = (B ^ 2 * C) * S * (L n) ^ 2 := by ring
  have hIndex : S < (B ^ 2 * C) * (L n) ^ 2 := by
    by_contra h
    have hReverse : (B ^ 2 * C) * (L n) ^ 2 ≤ S :=
      le_of_not_gt h
    have hScaled : S * ((B ^ 2 * C) * (L n) ^ 2) ≤ S * S :=
      mul_le_mul_of_nonneg_left hReverse (le_of_lt hSPos)
    nlinarith [hRateSq, hUpperSq, hScaled]
  have hCoefficient : B ^ 2 * C ≤ D := by
    dsimp [D]
    linarith [le_max_left (B ^ 2 * C) 0]
  have hD : (B ^ 2 * C) * (L n) ^ 2 ≤ D * (L n) ^ 2 :=
    mul_le_mul_of_nonneg_right hCoefficient (sq_nonneg _)
  exact hIndex.trans_le hD

/-- On any quantitative native witness, a normalized vorticity ceiling
imposes a square-root-index lower rate on the logarithmic energy factor
of an actual-gradient endpoint estimate. -/
theorem positiveGrowth_native_endpoint_logEnergy_square_lower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    {g E : ℝ → ℝ} {B C : ℝ}
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hEndpoint : ActualVelocityGradientLogBoundFrom u b T g E B)
    (hVorticityCeiling : ∀ᶠ n : ℕ in atTop,
      (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1) ≤ C) :
    ∃ D : ℝ, 0 < D ∧
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) + 1 <
          D * (1 + Real.log (E (τ n))) ^ 2 := by
  exact indexed_product_square_lower
    (fun n => 1 + |g (τ n)|)
    (fun n => 1 + Real.log (E (τ n))) B C
    (positiveGrowth_nativeGradient_forces_endpointRate hData hEndpoint)
    hVorticityCeiling

/-- The canonical BKM coefficient and actual H³ energy obey the same
necessary rate on every native witness, including the forced and bounded
complement branches. -/
theorem positiveGrowth_native_canonical_logEnergy_square_lower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    {g : ℝ → ℝ} {C : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hVorticityCeiling : ∀ᶠ n : ℕ in atTop,
      (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1) ≤ C) :
    ∃ D : ℝ, 0 < D ∧
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) + 1 <
          D * (1 + Real.log (velocityH3EnergyAt u (τ n))) ^ 2 := by
  have hbAbs : b ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hb.1, hb.2⟩
  have hEndpoint : ActualVelocityGradientLogBoundFrom
      u b T g (velocityH3EnergyAt u)
      (h3BKMCanonicalSelectedLogGradientConstant
        (Real.sqrt (velocityH3Energy0At u b))) :=
    actualVelocityGradientLogBoundFrom_canonicalSelectedBKM_of_kineticEnergyControlledFromAnchor
      hH3.navier_stokes hbAbs hg
      (h3EnergyProfileFrom_h3Path hH3 hbAbs)
      (bkmKineticEnergyControlledFromAnchor_of_h3Path_closed hH3 hClass hb)
  exact positiveGrowth_native_endpoint_logEnergy_square_lower
    hData hEndpoint hVorticityCeiling

end

end Euclidean
end Bridge
end PrimeTensor
