import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorRelativeRefinement

/-!
# Bounded-factor implications on the refined relative witness

The refined witness carries divergence of one normalized canonical BKM
factor square, with the branch fixed on that witness. An eventual upper
bound on the other normalized square therefore forces the selected
factor to be the divergent one. This records separate analytic gates
for vorticity and logarithmic H³ energy without supplying either bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- An eventual bound for either factor forces divergence of the other. -/
def H3TerminalEndpointFactorBoundConsequences
    (V L : ℕ → ℝ) : Prop :=
  ((∃ C : ℝ, ∀ᶠ n : ℕ in atTop, L n ≤ C) →
      Tendsto V atTop atTop) ∧
    ((∃ C : ℝ, ∀ᶠ n : ℕ in atTop, V n ≤ C) →
      Tendsto L atTop atTop)

private theorem boundConsequences_of_factorRate
    (V L : ℕ → ℝ)
    (hRate : Tendsto V atTop atTop ∨ Tendsto L atTop atTop) :
    H3TerminalEndpointFactorBoundConsequences V L := by
  constructor
  · rintro ⟨C, hBound⟩
    rcases hRate with hV | hL
    · exact hV
    · obtain ⟨n, hnAbove, hnBound⟩ :=
        ((hL.eventually (eventually_gt_atTop C)).and hBound).exists
      exact False.elim ((not_lt_of_ge hnBound) hnAbove)
  · rintro ⟨C, hBound⟩
    rcases hRate with hV | hL
    · obtain ⟨n, hnAbove, hnBound⟩ :=
        ((hV.eventually (eventually_gt_atTop C)).and hBound).exists
      exact False.elim ((not_lt_of_ge hnBound) hnAbove)
    · exact hL

/-- On the same refined native and relative-escape witness, either
eventual normalized factor bound selects the other factor's divergent
rate. The conclusion retains the witness and its ratio inequality. -/
theorem endpointFactor_relativeRefinedWitness_boundConsequences
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    {ratio : ℕ → ℝ}
    (hWitness :
      H3TerminalEndpointFactorRelativeRefinedWitness
        u b T p sCurl sGradient τ y k g ratio) :
    ∃ l : ℕ → ℕ,
      Tendsto l atTop atTop ∧
        (∀ n : ℕ, n ≤ l n ∧ n ≤ k (l n)) ∧
        H3TerminalPositiveGrowthQuantitativeNativeData
          u b T p sCurl sGradient
            (fun n => τ (k (l n))) (fun n => y (k (l n))) ∧
        Tendsto (fun n : ℕ => |g (τ (k (l n)))|) atTop atTop ∧
        (∀ n : ℕ, (n : ℝ) + 1 < ratio (l n)) ∧
        H3TerminalEndpointFactorBoundConsequences
          (fun n : ℕ =>
            (1 + |g (τ (k (l n)))|) ^ 2 /
              ((k (l n) : ℝ) + 1))
          (fun n : ℕ =>
            (1 + Real.log (velocityH3EnergyAt u (τ (k (l n))))) ^ 2 /
              ((k (l n) : ℝ) + 1)) := by
  obtain ⟨l, hlTop, hIndex, hNative, hEnvelope, hRate, hRatio⟩ := hWitness
  exact ⟨l, hlTop, hIndex, hNative, hEnvelope, hRatio,
    boundConsequences_of_factorRate _ _ hRate⟩

end

end Euclidean
end Bridge
end PrimeTensor
