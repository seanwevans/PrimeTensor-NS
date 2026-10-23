import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionKernelSpan244
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic

/-!
# Normalized compact smooth time bump on every strict interval

The algebraic kernel theorem `KernelSpan244` assumes a normalized test `ρ`
and compact antiderivatives of zero-mass tests. This module proves the
existence of `ρ` with integral exactly one UNCONDITIONALLY for `a < b`.

The pinned mathlib `ContDiffBump.normed` supplies a smooth real function with
integral one; its exact closed-ball support is placed strictly inside `(a,b)`.
The only remaining test-spanning premise is now the compact antiderivative
of a smooth time test with zero integral.

No projected physical momentum identity is inferred from H³ admissibility.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set TopologicalSpace Metric
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

/-- Every nonempty real interval admits a normalized compact smooth test
with support strictly inside it. In particular, the normalized bump used to
split the codimension-one quotient of time tests is not an extra PDE axiom. -/
theorem h3Path_exists_normalizedCompactTimeBump244
    {a b : ℝ} (hab : a < b) :
    ∃ ρ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
      (∫ t : ℝ, ρ t) = 1 := by
  let c : ℝ := (a + b) / 2
  let r : ℝ := (b - a) / 4
  have hr : 0 < r := by
    dsimp [r]
    linarith
  let β : ContDiffBump c :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  have hClosed : Metric.closedBall c r ⊆ Set.Ioo a b := by
    intro t ht
    have hdist : dist t c ≤ r := Metric.mem_closedBall.mp ht
    have htAbs : |t - c| ≤ r := by
      simpa only [Real.dist_eq] using hdist
    obtain ⟨hLo, hHi⟩ := abs_le.mp htAbs
    dsimp [c, r] at hLo hHi
    constructor <;> linarith
  let ρ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤ :=
    ⟨β.normed (volume : Measure ℝ),
      β.contDiff_normed,
      β.hasCompactSupport_normed,
      by
        change tsupport (β.normed (volume : Measure ℝ)) ⊆ Set.Ioo a b
        rw [β.tsupport_normed_eq]
        exact hClosed⟩
  refine ⟨ρ, ?_⟩
  change (∫ t : ℝ, β.normed (volume : Measure ℝ) t) = 1
  exact β.integral_normed

/-- Normalization is now automatic; compact antiderivatives for zero-mean
tests suffice to generate the whole test space by derivatives and one bump. -/
theorem h3Path_compactTimeTestSpan_of_zeroMassPrimitive244
    {a b : ℝ} (hab : a < b)
    (hPrimitive : ∀ θ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
      (∫ t : ℝ, θ t) = 0 →
        ∃ η : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
          θ = TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) η) :
    h3PathCompactTimeTestDerivativeSpan244 a b := by
  obtain ⟨ρ, hρ⟩ := h3Path_exists_normalizedCompactTimeBump244 hab
  exact h3Path_compactTimeTestSpan_of_normalizedBump_and_zeroMassPrimitive244
    a b ρ hρ hPrimitive

/-- Hence arbitrary zero-derivative scalar distributions are constants as
soon as compact antiderivatives for zero-mean tests are established. -/
theorem h3Path_zeroDistributionDerivative_eq_constant_of_zeroMassPrimitive244
    {a b : ℝ} (hab : a < b)
    (hPrimitive : ∀ θ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
      (∫ t : ℝ, θ t) = 0 →
        ∃ η : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
          θ = TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) η)
    (D : Distribution (h3PathStrictTimeOpen244 a b) ℝ ⊤)
    (hZero : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℝ) D = 0) :
    ∃ K : ℝ, D = h3PathRegularTimeDistribution244
      (h3PathStrictTimeOpen244 a b) (fun _ : ℝ => K) := by
  exact h3Path_zeroDistributionDerivative_eq_constant_of_compactSpan244
    a b (h3Path_compactTimeTestSpan_of_zeroMassPrimitive244 hab hPrimitive) D hZero

/-- Physical specialization, retaining the unresolved PDE-to-distribution
premise and the now single remaining real-analysis premise. -/
theorem h3Path_physicalFTCDefect_constantDistribution_of_zeroMassPrimitive244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hPrimitive : ∀ θ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
      (∫ t : ℝ, θ t) = 0 →
        ∃ η : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
          θ = TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) η)
    (hMomentum : h3PathSolenoidalDistributionalMomentumOn244 hH3 a b) :
    ∀ φ : H3WeakTestVector, H3WeakTestVectorDivergenceFree φ →
      ∃ K : ℝ,
        h3PathPhysicalTestFTCDefectDistribution244 hH3 a b φ =
          h3PathRegularTimeDistribution244
            (h3PathStrictTimeOpen244 a b) (fun _ : ℝ => K) := by
  exact h3Path_physicalFTCDefect_constantDistribution_of_compactSpan244
    hH3 ha hab hb
    (h3Path_compactTimeTestSpan_of_zeroMassPrimitive244 hab hPrimitive)
    hMomentum

end
end PrimeTensor.FirstMonomialTriad
