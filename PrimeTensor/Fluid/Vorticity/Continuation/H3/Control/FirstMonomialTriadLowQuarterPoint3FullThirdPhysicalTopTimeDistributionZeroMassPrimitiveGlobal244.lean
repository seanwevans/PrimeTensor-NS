import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionZeroMassPrimitiveInterior244
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Zero-mass time tests: unconditional compact antiderivative and distribution kernel

Every compact smooth time test supported in an open real interval has a compact
support bounded strictly away from both endpoints. The pinned mathlib extreme-
value lemma `IsCompact.exists_forall_le'` extracts the lower margin from the
identity function and the upper margin from negation. Enlarging the margins
slightly produces `a < ℓ < r < b` with the support inside `(ℓ,r)`, even when
the support is empty.

The interior-bounds compact primitive theorem then constructs the actual test
primitive. Together with the normalized bump and kernel-span results, this
makes the one-dimensional homogeneous distribution kernel unconditional.

This is scalar distribution theory only: no physical PDE-to-time-distribution
identity is inferred from H³ path admissibility.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set TopologicalSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

/-- Compact support inside a nonempty open interval admits *strictly interior*
left and right enclosures. The proof handles empty compact sets as well. -/
theorem h3Path_compactTimeTest_hasInteriorSupportBounds244
    {a b : ℝ} (hab : a < b)
    (θ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤) :
    ∃ ℓ r : ℝ,
      a < ℓ ∧ ℓ < r ∧ r < b ∧
      tsupport (fun t : ℝ => θ t) ⊆ Set.Ioo ℓ r := by
  let K : Set ℝ := tsupport (fun t : ℝ => θ t)
  have hKCompact : IsCompact K := θ.hasCompactSupport
  have hKInside : K ⊆ Set.Ioo a b := θ.tsupport_subset
  -- A strict lower margin from the compact-image minimum principle.
  obtain ⟨m, ham, hm⟩ := hKCompact.exists_forall_le'
    (f := fun t : ℝ => t) continuous_id.continuousOn
    (by
      intro t ht
      exact (hKInside ht).1)
  -- Explicitly fix the lower bound for the negated coordinate to `-b`.
  -- Without `(a := -b)`, `exists_forall_le'` leaves an unconstrained
  -- implicit parameter, so the later proof of `-n < b` has no useful bound.
  have hNegBelow : ∀ t ∈ K, (-b : ℝ) < -t := by
    intro t ht
    have htb : t < b := (hKInside ht).2
    linarith
  obtain ⟨n, hnb, hn⟩ := hKCompact.exists_forall_le'
    (f := fun t : ℝ => -t) (a := -b)
    (continuous_id.neg.continuousOn) hNegBelow
  let M : ℝ := -n
  have hMb : M < b := by
    dsimp [M]
    linarith only [hnb]
  have hKLower : ∀ t ∈ K, m ≤ t := by
    intro t ht
    exact hm t ht
  have hKUpper : ∀ t ∈ K, t ≤ M := by
    intro t ht
    have ht' := hn t ht
    dsimp [M]
    linarith
  -- The fixed middle-third reference bounds enforce ℓ < r, even for K=∅.
  let ℓ : ℝ := min ((a + m) / 2) ((2 * a + b) / 3)
  let r : ℝ := max ((M + b) / 2) ((a + 2 * b) / 3)
  have haℓ : a < ℓ := by
    change a < min ((a + m) / 2) ((2 * a + b) / 3)
    apply lt_min_iff.mpr
    constructor <;> linarith
  have hrb : r < b := by
    change max ((M + b) / 2) ((a + 2 * b) / 3) < b
    apply max_lt_iff.mpr
    constructor <;> linarith
  have hℓr : ℓ < r := by
    have hL : ℓ ≤ (2 * a + b) / 3 := min_le_right _ _
    have hR : (a + 2 * b) / 3 ≤ r := le_max_right _ _
    linarith
  refine ⟨ℓ, r, haℓ, hℓr, hrb, ?_⟩
  intro t ht
  have hLm : ℓ ≤ (a + m) / 2 := min_le_left _ _
  have hMr : (M + b) / 2 ≤ r := le_max_left _ _
  have hmt := hKLower t ht
  have htM := hKUpper t ht
  constructor <;> linarith

/-- Every zero-mean compact smooth scalar test on a connected open time interval
is the derivative of another compact smooth test on the *same* interval. -/
theorem h3Path_zeroMassTimeTest_hasCompactPrimitive244
    {a b : ℝ} (hab : a < b)
    (θ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤)
    (hMass : (∫ t : ℝ, θ t) = 0) :
    ∃ η : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
      θ = TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) η := by
  obtain ⟨ℓ, r, haℓ, hℓr, hrb, hInner⟩ :=
    h3Path_compactTimeTest_hasInteriorSupportBounds244 hab θ
  exact h3Path_zeroMassTimeTest_hasCompactPrimitive_of_interiorBounds244
    haℓ hℓr hrb θ hInner hMass

/-- Unconditional spanning by time derivatives and the normalized compact
smooth bump on every nonempty open real interval. -/
theorem h3Path_compactTimeTestDerivativeSpan_onStrict244
    {a b : ℝ} (hab : a < b) :
    h3PathCompactTimeTestDerivativeSpan244 a b := by
  exact h3Path_compactTimeTestSpan_of_zeroMassPrimitive244 hab
    (fun θ hMass => h3Path_zeroMassTimeTest_hasCompactPrimitive244 hab θ hMass)

/-- The kernel of time differentiation on scalar distributions over a connected
open interval consists precisely of constant regular distributions. -/
theorem h3Path_zeroDistributionDerivative_eq_constant_onStrict244
    {a b : ℝ} (hab : a < b)
    (D : Distribution (h3PathStrictTimeOpen244 a b) ℝ ⊤)
    (hZero : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℝ) D = 0) :
    ∃ K : ℝ,
      D = h3PathRegularTimeDistribution244
        (h3PathStrictTimeOpen244 a b) (fun _ : ℝ => K) := by
  exact h3Path_zeroDistributionDerivative_eq_constant_of_compactSpan244
    a b (h3Path_compactTimeTestDerivativeSpan_onStrict244 hab) D hZero

/-- Unconditional *scalar analytic* kernel applied to the physical FTC defect.
The distributional momentum equation remains an explicit assumption. -/
theorem h3Path_physicalFTCDefect_constantDistribution_onStrict244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hMomentum : h3PathSolenoidalDistributionalMomentumOn244 hH3 a b) :
    ∀ φ : H3WeakTestVector, H3WeakTestVectorDivergenceFree φ →
      ∃ K : ℝ,
        h3PathPhysicalTestFTCDefectDistribution244 hH3 a b φ =
          h3PathRegularTimeDistribution244
            (h3PathStrictTimeOpen244 a b) (fun _ : ℝ => K) := by
  exact h3Path_physicalFTCDefect_constantDistribution_of_compactSpan244
    hH3 ha hab hb (h3Path_compactTimeTestDerivativeSpan_onStrict244 hab)
    hMomentum

end
end PrimeTensor.FirstMonomialTriad
