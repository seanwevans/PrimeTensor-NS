import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopTimeDistributionFromWeakFTC244
import Mathlib.Tactic

/-!
# The one-dimensional homogeneous distribution kernel: compact-test spanning reduction

The remaining distributional uniqueness theorem is reduced to a genuinely
one-dimensional assertion about compact smooth time tests.  A normalized
compact smooth time test `ρ` must generate the integral quotient of all
compact tests, while compact zero-mean time tests must be derivatives of
compact smooth time tests on the same connected interval.

This module proves the *distribution-theoretic* half of the argument:
under the explicit compact-test spanning property, **every** scalar
distribution whose distributional time derivative is zero is precisely a
constant regular distribution.  It then transfers this to the actual physical
momentum-minus-source-primitive defect.

Importantly, the test-function spanning property is a named, visible premise,
not a theorem silently assumed from `LoggedPreterminalH3PathAdmissible`.
Its unconditional construction is the next analytic obligation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set TopologicalSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval Topology Distributions

noncomputable section
set_option maxHeartbeats 1800000

/-- The exact compact-test algebraic spanning statement needed to identify
zero-derivative distributions on the open time interval.  The coefficient
of the fixed bump is the *actual integral* of the test. -/
def h3PathCompactTimeTestDerivativeSpan244 (a b : ℝ) : Prop :=
  ∃ ρ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
    ∀ θ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
      ∃ η : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
        θ = TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) η +
          (∫ t : ℝ, θ t) • ρ

/-- A normalized compact bump and compact antiderivatives for zero-mass
tests imply the precise spanning property. This separates elementary linear
algebra from the genuinely analytic construction of antiderivatives with
compact support. -/
theorem h3Path_compactTimeTestSpan_of_normalizedBump_and_zeroMassPrimitive244
    (a b : ℝ)
    (ρ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤)
    (hρ : (∫ t : ℝ, ρ t) = 1)
    (hPrimitive : ∀ θ : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
      (∫ t : ℝ, θ t) = 0 →
        ∃ η : TestFunction (h3PathStrictTimeOpen244 a b) ℝ ⊤,
          θ = TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) η) :
    h3PathCompactTimeTestDerivativeSpan244 a b := by
  let Ω : Opens ℝ := h3PathStrictTimeOpen244 a b
  have hOne : LocallyIntegrableOn (fun _ : ℝ => (1 : ℝ))
      Ω (volume : Measure ℝ) :=
    continuousOn_const.locallyIntegrableOn measurableSet_Ioo
  have hρInt : Integrable (fun t : ℝ => ρ t) volume := ρ.integrable hOne
  refine ⟨ρ, ?_⟩
  intro θ
  let c : ℝ := ∫ t : ℝ, θ t
  let q : TestFunction Ω ℝ ⊤ := θ - c • ρ
  have hθInt : Integrable (fun t : ℝ => θ t) volume := θ.integrable hOne
  have hqZero : (∫ t : ℝ, q t) = 0 := by
    change (∫ t : ℝ, θ t - c • ρ t) = 0
    have hcρInt : Integrable (fun t : ℝ => c • ρ t) volume := by
      simpa only [smul_eq_mul] using hρInt.const_mul c
    rw [integral_sub hθInt hcρInt, integral_smul, hρ]
    simp [c]
  obtain ⟨η, hη⟩ := hPrimitive q hqZero
  refine ⟨η, ?_⟩
  calc
    θ = q + c • ρ := by dsimp [q]; abel
    _ = TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) η +
        (∫ t : ℝ, θ t) • ρ := by
          exact congrArg (fun v : TestFunction Ω ℝ ⊤ => v + c • ρ) hη

/-- The algebraic content of the connected-interval kernel theorem.  This
works for *arbitrary* distributions, not merely regular distributions and
not merely the projected Navier--Stokes source.  It does not invoke classical
differentiability of the represented function. -/
theorem h3Path_zeroDistributionDerivative_eq_constant_of_compactSpan244
    (a b : ℝ)
    (hSpan : h3PathCompactTimeTestDerivativeSpan244 a b)
    (D : Distribution (h3PathStrictTimeOpen244 a b) ℝ ⊤)
    (hZero : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℝ) D = 0) :
    ∃ K : ℝ,
      D = h3PathRegularTimeDistribution244
        (h3PathStrictTimeOpen244 a b) (fun _ : ℝ => K) := by
  obtain ⟨ρ, hSpan⟩ := hSpan
  let K : ℝ := D ρ
  refine ⟨K, ?_⟩
  let Ω : Opens ℝ := h3PathStrictTimeOpen244 a b
  have hKLoc : LocallyIntegrableOn (fun _ : ℝ => K)
      Ω (volume : Measure ℝ) :=
    continuousOn_const.locallyIntegrableOn measurableSet_Ioo
  ext θ
  obtain ⟨η, hθ⟩ := hSpan θ
  have hDerivativeZero : D (TestFunction.lineDerivCLM (k := ⊤)
      ℝ (1 : ℝ) η) = 0 := by
    have h := congrArg
      (fun X : Distribution Ω ℝ ⊤ => X η) hZero
    have h0 : (0 : Distribution Ω ℝ ⊤) η = 0 := by simp
    rw [Distribution.lineDerivCLM_apply, h0] at h
    exact neg_eq_zero.mp h
  have hEval : D θ = (∫ t : ℝ, θ t) * K := by
    calc
      D θ = D (TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) η +
          (∫ t : ℝ, θ t) • ρ) := congrArg D hθ
      _ = D (TestFunction.lineDerivCLM (k := ⊤) ℝ (1 : ℝ) η) +
          (∫ t : ℝ, θ t) • D ρ := by
            rw [map_add, map_smul]
      _ = (∫ t : ℝ, θ t) * K := by
            simp only [hDerivativeZero, zero_add, smul_eq_mul, K]
  rw [h3Path_regularTimeDistribution_apply244 Ω (fun _ : ℝ => K) hKLoc]
  simpa only [smul_eq_mul, integral_mul_const, mul_comm] using hEval

/-- Applying the general homogeneous kernel result to the exact physical
momentum-minus-projected-source-primitive distribution.  The physical
momentum distributional equation remains an EXPLICIT hypothesis. -/
theorem h3Path_physicalFTCDefect_constantDistribution_of_compactSpan244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T)
    (hSpan : h3PathCompactTimeTestDerivativeSpan244 a b)
    (hMomentum : h3PathSolenoidalDistributionalMomentumOn244 hH3 a b) :
    ∀ φ : H3WeakTestVector, H3WeakTestVectorDivergenceFree φ →
      ∃ K : ℝ,
        h3PathPhysicalTestFTCDefectDistribution244 hH3 a b φ =
          h3PathRegularTimeDistribution244
            (h3PathStrictTimeOpen244 a b) (fun _ : ℝ => K) := by
  have hDefectZero :=
    (h3Path_distributionalMomentum_iff_defectDerivativeZero244
      hH3 ha hab hb).mp hMomentum
  intro φ hφ
  exact h3Path_zeroDistributionDerivative_eq_constant_of_compactSpan244
    a b hSpan
    (h3PathPhysicalTestFTCDefectDistribution244 hH3 a b φ)
    (hDefectZero φ hφ)

end
end PrimeTensor.FirstMonomialTriad
