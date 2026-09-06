import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Compact
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Pressure.Annihilation

/-!
# Classicalization: weak curl gives ordinary distributional curl

PrimeTensor already contains a pinned-Mathlib-compatible ordinary distribution
bridge for the weak pressure argument:

    H3WeakScalarDistribution
    h3WeakDistributionOfFun

This file reuses that known-green bridge rather than introducing a second
function-to-distribution constructor.

For each physical scalar `L²` coordinate, its raw representative is locally
integrable, so `h3WeakDistributionOfFun` acts on a compact smooth test by the
usual integral.  That integral is exactly the existing real `L²` Hilbert
pairing with `h3WeakTestFunctionPhysicalL2`.

The three weak curl identities therefore become literal equalities of ordinary
distributional derivatives, expressed through the already-established
`Distribution.lineDerivCLM` API:

    ∂₁ V₀ = ∂₀ V₁,
    ∂₂ V₀ = ∂₀ V₂,
    ∂₂ V₁ = ∂₁ V₂.

No Montel-space conversion and no newer `Distribution.ofFun` API are used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzDistribution
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzDistribution :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## L² representatives in the existing ordinary distribution bridge -/

/-- A physical scalar `L²` representative is locally integrable. -/
theorem h3PhysicalScalarL2_locallyIntegrable
    (f : H3ScalarL2) :
    LocallyIntegrable
      (f : Point3 → ℝ)
      (volume : Measure Point3) := by
  exact
    (MeasureTheory.Lp.memLp f).locallyIntegrable
      (by norm_num)

/-- Evaluating the existing function-induced ordinary distribution on a weak
test is exactly the scalar real `L²` Hilbert pairing. -/
theorem h3WeakDistributionOfPhysicalScalarL2_apply
    (f : H3ScalarL2)
    (ψ : H3WeakTestFunction) :
    h3WeakDistributionOfFun
        (f : Point3 → ℝ)
        ψ
      =
    inner ℝ
      f
      (h3WeakTestFunctionPhysicalL2 ψ) := by
  have hfLocalOn :
      LocallyIntegrableOn
        (f : Point3 → ℝ)
        Set.univ
        (volume : Measure Point3) :=
    (h3PhysicalScalarL2_locallyIntegrable f).locallyIntegrableOn
      Set.univ

  have hEval :
      h3WeakDistributionOfFun
          (f : Point3 → ℝ)
          ψ
        =
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          ((f : Point3 → ℝ) x)
        ∂volume := by
    unfold h3WeakDistributionOfFun
    exact
      TestFunction.integralAgainstBilinCLM_eq_integral
        hfLocalOn

  rw [hEval]
  rw [MeasureTheory.L2.inner_def]

  apply integral_congr_ae

  have hψ :=
    h3WeakTestFunctionPhysicalL2_ae ψ

  filter_upwards [hψ] with x hψx

  rw [hψx]

  simp [mul_comm]

/-! ## Ordinary distributional curl -/

/-- The three curl-zero identities in the already-established ordinary scalar
distribution space. -/
def H3PhysicalRealFinVectorL2HilbertDistributionCurlFree
    (V : H3PhysicalRealFinVectorL2Hilbert) : Prop :=
  (Distribution.lineDerivCLM
      (axisDirection (h3AxisOfFin3 1)) :
      H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
      (h3WeakDistributionOfFun
        (V 0 : Point3 → ℝ))
    =
  (Distribution.lineDerivCLM
      (axisDirection (h3AxisOfFin3 0)) :
      H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
      (h3WeakDistributionOfFun
        (V 1 : Point3 → ℝ))
  ∧
  (Distribution.lineDerivCLM
      (axisDirection (h3AxisOfFin3 2)) :
      H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
      (h3WeakDistributionOfFun
        (V 0 : Point3 → ℝ))
    =
  (Distribution.lineDerivCLM
      (axisDirection (h3AxisOfFin3 0)) :
      H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
      (h3WeakDistributionOfFun
        (V 2 : Point3 → ℝ))
  ∧
  (Distribution.lineDerivCLM
      (axisDirection (h3AxisOfFin3 2)) :
      H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
      (h3WeakDistributionOfFun
        (V 1 : Point3 → ℝ))
    =
  (Distribution.lineDerivCLM
      (axisDirection (h3AxisOfFin3 1)) :
      H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
      (h3WeakDistributionOfFun
        (V 2 : Point3 → ℝ))

/-! ## Each weak curl identity is a distribution identity -/

theorem h3WeakDistributionOfPhysicalScalarL2_curl01_eq_of_weakCurlFree
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hWeak :
      H3PhysicalRealFinVectorL2HilbertWeakCurlFree V) :
    (Distribution.lineDerivCLM
        (axisDirection (h3AxisOfFin3 1)) :
        H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
        (h3WeakDistributionOfFun
          (V 0 : Point3 → ℝ))
      =
    (Distribution.lineDerivCLM
        (axisDirection (h3AxisOfFin3 0)) :
        H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
        (h3WeakDistributionOfFun
          (V 1 : Point3 → ℝ)) := by
  ext ψ

  simp_rw [Distribution.lineDerivCLM_apply]

  change
    -
      h3WeakDistributionOfFun
        (V 0 : Point3 → ℝ)
        (h3WeakTestFunctionSpatialDerivative
          (h3AxisOfFin3 1)
          ψ)
      =
    -
      h3WeakDistributionOfFun
        (V 1 : Point3 → ℝ)
        (h3WeakTestFunctionSpatialDerivative
          (h3AxisOfFin3 0)
          ψ)

  rw [
    h3WeakDistributionOfPhysicalScalarL2_apply,
    h3WeakDistributionOfPhysicalScalarL2_apply
  ]

  exact
    congrArg Neg.neg
      (sub_eq_zero.mp ((hWeak ψ).1))

theorem h3WeakDistributionOfPhysicalScalarL2_curl02_eq_of_weakCurlFree
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hWeak :
      H3PhysicalRealFinVectorL2HilbertWeakCurlFree V) :
    (Distribution.lineDerivCLM
        (axisDirection (h3AxisOfFin3 2)) :
        H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
        (h3WeakDistributionOfFun
          (V 0 : Point3 → ℝ))
      =
    (Distribution.lineDerivCLM
        (axisDirection (h3AxisOfFin3 0)) :
        H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
        (h3WeakDistributionOfFun
          (V 2 : Point3 → ℝ)) := by
  ext ψ

  simp_rw [Distribution.lineDerivCLM_apply]

  change
    -
      h3WeakDistributionOfFun
        (V 0 : Point3 → ℝ)
        (h3WeakTestFunctionSpatialDerivative
          (h3AxisOfFin3 2)
          ψ)
      =
    -
      h3WeakDistributionOfFun
        (V 2 : Point3 → ℝ)
        (h3WeakTestFunctionSpatialDerivative
          (h3AxisOfFin3 0)
          ψ)

  rw [
    h3WeakDistributionOfPhysicalScalarL2_apply,
    h3WeakDistributionOfPhysicalScalarL2_apply
  ]

  exact
    congrArg Neg.neg
      (sub_eq_zero.mp ((hWeak ψ).2.1))

theorem h3WeakDistributionOfPhysicalScalarL2_curl12_eq_of_weakCurlFree
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hWeak :
      H3PhysicalRealFinVectorL2HilbertWeakCurlFree V) :
    (Distribution.lineDerivCLM
        (axisDirection (h3AxisOfFin3 2)) :
        H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
        (h3WeakDistributionOfFun
          (V 1 : Point3 → ℝ))
      =
    (Distribution.lineDerivCLM
        (axisDirection (h3AxisOfFin3 1)) :
        H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
        (h3WeakDistributionOfFun
          (V 2 : Point3 → ℝ)) := by
  ext ψ

  simp_rw [Distribution.lineDerivCLM_apply]

  change
    -
      h3WeakDistributionOfFun
        (V 1 : Point3 → ℝ)
        (h3WeakTestFunctionSpatialDerivative
          (h3AxisOfFin3 2)
          ψ)
      =
    -
      h3WeakDistributionOfFun
        (V 2 : Point3 → ℝ)
        (h3WeakTestFunctionSpatialDerivative
          (h3AxisOfFin3 1)
          ψ)

  rw [
    h3WeakDistributionOfPhysicalScalarL2_apply,
    h3WeakDistributionOfPhysicalScalarL2_apply
  ]

  exact
    congrArg Neg.neg
      (sub_eq_zero.mp ((hWeak ψ).2.2))

/-- All three ordinary distributional curl identities follow from weak
curl-freeness. -/
theorem h3PhysicalRealFinVectorL2Hilbert_distributionCurlFree_of_weakCurlFree
    {V : H3PhysicalRealFinVectorL2Hilbert}
    (hWeak :
      H3PhysicalRealFinVectorL2HilbertWeakCurlFree V) :
    H3PhysicalRealFinVectorL2HilbertDistributionCurlFree V := by
  exact
    ⟨
      h3WeakDistributionOfPhysicalScalarL2_curl01_eq_of_weakCurlFree hWeak,
      h3WeakDistributionOfPhysicalScalarL2_curl02_eq_of_weakCurlFree hWeak,
      h3WeakDistributionOfPhysicalScalarL2_curl12_eq_of_weakCurlFree hWeak
    ⟩

/-! ## Exact remaining transport frontier -/

/-- The remaining bridge is transport of ordinary distributional curl from
physical `Point3` to the tempered-distribution curl predicate on the Euclidean
Fourier carrier. -/
def H3PhysicalL2DistributionCurlFreeImpliesTemperedCurlFree : Prop :=
  ∀ V : H3PhysicalRealFinVectorL2Hilbert,
    H3PhysicalRealFinVectorL2HilbertDistributionCurlFree V →
    H3PhysicalRealFinVectorL2HilbertTemperedCurlFree V

/-- The ordinary-distribution transport theorem is sufficient for the weak-to-
tempered bridge isolated by the Fourier reduction. -/
theorem H3PhysicalL2WeakCurlFreeImpliesTemperedCurlFree_of_distributionTransport
    (hTransport :
      H3PhysicalL2DistributionCurlFreeImpliesTemperedCurlFree) :
    H3PhysicalL2WeakCurlFreeImpliesTemperedCurlFree := by
  intro V hWeak

  exact
    hTransport
      V
      (h3PhysicalRealFinVectorL2Hilbert_distributionCurlFree_of_weakCurlFree
        hWeak)

/-- Therefore the same ordinary-to-tempered transport theorem is sufficient
for full parameter-free physical Leray density. -/
theorem H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_of_distributionTransport
    (hTransport :
      H3PhysicalL2DistributionCurlFreeImpliesTemperedCurlFree) :
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan := by
  exact
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_of_temperedBridge
      (H3PhysicalL2WeakCurlFreeImpliesTemperedCurlFree_of_distributionTransport
        hTransport)

end

end Euclidean
end Bridge
end PrimeTensor
