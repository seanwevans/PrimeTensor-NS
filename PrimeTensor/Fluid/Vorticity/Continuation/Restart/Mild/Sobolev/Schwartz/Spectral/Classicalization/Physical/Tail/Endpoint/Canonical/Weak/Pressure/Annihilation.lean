import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Pressure.Gradient.Defect
import Mathlib.Analysis.Distribution.Distribution

/-!
# Classicalization: weak annihilation of the endpoint pressure gradient

The endpoint projected momentum equation has now been reduced to

    ∂ₛ W + P nonlinear = ΔW - ∇q,

where `q` is the scalar difference between the old preterminal pressure and the
canonical Leray-complement pressure.

The old pressure need not have any global Fourier integrability or temperate
growth.  The correct pressure-elimination mechanism is therefore the ordinary
distribution space `𝓓'`, not tempered distributions.

For any locally integrable scalar `q`, its distributional coordinate derivative
acts on a test function `φ` by

    (∂ᵢ T_q)(φ) = - T_q(∂ᵢ φ).

Consequently, for a compactly supported smooth test vector `φ = (φᵢ)`,

    Σᵢ (∂ᵢ T_q)(φᵢ)
      = - T_q(Σᵢ ∂ᵢ φᵢ).

Thus every scalar gradient distribution annihilates every divergence-free test
vector.

This file packages that generic three-dimensional fact and then specializes it
to the endpoint scalar pressure defect.  It introduces no decay hypothesis on
the old pressure and no `L²`-valued time derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalWeakPressureAnnihilation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalTailEndpointCanonicalWeakPressureAnnihilation :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Real compactly supported smooth scalar test function on physical space,
with the regularity index fixed explicitly to `⊤ : ℕ∞`. -/
abbrev H3WeakTestFunction :=
  TestFunction
    (⊤ : TopologicalSpace.Opens Point3)
    ℝ
    (⊤ : ℕ∞)

/-- Real compactly supported smooth three-component test vector on physical
space. -/
abbrev H3WeakTestVector :=
  Fin 3 → H3WeakTestFunction

/-- Scalar distribution space used by the endpoint weak-pressure argument. -/
abbrev H3WeakScalarDistribution :=
  Distribution
    (⊤ : TopologicalSpace.Opens Point3)
    ℝ
    (⊤ : ℕ∞)

/-- Function-induced scalar distribution for the mathlib revision pinned by
PrimeTensor.

The pinned revision predates `Distribution.ofFun`; the underlying continuous
functional already exists as `TestFunction.integralAgainstBilinCLM`. -/
noncomputable def h3WeakDistributionOfFun
    (q : Point3 → ℝ) :
    H3WeakScalarDistribution :=
  TestFunction.integralAgainstBilinCLM
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (volume : Measure Point3)
    q

/-- Distribution-theoretic divergence-free condition for a three-component test
vector.  This is stated directly in `TestFunction`, so compact support and
smoothness are already built into the type. -/
def H3WeakTestVectorDivergenceFree
    (φ : H3WeakTestVector) : Prop :=
  ∑ i : Fin 3,
    ((TestFunction.lineDerivCLM
      ℝ
      (axisDirection (h3AxisOfFin3 i)) :
        H3WeakTestFunction →L[ℝ] H3WeakTestFunction)
      (φ i))
    =
  (0 : H3WeakTestFunction)

/-- Any scalar distributional gradient annihilates a divergence-free
three-component test vector.

This is integration by parts at the level of `Distribution.lineDerivCLM`; no
boundary term appears because the test functions are compactly supported. -/
theorem h3DistributionGradient_pairing_eq_zero_of_testDivergenceFree
    (q : Point3 → ℝ)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    ∑ i : Fin 3,
      (((Distribution.lineDerivCLM
        (axisDirection (h3AxisOfFin3 i)) :
          H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
        (h3WeakDistributionOfFun q))
        (φ i))
      =
    0 := by
  let T : H3WeakScalarDistribution :=
    h3WeakDistributionOfFun q

  change
    ∑ i : Fin 3,
      (((Distribution.lineDerivCLM
        (axisDirection (h3AxisOfFin3 i)) :
          H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
        T)
        (φ i))
      =
    0

  simp_rw [Distribution.lineDerivCLM_apply]

  calc
    (∑ i : Fin 3,
      - T
        (((TestFunction.lineDerivCLM
          ℝ
          (axisDirection (h3AxisOfFin3 i)) :
            H3WeakTestFunction →L[ℝ] H3WeakTestFunction)
          (φ i))))
        =
      -
      (∑ i : Fin 3,
        T
          (((TestFunction.lineDerivCLM
            ℝ
            (axisDirection (h3AxisOfFin3 i)) :
              H3WeakTestFunction →L[ℝ] H3WeakTestFunction)
            (φ i)))) := by
      simp
    _ =
      -
      T
        (∑ i : Fin 3,
          ((TestFunction.lineDerivCLM
            ℝ
            (axisDirection (h3AxisOfFin3 i)) :
              H3WeakTestFunction →L[ℝ] H3WeakTestFunction)
            (φ i))) := by
      rw [map_sum]
    _ = 0 := by
      have hφ' :
          (∑ i : Fin 3,
            ((TestFunction.lineDerivCLM
              ℝ
              (axisDirection (h3AxisOfFin3 i)) :
                H3WeakTestFunction →L[ℝ] H3WeakTestFunction)
              (φ i)))
            =
          (0 : H3WeakTestFunction) := by
        simpa only [H3WeakTestVectorDivergenceFree] using hφ
      rw [hφ']
      simp

/-- The endpoint scalar pressure defect is locally integrable on physical
space.  This records that the local integral functional used below is the
genuine function-induced distribution rather than its fallback zero branch. -/
theorem h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint_locallyIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) tau) :
    LocallyIntegrable
      (h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint s)
      (volume : Measure Point3) := by
  have hC1 :=
    h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint_spatialC1
      hNS ht htau hEnd hE hTail hEndpoint hs

  exact hC1.continuous.locallyIntegrable

/-- The distributional gradient of the endpoint scalar pressure defect
annihilates every divergence-free compactly supported smooth test vector. -/
theorem h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint_distributionGradient_pairing_eq_zero
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) tau)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    ∑ i : Fin 3,
      (((Distribution.lineDerivCLM
        (axisDirection (h3AxisOfFin3 i)) :
          H3WeakScalarDistribution →L[ℝ] H3WeakScalarDistribution)
        (h3WeakDistributionOfFun
          (h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint
            hNS ht htau.le hEnd hE hTail hEndpoint s)))
        (φ i))
      =
    0 := by
  have hLocal :
      LocallyIntegrable
        (h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint s)
        (volume : Measure Point3) :=
    h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint_locallyIntegrable
      hNS ht htau hEnd hE hTail hEndpoint hs

  have hLocalOn :
      LocallyIntegrableOn
        (h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint s)
        Set.univ
        (volume : Measure Point3) :=
    hLocal.locallyIntegrableOn Set.univ

  -- `hLocalOn` records that `h3WeakDistributionOfFun` is the genuine integral
  -- functional rather than the fallback zero branch of
  -- `TestFunction.integralAgainstBilinCLM`.
  exact
    h3DistributionGradient_pairing_eq_zero_of_testDivergenceFree
      (h3PreterminalTailCanonicalNormalizedRealPressureScalarDefectOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint s)
      φ
      hφ

end

end Euclidean
end Bridge
end PrimeTensor
