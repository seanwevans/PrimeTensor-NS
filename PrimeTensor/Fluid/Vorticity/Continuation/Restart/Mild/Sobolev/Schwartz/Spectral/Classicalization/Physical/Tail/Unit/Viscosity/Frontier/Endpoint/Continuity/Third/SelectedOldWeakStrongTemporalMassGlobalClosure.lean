import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergyProductGlobalClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalMassReduction

/-!
# Reduce temporal product integrability to a compact-test spatial mass envelope

The global weak--strong uniqueness route has been reduced to family-level
temporal product integrability.  `TemporalMassReduction` already shows that the
full product-space Fubini hypothesis follows from a much smaller quantitative
condition for one compact weak test:

    M_i(r) = ∫ |φ_i(x) ∂ₜu_i(t+r,x)| dx ≤ C

uniformly in coordinate `i` and elapsed time `r`.

This file packages that condition for every divergence-free compact weak test,
then across the canonical restart radius and globally across every retained H³
tail.

Thus the continuation chain becomes

    compact-test temporal spatial norm-mass envelope
      -> temporal product integrability
      -> weak FTC
      -> selected/old weak-energy uniqueness
      -> endpoint continuity
      -> H3ControlProducesExtension.

No pressure hypothesis is used in this reduction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongTemporalMassGlobalClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- On one fixed elapsed interval, every divergence-free compact weak test has
a finite uniform spatial norm-mass envelope for the old temporal derivative. -/
def H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalSpatialNormMassUniformlyBoundedOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (_ht : t ∈ Set.Ioo (0 : ℝ) T)
    (_hEnd : t + tau < T)
    (_hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
      H3PreterminalLoggedVelocityTemporalSpatialNormMassUniformlyBoundedOnElapsed
        hNS t tau φ

/-- A family-level temporal spatial norm-mass envelope implies the exact
family-level product-integrability hypothesis used by the pressure-free
weak-energy route. -/
theorem H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed_of_allTemporalSpatialNormMassUniformlyBounded
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hMass :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalSpatialNormMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
      hNS ht hEnd hTail := by
  intro φ hφ q

  exact
    H3PreterminalLoggedVelocityTemporalProductIntegrableTo_of_uniformBound
      hNS
      φ
      q.property.1
      q.property.2
      (hMass φ hφ)

/-- Radius-wide temporal spatial norm-mass frontier. -/
def H3PreterminalTailUnitViscosityZeroTemporalSpatialNormMassFrontierOnRestartRadius
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E),
    ∀ hqPos : 0 < (q : ℝ),
      ∀ hEnd : t + (q : ℝ) < T,
        H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalSpatialNormMassUniformlyBoundedOnElapsed
          hNS ht hEnd hTail

/-- Global temporal spatial norm-mass frontier for every retained canonical H³
tail. -/
def H3PreterminalTailUnitViscosityZeroTemporalSpatialNormMassFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityZeroTemporalSpatialNormMassFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- Radius-wide temporal spatial norm-mass control implies the radius-wide
temporal product-integrability frontier. -/
theorem H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontierOnRestartRadius_of_temporalSpatialNormMass
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hMass :
      H3PreterminalTailUnitViscosityZeroTemporalSpatialNormMassFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontierOnRestartRadius
      E u T t hNS ht hE hTail := by
  intro q hqPos hEnd

  exact
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed_of_allTemporalSpatialNormMassUniformlyBounded
      hNS
      ht
      hEnd
      hTail
      (hMass q hqPos hEnd)

/-- Global temporal spatial norm-mass control implies the global temporal
product-integrability frontier. -/
theorem H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontier_of_temporalSpatialNormMass
    (hMass :
      H3PreterminalTailUnitViscosityZeroTemporalSpatialNormMassFrontier) :
    H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontier := by
  intro E hE u T t hNS ht hTail

  exact
    H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontierOnRestartRadius_of_temporalSpatialNormMass
      hNS
      ht
      hE
      hTail
      (hMass E hE u T t hNS ht hTail)

/-- Continuation closure reduced to the compact-test temporal spatial norm-mass
frontier alone. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroTemporalSpatialNormMassClosed
    (hMass :
      H3PreterminalTailUnitViscosityZeroTemporalSpatialNormMassFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroTemporalProductIntegrabilityClosed
      (H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontier_of_temporalSpatialNormMass
        hMass)

end

end Euclidean
end Bridge
end PrimeTensor
