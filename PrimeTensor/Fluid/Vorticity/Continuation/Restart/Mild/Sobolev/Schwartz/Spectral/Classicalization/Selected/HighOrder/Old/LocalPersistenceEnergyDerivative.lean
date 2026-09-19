import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.HighOrder.Old.LocalPersistenceContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.EnergyDerivativeAssembly

/-!
# Close seed-level canonical H³-energy right continuity from derivative inputs

`Old.LocalPersistenceContinuity` split the local H³ persistence problem into

1. qualitative persistence of H³ integrability;
2. right continuity of the canonical H³ energy.

The second item is already accessible through the existing orderwise energy
derivative machinery.

At one H³-integrable interior slice, it is enough to have

* the order-two mixed time/space derivative field;
* the order-three mixed time/space derivative field;
* the four local dominated-integral packages collected in
  `H3EnergyDerivativeDominationDataAt`.

Orders zero and one need no additional mixed-time hypothesis because those
derivatives are already built into `PreterminalVorticityRegularity3`.

`h3OrderEnergyDerivativeIdentities_of_integrable_of_tailInputs` assembles these
inputs into the four exact energy-block derivatives, and
`hasDerivAt_velocityH3EnergyAt` gives differentiability of the full normalized
canonical H³ energy.  Differentiability implies continuity, hence the explicit
right-epsilon formulation used by the local persistence reduction.

After this file, the only remaining seed-level local persistence input is

    H3IntegrableSlicePersistsLocally.

No new PDE estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SeedEnergyRightContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Exact derivative-side data required at every H³-integrable interior slice.

This proposition deliberately does not assume an energy class or a terminal H³
tail.  It is a pointwise-in-time analytic interface.
-/
def H3IntegrableSliceHasEnergyDerivativeInputs : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ),
      LoggedPreterminalNavierStokesAdmissible u T →
      t ∈ Set.Ioo (0 : ℝ) T →
      VelocityH3IntegrableAt u t →
      H3Order2VelocityMixedTimeDerivativeOnPreterminal u T
        ∧
      H3Order3VelocityMixedTimeDerivativeOnPreterminal u T
        ∧
      Nonempty
        (H3EnergyDerivativeDominationDataAt u T t)

/--
The existing orderwise derivative machinery closes right continuity of the
canonical H³ energy at every H³-integrable interior slice.
-/
theorem h3EnergyRightContinuousAtIntegrableSlice_of_derivativeInputs
    (hInputs : H3IntegrableSliceHasEnergyDerivativeInputs) :
    H3EnergyRightContinuousAtIntegrableSlice := by

  intro u T t hNS ht hInt ε hε

  rcases
    hInputs u T t hNS ht hInt
  with
    ⟨
      hMixed2,
      hMixed3,
      ⟨hDom⟩
    ⟩

  have hIdentities :
      H3OrderEnergyDerivativeIdentities u t :=
    h3OrderEnergyDerivativeIdentities_of_integrable_of_tailInputs
      hNS
      ht
      hInt
      hMixed2
      hMixed3
      hDom

  have hContinuous :
      ContinuousAt
        (velocityH3EnergyAt u)
        t :=
    (hasDerivAt_velocityH3EnergyAt
      hIdentities).continuousAt

  rcases
    (Metric.continuousAt_iff.mp hContinuous)
      ε hε
  with
    ⟨
      δ,
      hδ,
      hNear
    ⟩

  refine
    ⟨
      δ,
      hδ,
      ?_
    ⟩

  intro s hts _hsT hsδ

  have hdist :
      dist s t < δ := by
    rw [Real.dist_eq]
    rw [abs_of_nonneg (sub_nonneg.mpr hts)]
    linarith

  have hEnergyDist :
      dist
          (velocityH3EnergyAt u s)
          (velocityH3EnergyAt u t)
        <
      ε :=
    hNear hdist

  simpa only [Real.dist_eq] using hEnergyDist

/--
Therefore local H³-integrability persistence plus the already-isolated
derivative inputs yields the exact canonical `2E` local H³ tail.
-/
theorem h3IntegrableSliceProducesLocalCanonicalH3Tail_of_persistence_of_derivativeInputs
    (hPersist : H3IntegrableSlicePersistsLocally)
    (hInputs : H3IntegrableSliceHasEnergyDerivativeInputs) :
    H3IntegrableSliceProducesLocalCanonicalH3Tail := by

  exact
    h3IntegrableSliceProducesLocalCanonicalH3Tail_of_persistence_of_energyRightContinuous
      hPersist
      (h3EnergyRightContinuousAtIntegrableSlice_of_derivativeInputs
        hInputs)

/--
The same reduction gives local old-branch C5/C4 regularization from every H³
seed.

At this point the seed-side local smoothing route depends only on

* qualitative local H³-integrability persistence;
* the explicit order-two/order-three mixed-time and dominated-integral inputs.
-/
theorem h3SeedProducesLocalEnergyClass_of_persistence_of_derivativeInputs
    (hPersist : H3IntegrableSlicePersistsLocally)
    (hInputs : H3IntegrableSliceHasEnergyDerivativeInputs) :
    H3SeedProducesLocalEnergyClass := by

  exact
    h3SeedProducesLocalEnergyClass_of_localCanonicalH3Persistence
      (h3IntegrableSliceProducesLocalCanonicalH3Tail_of_persistence_of_derivativeInputs
        hPersist
        hInputs)

end

end Euclidean
end Bridge
end PrimeTensor
