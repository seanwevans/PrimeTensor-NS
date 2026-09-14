import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalJointMeasurable
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Integrable
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.TemporalMassIntegrable

/-!
# Zeroth-order endpoint continuity: reduce old temporal Fubini to one mass envelope

`TemporalJointMeasurable` closed the product-space measurability half of the
endpoint-independent old temporal derivative.

This file isolates the remaining finiteness input in the smallest form useful
for the weak FTC argument.

For one compact smooth weak-test vector `φ`, define the coordinatewise spatial
mass

    M_i(r) = ∫_x ‖φ_i(x) ∂ₜu_i(t+r,x)‖ dx.

The exact remaining quantitative obligation is simply a finite constant `C`
such that

    M_i(r) ≤ C

for every coordinate and every elapsed time in the open interval.

Once such a constant exists:

1. `TemporalJointMeasurable` gives a.e.-strong measurability of every `M_i`;
2. finite interval measure plus the uniform bound gives time integrability;
3. the generic Carathéodory/Fubini reduction already developed for vorticity
   upgrades that scalar mass integrability to full product-space integrability
   of `(r,x) ↦ φ_i(x) ∂ₜu_i(t+r,x)`.

No endpoint continuity, pointwise spacetime domination, or joint continuity is
introduced here.  The next file may therefore perform Fubini under exactly this
single mass-envelope frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldTemporalMassReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroOldTemporalMassReduction :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Exact remaining scalar mass-envelope condition for one compact weak-test
vector on the complete elapsed interval. -/
def H3PreterminalLoggedVelocityTemporalSpatialNormMassUniformlyBoundedOnElapsed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t tau : ℝ)
    (φ : H3WeakTestVector) : Prop :=
  ∃ C : ℝ,
    ∀ (i : Fin 3) (r : ℝ),
      r ∈ Set.Ioo (0 : ℝ) tau →
      h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed
          hNS t i (φ i) r
        ≤
      C

/-- Coordinatewise scalar mass integrability required by product-space Fubini. -/
def H3PreterminalLoggedVelocityTemporalSpatialNormMassIntegrableTo
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t q : ℝ)
    (φ : H3WeakTestVector) : Prop :=
  ∀ i : Fin 3,
    Integrable
      (h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed
        hNS t i (φ i))
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q))

/-- Coordinatewise product-space integrability required to commute the old
temporal derivative through compact testing. -/
def H3PreterminalLoggedVelocityTemporalProductIntegrableTo
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t q : ℝ)
    (φ : H3WeakTestVector) : Prop :=
  ∀ i : Fin 3,
    Integrable
      (fun z : ℝ × Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i z.2)
          (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
            hNS i (t + z.1) z.2))
      (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) q)).prod
        (volume : Measure Point3))

/-- Every old temporal spatial norm mass is nonnegative. -/
theorem h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (i : Fin 3)
    (ψ : H3WeakTestFunction)
    (r : ℝ) :
    0 ≤
      h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed
        hNS t i ψ r := by
  unfold
    h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed

  exact
    integral_nonneg
      (fun x : Point3 =>
        norm_nonneg
          ((ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
              hNS i (t + r) x)))

/-- A uniform spatial-mass envelope on `[0,tau]` gives coordinatewise time
integrability on every shortened target `q ≤ tau`. -/
theorem H3PreterminalLoggedVelocityTemporalSpatialNormMassIntegrableTo_of_uniformBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (φ : H3WeakTestVector)
    (hq0 : 0 ≤ q)
    (hqtau : q ≤ tau)
    (hBound :
      H3PreterminalLoggedVelocityTemporalSpatialNormMassUniformlyBoundedOnElapsed
        hNS t tau φ) :
    H3PreterminalLoggedVelocityTemporalSpatialNormMassIntegrableTo
      hNS t q φ := by
  rcases hBound with ⟨C, hC⟩

  intro i

  apply
    integrable_restrict_Ioo_of_aestronglyMeasurable_of_nonneg_of_le
      q C
      (h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed_aestronglyMeasurable
        hNS i (φ i))

  · intro r

    exact
      h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed_nonneg
        hNS i (φ i) r

  · intro r hr

    have hrTau :
        r ∈ Set.Ioo (0 : ℝ) tau := by
      exact
        ⟨
          hr.1,
          lt_of_lt_of_le hr.2 hqtau
        ⟩

    exact hC i r hrTau

/-- Joint measurability plus coordinatewise scalar mass integrability gives the
full product-space integrability needed by Fubini. -/
theorem H3PreterminalLoggedVelocityTemporalProductIntegrableTo_of_spatialNormMassIntegrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (t q : ℝ)
    (φ : H3WeakTestVector)
    (hMass :
      H3PreterminalLoggedVelocityTemporalSpatialNormMassIntegrableTo
        hNS t q φ) :
    H3PreterminalLoggedVelocityTemporalProductIntegrableTo
      hNS t q φ := by
  intro i

  exact
    h3WeakTest_continuousMapExtension_productIntegrable_of_spatialNormMassIntegrable
      (φ i)
      (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
        hNS i)
      (measurable_h3LoggedPreterminalVelocity_temporalDerivative_joint
        hNS i)
      t q
      (hMass i)

/-- A single uniform compact-test mass envelope therefore closes every
coordinatewise product-integrability requirement on every shortened elapsed
target. -/
theorem H3PreterminalLoggedVelocityTemporalProductIntegrableTo_of_uniformBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (φ : H3WeakTestVector)
    (hq0 : 0 ≤ q)
    (hqtau : q ≤ tau)
    (hBound :
      H3PreterminalLoggedVelocityTemporalSpatialNormMassUniformlyBoundedOnElapsed
        hNS t tau φ) :
    H3PreterminalLoggedVelocityTemporalProductIntegrableTo
      hNS t q φ := by
  apply
    H3PreterminalLoggedVelocityTemporalProductIntegrableTo_of_spatialNormMassIntegrable
      hNS t q φ

  exact
    H3PreterminalLoggedVelocityTemporalSpatialNormMassIntegrableTo_of_uniformBound
      hNS φ hq0 hqtau hBound

end

end Euclidean
end Bridge
end PrimeTensor
