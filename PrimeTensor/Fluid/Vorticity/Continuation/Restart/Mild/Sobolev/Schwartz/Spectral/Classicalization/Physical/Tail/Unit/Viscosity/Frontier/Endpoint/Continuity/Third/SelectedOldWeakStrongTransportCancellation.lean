import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongTransportSplit
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.IntegrationByParts.Closure

/-!
# Selected--old weak--strong pure transport cancellation

The pointwise convection difference is already split as

    (S · ∇)S - (O · ∇)O
      = ((S - O) · ∇)S + O · ∇(S - O).

This file kills the second term in the relative-energy pairing.

The existing H³ transport infrastructure contains the generic scalar theorem

    ∫ f (v · ∇f) = 0

for an incompressible preterminal Navier--Stokes velocity `v`, provided the
whole-space scalar flux vanishes.  The theorem is genuinely generic in `f`.
Consequently it applies directly to each selected-minus-old component

    D_j = S_j - O_j.

We first identify the explicit weak--strong term introduced in the preceding
file with `h3ScalarTransport O t D_j`, then specialize the existing scalar
transport cancellation.  A second wrapper consumes the stronger honest
integration-by-parts datum `TransportScalarIntegrationByPartsAt`.

No Leray projection and no estimate of `((S-O) · ∇)S` is performed here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongTransportCancellation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One selected-minus-old scalar velocity component. -/
noncomputable def selectedOldVelocityDifferenceComponent
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    (selected t x).component j
      -
    (old t x).component j

/-- The explicit old-velocity transport term from the weak--strong split is
exactly the generic scalar transport of the corresponding difference
component. -/
theorem realAdvectionOldTransportDifferenceComponent_eq_scalarTransport
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    (fun x =>
      realAdvectionOldTransportDifferenceComponent
        selected old t x j)
      =
    h3ScalarTransport
      old t
      (selectedOldVelocityDifferenceComponent
        selected old t j) := by
  funext x
  unfold
    realAdvectionOldTransportDifferenceComponent
    selectedOldVelocityDifferenceComponent
    h3ScalarTransport
  rfl

/-- Spatial `C¹` regularity of one selected-minus-old component. -/
theorem selectedOldVelocityDifferenceComponent_spatialC1
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three)
    (hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x =>
            (selected t x).component k))
    (hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x =>
            (old t x).component k)) :
    SpatialC1
      (selectedOldVelocityDifferenceComponent
        selected old t j) := by
  unfold selectedOldVelocityDifferenceComponent
  exact
    (hSelected j).sub (hOld j)

/-- Componentwise weak--strong pure-transport cancellation in flux form:

    ∫ D_j (O · ∇D_j) = 0.

This is the term that disappears by old-branch incompressibility. -/
theorem spatialEnergyPairing_oldTransportDifference_eq_zero
    {selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three}
    {p :
      PrimeTensor.SpaceTimeScalarField ℝ ℝ ℝ Depth.three}
    {T t : ℝ}
    (s : PreterminalNavierStokes3 old p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (j : PrimeTensor.Axis Depth.three)
    (hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x =>
            (selected t x).component k))
    (hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x =>
            (old t x).component k))
    (hFlux :
      TransportScalarFluxVanishesAt
        old t
        (selectedOldVelocityDifferenceComponent
          selected old t j)) :
    spatialEnergyPairing
        (selectedOldVelocityDifferenceComponent
          selected old t j)
        (fun x =>
          realAdvectionOldTransportDifferenceComponent
            selected old t x j)
      =
    0 := by
  rw [
    realAdvectionOldTransportDifferenceComponent_eq_scalarTransport
      selected old t j
  ]

  exact
    spatialEnergyPairing_scalarTransport_eq_zero
      s ht
      (selectedOldVelocityDifferenceComponent_spatialC1
        selected old t j hSelected hOld)
      hFlux

/-- The same cancellation consuming the honest whole-space
integration-by-parts datum.  This is the preferred interface for the concrete
selected/old specialization. -/
theorem spatialEnergyPairing_oldTransportDifference_eq_zero_of_integrationByParts
    {selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three}
    {p :
      PrimeTensor.SpaceTimeScalarField ℝ ℝ ℝ Depth.three}
    {T t : ℝ}
    (s : PreterminalNavierStokes3 old p T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (j : PrimeTensor.Axis Depth.three)
    (hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x =>
            (selected t x).component k))
    (hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x =>
            (old t x).component k))
    (hIBP :
      TransportScalarIntegrationByPartsAt
        old t
        (selectedOldVelocityDifferenceComponent
          selected old t j)) :
    spatialEnergyPairing
        (selectedOldVelocityDifferenceComponent
          selected old t j)
        (fun x =>
          realAdvectionOldTransportDifferenceComponent
            selected old t x j)
      =
    0 := by
  exact
    spatialEnergyPairing_oldTransportDifference_eq_zero
      s ht j hSelected hOld hIBP.2

end

end Euclidean
end Bridge
end PrimeTensor
