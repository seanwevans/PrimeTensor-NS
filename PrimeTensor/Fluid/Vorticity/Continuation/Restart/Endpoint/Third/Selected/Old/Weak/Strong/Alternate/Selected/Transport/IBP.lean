import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Alternate.Forcing.Pairing.Bound
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.IntegrationByParts.Closure

/-!
# Honest selected-transport IBP package for the alternate weak--strong split

The alternate relative-energy route has reduced the spatial transport seam to
two facts for each difference component `D_j`:

* the selected scalar flux has zero whole-space integral;
* the selected pure-transport energy density is integrable.

Those are not independent analytic assumptions.  The honest whole-space datum

    Integrable (div (S D_j²))
      ∧
    ∫ div (S D_j²) = 0

contains both.  Pointwise incompressibility of the selected restart gives

    div (S D_j²) = 2 D_j (S · ∇D_j),

so integrability of the flux divergence immediately implies integrability of
the pure-transport pairing.

This file packages exactly that fact and reconnects it to the alternate
forcing estimate.  The downstream theorem now has one spatial hypothesis
instead of a separate flux and pairing-integrability pair.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

attribute [local instance]
  point3MeasureSpaceH3SelectedOldWeakStrongTransportIntegralBound

noncomputable local instance axisFintypeH3SelectedOldWeakStrongAlternateSelectedTransportIBP
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Honest scalar-transport IBP implies pure-transport pairing integrability
for any spatially `C¹`, pointwise incompressible transporting velocity.

This is the pressure-free analogue of
`transportScalarPairingIntegrable_of_integrationByParts`, specialized only to
the structural facts actually used in its proof. -/
theorem scalarTransportPairingIntegrable_of_integrationByParts_of_divergenceFree
    (v :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    {f : ScalarField3}
    (hv :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun q : Point3 =>
            (v t q).component k))
    (hDiv :
      ∀ x : Point3,
        PrimeTensor.Bridge.RealFluid.divergence
            spatial3 (v t) x
          =
        0)
    (hf : SpatialC1 f)
    (hIBP :
      TransportScalarIntegrationByPartsAt
        v t f) :
    Integrable
      (fun x : Point3 =>
        f x * h3ScalarTransport v t f x)
      (volume : Measure Point3) := by
  have hPointwise :
      (fun x : Point3 =>
        transportScalarFluxDivergenceXYZ
          v t f x)
        =
      (fun x : Point3 =>
        2 * (f x * h3ScalarTransport v t f x)) := by
    funext x

    simpa [mul_assoc] using
      transportScalarFluxDivergenceXYZ_eq_two_mul_transport_of_divergenceFree
        v t hv hDiv hf x

  have hTwice :
      Integrable
        (fun x : Point3 =>
          2 * (f x * h3ScalarTransport v t f x))
        (volume : Measure Point3) := by
    rw [← hPointwise]

    exact hIBP.1

  have hHalf :
      Integrable
        (fun x : Point3 =>
          (1 / 2 : ℝ) *
            (2 * (f x * h3ScalarTransport v t f x)))
        (volume : Measure Point3) :=
    hTwice.const_mul (1 / 2 : ℝ)

  have hEq :
      (fun x : Point3 =>
        (1 / 2 : ℝ) *
          (2 * (f x * h3ScalarTransport v t f x)))
        =
      (fun x : Point3 =>
        f x * h3ScalarTransport v t f x) := by
    funext x
    ring

  rw [hEq] at hHalf

  exact hHalf

/-- Honest selected-transport whole-space integration-by-parts datum for every
selected-minus-old difference component at one elapsed time. -/
def H3PreterminalSelectedOldWeakStrongSelectedTransportIntegrationByPartsAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) : Prop :=
  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity
      u t

  ∀ j : PrimeTensor.Axis Depth.three,
    TransportScalarIntegrationByPartsAt
      selected
      (q : ℝ)
      (selectedOldVelocityDifferenceComponent
        selected old (q : ℝ) j)

/-- Forget the explicit integrability field and recover the selected
scalar-flux cancellation predicate used by the alternate cancellation theorem.
-/
theorem h3PreterminalSelectedOldWeakStrongSelectedTransportFluxVanishesAt_of_integrationByParts
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (hIBP :
      H3PreterminalSelectedOldWeakStrongSelectedTransportIntegrationByPartsAt
        hNS ht hEnd hE hTail q) :
    H3PreterminalSelectedOldWeakStrongSelectedTransportFluxVanishesAt
      hNS ht hEnd hE hTail q := by
  intro j

  exact
    (hIBP j).2

/-- The same honest selected-transport IBP datum automatically gives every
pure-transport pairing-integrability fact required to split the alternate
convection integral. -/
theorem h3PreterminalSelectedOldWeakStrongSelectedTransportPairingIntegrableAt_of_integrationByParts
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau)
    (hIBP :
      H3PreterminalSelectedOldWeakStrongSelectedTransportIntegrationByPartsAt
        hNS ht hEnd hE hTail q) :
    H3PreterminalSelectedOldWeakStrongSelectedTransportPairingIntegrableAt
      hNS ht hEnd hE hTail q := by
  let selected :=
    h3PreterminalSelectedWeakStrongVelocity
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail

  let old :=
    h3PreterminalOldElapsedWeakStrongVelocity
      u t

  intro j

  have hSelected :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (selected (q : ℝ) x).component k) := by
    intro k
    dsimp only [selected]

    exact
      h3PreterminalSelectedWeakStrongVelocity_component_spatialC1
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail (q : ℝ) k

  have hOld :
      ∀ k : PrimeTensor.Axis Depth.three,
        SpatialC1
          (fun x : Point3 =>
            (old (q : ℝ) x).component k) := by
    intro k
    dsimp only [old]

    exact
      h3PreterminalOldElapsedWeakStrongVelocity_component_spatialC1
        hNS ht hEnd hTail q k

  have hf :
      SpatialC1
        (selectedOldVelocityDifferenceComponent
          selected old (q : ℝ) j) :=
    selectedOldVelocityDifferenceComponent_spatialC1
      selected old (q : ℝ) j
      hSelected hOld

  have hDiv :
      ∀ x : Point3,
        PrimeTensor.Bridge.RealFluid.divergence
            spatial3 (selected (q : ℝ)) x
          =
        0 := by
    intro x
    dsimp only [selected]

    exact
      h3PreterminalSelectedWeakStrongVelocity_divergence_eq_zero
        hNS ht hEnd hE hTail htauR q x

  have hPair :
      Integrable
        (fun x : Point3 =>
          selectedOldVelocityDifferenceComponent
              selected old (q : ℝ) j x
            *
          h3ScalarTransport
              selected
              (q : ℝ)
              (selectedOldVelocityDifferenceComponent
                selected old (q : ℝ) j)
              x)
        (volume : Measure Point3) :=
    scalarTransportPairingIntegrable_of_integrationByParts_of_divergenceFree
      selected
      (q : ℝ)
      hSelected
      hDiv
      hf
      (hIBP j)

  have hTransportEq :=
    realAdvectionSelectedTransportDifferenceComponent_eq_scalarTransport
      selected old (q : ℝ) j

  change
    Integrable
      (fun x : Point3 =>
        ((selected (q : ℝ) x).component j
            -
          (old (q : ℝ) x).component j)
          *
        realAdvectionSelectedTransportDifferenceComponent
          selected old (q : ℝ) x j)
      (volume : Measure Point3)

  change
    Integrable
      (fun x : Point3 =>
        selectedOldVelocityDifferenceComponent
            selected old (q : ℝ) j x
          *
        realAdvectionSelectedTransportDifferenceComponent
          selected old (q : ℝ) x j)
      (volume : Measure Point3)

  rw [← hTransportEq] at hPair

  exact hPair

/-- The alternate nonlinear forcing estimate now requires only one honest
selected whole-space IBP datum. -/
theorem neg_two_inner_selectedOldUnitLerayForcingDifference_le_six_mul_norm_sq_alternate_of_selectedTransportIBP
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (q : Set.Icc (0 : ℝ) tau)
    (hIBP :
      H3PreterminalSelectedOldWeakStrongSelectedTransportIntegrationByPartsAt
        hNS ht hEnd hE hTail q) :
    -2 *
      inner ℝ
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q)
        (h3PreterminalSelectedOldUnitLerayForcingDifferenceOnElapsed
          hNS ht hEnd hE hTail htauR q)
      ≤
    6 * h3PreterminalSelectedWeakStrongGradientEnvelope E *
      ‖h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q‖ ^ 2 := by
  have hFlux :=
    h3PreterminalSelectedOldWeakStrongSelectedTransportFluxVanishesAt_of_integrationByParts
      hNS ht hEnd hE hTail q hIBP

  have hPairing :=
    h3PreterminalSelectedOldWeakStrongSelectedTransportPairingIntegrableAt_of_integrationByParts
      hNS ht hEnd hE hTail htauR q hIBP

  exact
    neg_two_inner_selectedOldUnitLerayForcingDifference_le_six_mul_norm_sq_alternate
      hNS ht hEnd hE hTail htauR q
      hFlux hPairing

end

end Euclidean
end Bridge
end PrimeTensor
