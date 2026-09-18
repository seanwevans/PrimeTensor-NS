import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Flux.DivergenceIntegrability
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Preterminal.Spectral.Slice
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Envelope

/-!
# Pointwise velocity envelope for the Landau top-flux closure

The remaining top-order transport boundary term contains

    uᵣ (D³uⱼ)².

The third derivative is already in `L²`.  To place this flux coordinate in
`L¹`, the missing factor is a pointwise bound for the velocity itself.

This file derives that bound from the canonical weighted H³ spectral encoding
of one preterminal energy-class slice.  The argument is downstream of the H³
energy tree so that the spectral restart/classicalization machinery is not
imported back into the energy core.

For one strict energy-class tail time:

* H³ integrability plus preterminal regularity canonically builds the weighted
  spectral state;
* its norm is bounded by the normalized physical H³ energy;
* the real `C¹` spectral representative has a point-evaluation bound;
* almost-everywhere agreement with the original logged velocity upgrades to
  pointwise agreement because both representatives are continuous.

No new analytic frontier is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeLandauTopFluxVelocityEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
At every strict time in an H³ energy-class tail, each logged velocity component
is bounded pointwise by the canonical H³ spectral point-evaluation constant
times the normalized H³ energy.
-/
theorem norm_loggedVelocityComponent_le_h3Energy
    {
      u :
        SpaceTimeVectorField
          ℝ ℝ MulReal Depth.three
    }
    {a T t : ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (j : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    ‖loggedVelocityComponent u t j x‖
      ≤
    h3RawFourierL1DeweightingCoefficient
      *
    velocityH3EnergyAt u t := by

  rcases hClass.pressure_witness with
    ⟨p, hPDE, hp4⟩

  have htNS :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans
        hClass.terminal_start.1
        ht.1,
      ht.2
    ⟩

  let hNS :
      LoggedPreterminalNavierStokesAdmissible
        u T :=
    ⟨p, hPDE⟩

  let hMeas :
      VelocityH3MeasurableAt
        u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS htNS

  let hFourier :
      VelocityH3FourierCompatibleAt
        u t hH3 hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS htNS hH3

  let U : H3SpectralVelocityState :=
    velocityH3SpectralStateAt
      u t hH3 hMeas hFourier

  let k : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have hAE0 :=
    h3SpectralVelocityRealC1RepresentativeOnPoint3_velocityH3SpectralStateAt_ae_eq_loggedVelocityComponent
      hFourier k

  have hAE :
      h3SpectralScalarRealC1RepresentativeOnPoint3
          (U k)
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u t j := by

    dsimp only [U, k] at hAE0 ⊢

    simpa only [
      h3SpectralVelocityRealC1RepresentativeOnPoint3,
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
    ] using hAE0

  have hSpectralContinuous :
      Continuous
        (
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (U k)
        ) := by

    exact
      (
        h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one
          (U k)
      ).continuous

  have hOldContinuous :
      Continuous
        (
          loggedVelocityComponent
            u t j
        ) := by

    unfold loggedVelocityComponent

    exact
      (
        hPDE.regularity.velocity_spatial_three
          t htNS j
      ).continuous

  have hPointwise :
      h3SpectralScalarRealC1RepresentativeOnPoint3
          (U k)
        =
      loggedVelocityComponent
        u t j :=
    MeasureTheory.Measure.eq_of_ae_eq
      hAE
      hSpectralContinuous
      hOldContinuous

  have hEvaluation :
      ‖h3SpectralScalarRealC1RepresentativeOnPoint3
          (U k) x‖
        ≤
      h3RawFourierL1DeweightingCoefficient
        *
      ‖U k‖ :=
    norm_h3SpectralScalarRealC1RepresentativeOnPoint3_apply_le
      (U k) x

  have hCoordinate :
      ‖U k‖ ≤ ‖U‖ :=
    h3SpectralFinVector_coordinate_norm_le
      U k

  have hState :
      ‖U‖
        ≤
      velocityH3EnergyAt u t := by

    dsimp only [U]

    exact
      norm_velocityH3SpectralStateAt_le_energyCeiling
        hFourier
        (one_le_velocityH3EnergyAt u t)
        le_rfl

  have hScalar :
      ‖U k‖
        ≤
      velocityH3EnergyAt u t :=
    hCoordinate.trans hState

  have hBound :
      ‖h3SpectralScalarRealC1RepresentativeOnPoint3
          (U k) x‖
        ≤
      h3RawFourierL1DeweightingCoefficient
        *
      velocityH3EnergyAt u t :=
    hEvaluation.trans
      (
        mul_le_mul_of_nonneg_left
          hScalar
          h3RawFourierL1DeweightingCoefficient_nonneg
      )

  have hx :
      h3SpectralScalarRealC1RepresentativeOnPoint3
          (U k) x
        =
      loggedVelocityComponent
        u t j x :=
    congrFun hPointwise x

  rw [← hx]

  exact hBound

/--
Uniform componentwise form of the preceding estimate.  This is the shape
consumed by the top-order scalar-flux `L¹` argument.
-/
theorem loggedVelocityComponents_bounded_of_h3Energy
    {
      u :
        SpaceTimeVectorField
          ℝ ℝ MulReal Depth.three
    }
    {a T t : ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    ) :
    ∀
      (j : PrimeTensor.Axis Depth.three)
      (x : Point3),
        ‖loggedVelocityComponent u t j x‖
          ≤
        h3RawFourierL1DeweightingCoefficient
          *
        velocityH3EnergyAt u t := by

  intro j x

  exact
    norm_loggedVelocityComponent_le_h3Energy
      hClass ht hH3 j x

end

end Euclidean
end Bridge
end PrimeTensor
