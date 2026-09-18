import PrimeTensor.Fluid.Vorticity.Continuation.Landau.TopFlux.CutoffLimit
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Flux.DivergenceIntegrability

/-!
# Automatic top-order H³ transport-flux cancellation

The previous top-flux increments established the two global facts needed for
an expanding-cutoff divergence argument:

* every coordinate of `u (D³uⱼ)²` is in `L¹`;
* the recombined total divergence of that vector flux is in `L¹`.

`CutoffLimit` then proved the generic theorem that an integrable `C¹` vector
flux with integrable total divergence has zero whole-space divergence integral,
without requiring the individual coordinate derivatives of the flux to lie in
`L¹`.

This file specializes that theorem to the third-order H³ transport flux.
Consequently the old top-order boundary predicate is no longer an independent
analytic hypothesis once the local H³/PDE pairing data used to prove total
divergence integrability are available.

No fourth spatial derivative is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeLandauTopFluxAutomatic
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Canonical H³ data, PDE pairing integrability, and the two third-order
commutator-pairing integrability packages force the top-order scalar transport
flux to vanish at infinity.
-/
theorem h3ThirdDerivativeTransportFluxVanishesAt_of_pde
    {
      u :
        SpaceTimeVectorField
          ℝ ℝ MulReal Depth.three
    }
    {
      p :
        SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
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
    (
      hPDE :
        H3PDEPairingIntegrableAt
          u p t
    )
    (
      hGradientPairing :
        H3OrderThreeGradientPairingIntegrableAt
          u t
    )
    (
      hInterpolationPairing :
        H3OrderThreeInterpolationPairingIntegrableAt
          u t
    ) :
    H3ThirdDerivativeTransportFluxVanishesAt
      u t := by

  rcases hClass.pressure_witness with
    ⟨p₀, s, hp4⟩

  have htNS :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans
        hClass.terminal_start.1
        ht.1,
      ht.2
    ⟩

  have hRegular :
      H3OrderThreeTransportRegularityAt
        u t :=
    h3OrderThreeTransportRegularityAt_of_energyClass
      hClass
      ht

  have hCoordinates :
      H3ThirdDerivativeTransportFluxCoordinateIntegrableAt
        u t :=
    h3ThirdDerivativeTransportFluxCoordinate_integrable_of_h3Energy
      hClass
      ht
      hH3

  have hDivergence :
      H3ThirdDerivativeTransportFluxDivergenceIntegrableAt
        u t :=
    h3ThirdDerivativeTransportFluxDivergence_integrable_of_pde
      hClass
      ht
      hPDE
      hGradientPairing
      hInterpolationPairing

  intro i k l j

  have hComponentEq :
      loggedVelocityComponent u t j
        =
      (
        fun q : Point3 =>
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u t q
          ).component j
      ) := by
    rfl

  let f : ScalarField3 :=
    spatial3.d
      i
      (
        spatial3.d
          k
          (
            spatial3.d
              l
              (
                fun q : Point3 =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t q
                  ).component j
              )
          )
      )

  let Fx : ScalarField3 :=
    fun x : Point3 =>
      (
        PrimeTensor.Bridge.logSpaceTimeVectorField
          u t x
      ).component xAxis
        *
      (f x * f x)

  let Fy : ScalarField3 :=
    fun x : Point3 =>
      (
        PrimeTensor.Bridge.logSpaceTimeVectorField
          u t x
      ).component yAxis
        *
      (f x * f x)

  let Fz : ScalarField3 :=
    fun x : Point3 =>
      (
        PrimeTensor.Bridge.logSpaceTimeVectorField
          u t x
      ).component zAxis
        *
      (f x * f x)

  have hVx :
      SpatialC1
        (
          fun x : Point3 =>
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u t x
            ).component xAxis
        ) :=
    s.velocity_component_spatialC1
      htNS xAxis

  have hVy :
      SpatialC1
        (
          fun x : Point3 =>
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u t x
            ).component yAxis
        ) :=
    s.velocity_component_spatialC1
      htNS yAxis

  have hVz :
      SpatialC1
        (
          fun x : Point3 =>
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u t x
            ).component zAxis
        ) :=
    s.velocity_component_spatialC1
      htNS zAxis

  have hSecond2 :
      SpatialC2
        (
          spatial3.d
            k
            (
              spatial3.d
                l
                (
                  fun q : Point3 =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t q
                    ).component j
                )
            )
        ) :=
    (hRegular k l j).2

  have hf :
      SpatialC1 f := by

    dsimp only [f]

    change
      SpatialC1
        (
          fun q : Point3 =>
            partialDeriv
              i
              (
                spatial3.d
                  k
                  (
                    spatial3.d
                      l
                      (
                        fun y : Point3 =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t y
                          ).component j
                      )
                  )
              )
              q
        )

    exact
      PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
        hSecond2 i

  have hFxC1 :
      SpatialC1 Fx := by
    dsimp only [Fx]

    exact
      hVx.mul
        (hf.mul hf)

  have hFyC1 :
      SpatialC1 Fy := by
    dsimp only [Fy]

    exact
      hVy.mul
        (hf.mul hf)

  have hFzC1 :
      SpatialC1 Fz := by
    dsimp only [Fz]

    exact
      hVz.mul
        (hf.mul hf)

  have hFx :
      Integrable
        Fx
        (volume : Measure Point3) := by
    dsimp only [Fx, f]

    rw [← hComponentEq]

    simpa only [loggedVelocityComponent] using
      hCoordinates
        xAxis i k l j

  have hFy :
      Integrable
        Fy
        (volume : Measure Point3) := by
    dsimp only [Fy, f]

    rw [← hComponentEq]

    simpa only [loggedVelocityComponent] using
      hCoordinates
        yAxis i k l j

  have hFz :
      Integrable
        Fz
        (volume : Measure Point3) := by
    dsimp only [Fz, f]

    rw [← hComponentEq]

    simpa only [loggedVelocityComponent] using
      hCoordinates
        zAxis i k l j

  have hDivRaw :=
    hDivergence i k l j

  have hDiv :
      Integrable
        (
          fun x : Point3 =>
            spatial3.d xAxis Fx x
              +
            (
              spatial3.d yAxis Fy x
                +
              spatial3.d zAxis Fz x
            )
        )
        (volume : Measure Point3) := by

    dsimp only [Fx, Fy, Fz, f]

    simpa only [
      transportScalarFluxDivergenceXYZ
    ] using
      hDivRaw

  have hZero :
      (
        ∫ x : Point3,
          spatial3.d xAxis Fx x
            +
          (
            spatial3.d yAxis Fy x
              +
            spatial3.d zAxis Fz x
          )
          ∂volume
      )
        =
      0 :=
    integral_divergence_eq_zero_of_integrable_flux_coordinates
      hFxC1
      hFyC1
      hFzC1
      hFx
      hFy
      hFz
      hDiv

  unfold TransportScalarFluxVanishesAt

  dsimp only [Fx, Fy, Fz, f] at hZero

  simpa only [
    transportScalarFluxDivergenceXYZ
  ] using
    hZero

/--
The same hypotheses produce the honest order-three transport
integration-by-parts package: both total-divergence integrability and its zero
whole-space integral.
-/
theorem h3ThirdDerivativeTransportIntegrationByPartsAt_of_pde
    {
      u :
        SpaceTimeVectorField
          ℝ ℝ MulReal Depth.three
    }
    {
      p :
        SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
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
    (
      hPDE :
        H3PDEPairingIntegrableAt
          u p t
    )
    (
      hGradientPairing :
        H3OrderThreeGradientPairingIntegrableAt
          u t
    )
    (
      hInterpolationPairing :
        H3OrderThreeInterpolationPairingIntegrableAt
          u t
    ) :
    H3ThirdDerivativeTransportIntegrationByPartsAt
      u t := by

  have hDiv :
      H3ThirdDerivativeTransportFluxDivergenceIntegrableAt
        u t :=
    h3ThirdDerivativeTransportFluxDivergence_integrable_of_pde
      hClass
      ht
      hPDE
      hGradientPairing
      hInterpolationPairing

  have hFlux :
      H3ThirdDerivativeTransportFluxVanishesAt
        u t :=
    h3ThirdDerivativeTransportFluxVanishesAt_of_pde
      hClass
      ht
      hH3
      hPDE
      hGradientPairing
      hInterpolationPairing

  intro i k l j

  constructor

  · exact
      hDiv i k l j

  · exact
      hFlux i k l j

end

end Euclidean
end Bridge
end PrimeTensor
