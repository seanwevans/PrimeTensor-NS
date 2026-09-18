import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Pairing.Integrability.FromPDE

/-!
# Top-order transport flux divergence is integrable

The Landau tail frontier has been reduced to the top-order flux cancellation

    ∫ div (u (D³u)²) = 0.

The integrability half of that statement is already forced by the canonical
PDE package.

Indeed the PDE pairing data plus the independently integrable third-order
commutator imply

    D³u · (u · ∇D³u) ∈ L¹.

For an incompressible velocity the pointwise scalar-flux identity is

    div (u (D³u)²)
      =
    2 D³u (u · ∇D³u).

Hence every top-order scalar-flux divergence is automatically integrable.
No fourth-order `L²` derivative is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

attribute [local instance]
  point3MeasureSpaceH3OrderThreePairingClosure

noncomputable local instance axisFintypeH3TopFluxDivergenceIntegrability
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Every third-derivative scalar-flux divergence is integrable once the canonical
PDE transport pairing and the already-closed Landau commutator pairings are
available.
-/
theorem h3ThirdDerivativeTransportFluxDivergence_integrable_of_pde
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
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
    )
    (i k l j : PrimeTensor.Axis Depth.three) :
    MeasureTheory.Integrable
      (
        fun x : Point3 =>
          transportScalarFluxDivergenceXYZ
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityComponent u t j)
                    )
                )
            )
            x
      )
      volume := by

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

  have hSecond2 :
      SpatialC2
        (
          spatial3.d
            k
            (
              spatial3.d
                l
                (loggedVelocityComponent u t j)
            )
        ) :=
    (hRegular k l j).2

  have hThirdC1 :
      SpatialC1
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (
                  spatial3.d
                    l
                    (loggedVelocityComponent u t j)
                )
            )
        ) := by

    change
      SpatialC1
        (
          fun q =>
            partialDeriv
              i
              (
                spatial3.d
                  k
                  (
                    spatial3.d
                      l
                      (loggedVelocityComponent u t j)
                  )
              )
              q
        )

    exact
      PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
        hSecond2 i

  have hPairing3 :
      H3OrderThreeTransportPairingIntegrableAt
        u t :=
    h3OrderThreeTransportPairingIntegrableAt_of_pde
      hClass
      ht
      hPDE
      hGradientPairing
      hInterpolationPairing

  have hPure :=
    (hPairing3 i k l j).2

  have hPure' :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
              *
            h3ScalarTransport
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (
                        spatial3.d
                          l
                          (loggedVelocityComponent u t j)
                      )
                  )
              )
              x
        )
        volume := by

    simpa only [thirdTransportedDerivative] using
      hPure

  have hPointwise :
      (
        fun x : Point3 =>
          transportScalarFluxDivergenceXYZ
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityComponent u t j)
                    )
                )
            )
            x
      )
        =
      (
        fun x : Point3 =>
          2
            *
          (
            spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
              *
            h3ScalarTransport
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (
                        spatial3.d
                          l
                          (loggedVelocityComponent u t j)
                      )
                  )
              )
              x
          )
      ) := by

    funext x

    simpa only [mul_assoc] using
      transportScalarFluxDivergenceXYZ_eq_two_mul_transport
        s
        htNS
        hThirdC1
        x

  rw [hPointwise]

  exact
    hPure'.const_mul 2

end

end Euclidean
end Bridge
end PrimeTensor
