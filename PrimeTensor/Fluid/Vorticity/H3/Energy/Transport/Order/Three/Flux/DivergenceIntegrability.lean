import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Pairing.Integrability.FromPDE

/-!
# Top-order transport flux divergence is integrable

The canonical PDE package supplies integrability of the full third-order
transport pairing.  Subtracting the independently integrable commutator
pairing gives integrability of the pure transported-third-derivative pairing.

For incompressible velocity,

    div (u (D³u)²) = 2 D³u (u · ∇D³u),

so the top-order scalar-flux divergence is integrable without introducing a
fourth-order L² derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3TopFluxDivergenceIntegrability
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Canonical PDE pairing integrability plus the closed order-three commutator
pairings force L¹-integrability of every top-order scalar-flux divergence.
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
    ) :
    H3ThirdDerivativeTransportFluxDivergenceIntegrableAt
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

  have hPairing3 :
      H3OrderThreeTransportPairingIntegrableAt
        u t :=
    h3OrderThreeTransportPairingIntegrableAt_of_pde
      hClass
      ht
      hPDE
      hGradientPairing
      hInterpolationPairing

  intro i k l j

  have hSecond2 :
      SpatialC2
        (
          spatial3.d
            k
            (
              spatial3.d
                l
                (
                  fun q =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t q
                    ).component j
                )
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
                    (
                      fun q =>
                        (
                          PrimeTensor.Bridge.logSpaceTimeVectorField
                            u t q
                        ).component j
                    )
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
                      (
                        fun y =>
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

  have hPure :=
    (hPairing3 i k l j).2

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
                        (
                          fun q =>
                            (
                              PrimeTensor.Bridge.logSpaceTimeVectorField
                                u t q
                            ).component j
                        )
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
                        (
                          fun q =>
                            (
                              PrimeTensor.Bridge.logSpaceTimeVectorField
                                u t q
                            ).component j
                        )
                    )
                )
                x
              *
            thirdTransportedDerivative
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i k l j x
          )
      ) := by

    funext x

    simpa only [
      thirdTransportedDerivative,
      mul_assoc
    ] using
      transportScalarFluxDivergenceXYZ_eq_two_mul_transport
        s
        htNS
        hThirdC1
        x

  rw [hPointwise]

  exact
    hPure.const_mul 2

end

end Euclidean
end Bridge
end PrimeTensor
