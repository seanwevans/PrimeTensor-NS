import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Gradient.Energy

/-!
# Third-order H³ transport: integrated gradient block

The twelve `D³u · Du` terms of the third-order commutator are already bounded
pointwise by `thirdOrderGradientMajorantDensity`, and the complete finite-index
sum of the corresponding square energies is exactly `24 * E₃`.

This file supplies the measure-theoretic bridge for one fixed
`(i,k,l,j)`:

    |⟨DᵢDₖDₗ uⱼ, G₃(i,k,l,j)⟩|
      ≤ h(t) * Mgrad(i,k,l,j).

The split gradient pairing receives its own explicit integrability hypothesis.
This is deliberately weaker logically than pretending that integrability of the
full third commutator automatically implies integrability of each summand after
the gradient/interpolation split.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyTransportOrderThreeGradientIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
Integrability of the split gradient-block pairing.  This is kept explicit
because the pre-existing order-three pairing package concerns the unsplit
commutator.
-/
def H3OrderThreeGradientPairingIntegrableAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  ∀ i k l j : PrimeTensor.Axis Depth.three,
    MeasureTheory.Integrable
      (
        fun x : Point3 =>
          spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t j)
                  )
              )
              x
            *
          thirdTransportCommutatorGradientBlock
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k l j x
      )

private theorem thirdDerivativeSquare_integrable_orderThreeGradientIntegral
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (c r s q : PrimeTensor.Axis Depth.three) :
    MeasureTheory.Integrable
      (
        fun x : Point3 =>
          (
            spatial3.d r
              (
                spatial3.d s
                  (
                    spatial3.d q
                      (loggedVelocityComponent u t c)
                  )
              )
              x
          ) ^ 2
      ) := by

  have hC :=
    hH3 c

  dsimp only at hC

  simpa only [SpatialL2SquareIntegrable] using
    hC.2.2.2 r s q

private theorem thirdOrderAxisGradientMajorantDensity_integrable
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (i k l j r : PrimeTensor.Axis Depth.three) :
    MeasureTheory.Integrable
      (
        fun x : Point3 =>
          thirdOrderAxisGradientMajorantDensity
            u t i k l j r x
      ) := by

  have hF :=
    thirdDerivativeSquare_integrable_orderThreeGradientIntegral
      hH3 j i k l

  have hB1 :=
    thirdDerivativeSquare_integrable_orderThreeGradientIntegral
      hH3 r i k l

  have hB2 :=
    thirdDerivativeSquare_integrable_orderThreeGradientIntegral
      hH3 j i k r

  have hB3 :=
    thirdDerivativeSquare_integrable_orderThreeGradientIntegral
      hH3 j i r l

  have hB4 :=
    thirdDerivativeSquare_integrable_orderThreeGradientIntegral
      hH3 j r k l

  unfold thirdOrderAxisGradientMajorantDensity

  exact
    (
      (
        (
          (hF.const_mul 4).add hB1
        ).add hB2
      ).add hB3
    ).add hB4

/--
Integrating one axis-local pointwise majorant gives exactly its square-energy
counterpart.
-/
theorem integral_thirdOrderAxisGradientMajorantDensity_eq
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (i k l j r : PrimeTensor.Axis Depth.three) :
    (
      ∫ x : Point3,
        thirdOrderAxisGradientMajorantDensity
          u t i k l j r x
    )
      =
    thirdOrderAxisGradientMajorantEnergy
      u t i k l j r := by

  have hF :=
    thirdDerivativeSquare_integrable_orderThreeGradientIntegral
      hH3 j i k l

  have hB1 :=
    thirdDerivativeSquare_integrable_orderThreeGradientIntegral
      hH3 r i k l

  have hB2 :=
    thirdDerivativeSquare_integrable_orderThreeGradientIntegral
      hH3 j i k r

  have hB3 :=
    thirdDerivativeSquare_integrable_orderThreeGradientIntegral
      hH3 j i r l

  have hB4 :=
    thirdDerivativeSquare_integrable_orderThreeGradientIntegral
      hH3 j r k l

  have h0 :=
    hF.const_mul 4

  have h01 :=
    h0.add hB1

  have h012 :=
    h01.add hB2

  have h0123 :=
    h012.add hB3

  simp only [thirdOrderAxisGradientMajorantDensity]

  unfold
    thirdOrderAxisGradientMajorantEnergy
    spatialSquareEnergy

  have hSplit4 :
      (
        ∫ x : Point3,
          4
              *
            (
              spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
            ) ^ 2
            +
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t r)
                  )
              )
              x
          ) ^ 2
            +
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d r
                      (loggedVelocityComponent u t j)
                  )
              )
              x
          ) ^ 2
            +
          (
            spatial3.d i
              (
                spatial3.d r
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t j)
                  )
              )
              x
          ) ^ 2
            +
          (
            spatial3.d r
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t j)
                  )
              )
              x
          ) ^ 2
      )
        =
      (
        ∫ x : Point3,
          4
              *
            (
              spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
            ) ^ 2
            +
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t r)
                  )
              )
              x
          ) ^ 2
            +
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d r
                      (loggedVelocityComponent u t j)
                  )
              )
              x
          ) ^ 2
            +
          (
            spatial3.d i
              (
                spatial3.d r
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t j)
                  )
              )
              x
          ) ^ 2
      )
        +
      ∫ x : Point3,
        (
          spatial3.d r
            (
              spatial3.d k
                (
                  spatial3.d l
                    (loggedVelocityComponent u t j)
                )
            )
            x
        ) ^ 2 := by

    simpa only [Pi.add_apply] using
      (
        MeasureTheory.integral_add
          h0123
          hB4
      )

  have hSplit3 :
      (
        ∫ x : Point3,
          4
              *
            (
              spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
            ) ^ 2
            +
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t r)
                  )
              )
              x
          ) ^ 2
            +
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d r
                      (loggedVelocityComponent u t j)
                  )
              )
              x
          ) ^ 2
            +
          (
            spatial3.d i
              (
                spatial3.d r
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t j)
                  )
              )
              x
          ) ^ 2
      )
        =
      (
        ∫ x : Point3,
          4
              *
            (
              spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
            ) ^ 2
            +
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t r)
                  )
              )
              x
          ) ^ 2
            +
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d r
                      (loggedVelocityComponent u t j)
                  )
              )
              x
          ) ^ 2
      )
        +
      ∫ x : Point3,
        (
          spatial3.d i
            (
              spatial3.d r
                (
                  spatial3.d l
                    (loggedVelocityComponent u t j)
                )
            )
            x
        ) ^ 2 := by

    simpa only [Pi.add_apply] using
      (
        MeasureTheory.integral_add
          h012
          hB3
      )

  have hSplit2 :
      (
        ∫ x : Point3,
          4
              *
            (
              spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
            ) ^ 2
            +
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t r)
                  )
              )
              x
          ) ^ 2
            +
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d r
                      (loggedVelocityComponent u t j)
                  )
              )
              x
          ) ^ 2
      )
        =
      (
        ∫ x : Point3,
          4
              *
            (
              spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
            ) ^ 2
            +
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t r)
                  )
              )
              x
          ) ^ 2
      )
        +
      ∫ x : Point3,
        (
          spatial3.d i
            (
              spatial3.d k
                (
                  spatial3.d r
                    (loggedVelocityComponent u t j)
                )
            )
            x
        ) ^ 2 := by

    simpa only [Pi.add_apply] using
      (
        MeasureTheory.integral_add
          h01
          hB2
      )

  rw [
    hSplit4,
    hSplit3,
    hSplit2,
    MeasureTheory.integral_add h0 hB1,
    MeasureTheory.integral_const_mul
  ]

/--
Integrating the full three-axis gradient majorant gives its square-energy
counterpart.
-/
theorem integral_thirdOrderGradientMajorantDensity_eq
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (i k l j : PrimeTensor.Axis Depth.three) :
    (
      ∫ x : Point3,
        thirdOrderGradientMajorantDensity
          u t i k l j x
    )
      =
    thirdOrderGradientMajorantEnergy
      u t i k l j := by

  have hX :=
    thirdOrderAxisGradientMajorantDensity_integrable
      hH3 i k l j xAxis

  have hY :=
    thirdOrderAxisGradientMajorantDensity_integrable
      hH3 i k l j yAxis

  have hZ :=
    thirdOrderAxisGradientMajorantDensity_integrable
      hH3 i k l j zAxis

  unfold thirdOrderGradientMajorantDensity

  have hSplitXYZ :
      (
        ∫ x : Point3,
          thirdOrderAxisGradientMajorantDensity
              u t i k l j xAxis x
            +
          (
            thirdOrderAxisGradientMajorantDensity
                u t i k l j yAxis x
              +
            thirdOrderAxisGradientMajorantDensity
                u t i k l j zAxis x
          )
      )
        =
      (
        ∫ x : Point3,
          thirdOrderAxisGradientMajorantDensity
            u t i k l j xAxis x
      )
        +
      ∫ x : Point3,
        (
          thirdOrderAxisGradientMajorantDensity
              u t i k l j yAxis x
            +
          thirdOrderAxisGradientMajorantDensity
              u t i k l j zAxis x
        ) := by

    simpa only [Pi.add_apply] using
      (
        MeasureTheory.integral_add
          hX
          (hY.add hZ)
      )

  rw [
    hSplitXYZ,
    MeasureTheory.integral_add hY hZ,
    integral_thirdOrderAxisGradientMajorantDensity_eq
      hH3 i k l j xAxis,
    integral_thirdOrderAxisGradientMajorantDensity_eq
      hH3 i k l j yAxis,
    integral_thirdOrderAxisGradientMajorantDensity_eq
      hH3 i k l j zAxis
  ]

  unfold thirdOrderGradientMajorantEnergy

  simp only [axis_sum_three]

/--
For one fixed top-order coordinate tuple, the gradient-block pairing is bounded
by the integral of its pointwise majorant.
-/
theorem spatialEnergyPairing_thirdTransportCommutatorGradientBlock_le_integral
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {t : ℝ}
    (
      hGradient :
        VelocityGradientEnvelope
          u h t
    )
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (
      hPairing :
        H3OrderThreeGradientPairingIntegrableAt
          u t
    )
    (i k l j : PrimeTensor.Axis Depth.three) :
    abs
        (
          spatialEnergyPairing
            (
              spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t j)
                    )
                )
            )
            (
              thirdTransportCommutatorGradientBlock
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j
            )
        )
      ≤
    ∫ x : Point3,
      h t
        *
      thirdOrderGradientMajorantDensity
        u t i k l j x := by

  let prod : Point3 → ℝ :=
    fun x =>
      spatial3.d i
          (
            spatial3.d k
              (
                spatial3.d l
                  (loggedVelocityComponent u t j)
              )
          )
          x
        *
      thirdTransportCommutatorGradientBlock
        (
          PrimeTensor.Bridge.logSpaceTimeVectorField
            u
        )
        t i k l j x

  let majorant : Point3 → ℝ :=
    fun x =>
      h t
        *
      thirdOrderGradientMajorantDensity
        u t i k l j x

  have hProd :
      MeasureTheory.Integrable
        prod := by

    unfold prod

    exact
      hPairing i k l j

  have hAbsProd :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            abs (prod x)
        ) := by

    simpa only [Real.norm_eq_abs] using
      hProd.norm

  have hLeft :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            2 * abs (prod x)
        ) := by

    exact
      hAbsProd.const_mul 2

  have hDensity :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            thirdOrderGradientMajorantDensity
              u t i k l j x
        ) := by

    have hX :=
      thirdOrderAxisGradientMajorantDensity_integrable
        hH3 i k l j xAxis

    have hY :=
      thirdOrderAxisGradientMajorantDensity_integrable
        hH3 i k l j yAxis

    have hZ :=
      thirdOrderAxisGradientMajorantDensity_integrable
        hH3 i k l j zAxis

    unfold thirdOrderGradientMajorantDensity

    exact
      hX.add
        (hY.add hZ)

  have hMajorant :
      MeasureTheory.Integrable
        majorant := by

    unfold majorant

    exact
      hDensity.const_mul (h t)

  have hPointwise :
      ∀ x : Point3,
        2 * abs (prod x)
          ≤
        majorant x := by

    intro x

    unfold prod majorant

    exact
      thirdTransportCommutatorGradientBlock_density_le_gradientEnvelope
        hGradient
        i k l j x

  have hIntegralMono :
      (
        ∫ x : Point3,
          2 * abs (prod x)
      )
        ≤
      ∫ x : Point3,
        majorant x := by

    exact
      MeasureTheory.integral_mono
        hLeft
        hMajorant
        hPointwise

  have hIntegralAbs :
      abs
          (
            ∫ x : Point3,
              prod x
          )
        ≤
      ∫ x : Point3,
        abs (prod x) := by

    simpa only [Real.norm_eq_abs] using
      (
        MeasureTheory.norm_integral_le_integral_norm
          (f := prod)
      )

  have hPairingToAbsIntegral :
      abs
          (
            spatialEnergyPairing
              (
                spatial3.d i
                  (
                    spatial3.d k
                      (
                        spatial3.d l
                          (loggedVelocityComponent u t j)
                      )
                  )
              )
              (
                thirdTransportCommutatorGradientBlock
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i k l j
              )
          )
        ≤
      ∫ x : Point3,
        2 * abs (prod x) := by

    unfold spatialEnergyPairing

    change
      abs
          (
            2
              *
            (
              ∫ x : Point3,
                prod x
            )
          )
        ≤
      ∫ x : Point3,
        2 * abs (prod x)

    have hScaled :
        2
            *
          abs
            (
              ∫ x : Point3,
                prod x
            )
          ≤
        2
            *
          (
            ∫ x : Point3,
              abs (prod x)
          ) := by

      exact
        mul_le_mul_of_nonneg_left
          hIntegralAbs
          (by norm_num)

    calc
      abs
          (
            2
              *
            (
              ∫ x : Point3,
                prod x
            )
          )
          =
        2
          *
        abs
          (
            ∫ x : Point3,
              prod x
          ) := by
            rw [abs_mul]
            norm_num
      _ ≤
        2
          *
        (
          ∫ x : Point3,
            abs (prod x)
        ) :=
          hScaled
      _ =
        ∫ x : Point3,
          2 * abs (prod x) := by
            rw [MeasureTheory.integral_const_mul]

  exact
    le_trans
      hPairingToAbsIntegral
      hIntegralMono

/--
The same fixed-coordinate pairing is bounded directly by the integrated
square-energy majorant.
-/
theorem spatialEnergyPairing_thirdTransportCommutatorGradientBlock_le_majorantEnergy
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {t : ℝ}
    (
      hGradient :
        VelocityGradientEnvelope
          u h t
    )
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (
      hPairing :
        H3OrderThreeGradientPairingIntegrableAt
          u t
    )
    (i k l j : PrimeTensor.Axis Depth.three) :
    abs
        (
          spatialEnergyPairing
            (
              spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t j)
                    )
                )
            )
            (
              thirdTransportCommutatorGradientBlock
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j
            )
        )
      ≤
    h t
      *
    thirdOrderGradientMajorantEnergy
      u t i k l j := by

  calc
    abs
        (
          spatialEnergyPairing
            (
              spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t j)
                    )
                )
            )
            (
              thirdTransportCommutatorGradientBlock
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j
            )
        )
        ≤
      ∫ x : Point3,
        h t
          *
        thirdOrderGradientMajorantDensity
          u t i k l j x :=
      spatialEnergyPairing_thirdTransportCommutatorGradientBlock_le_integral
        hGradient
        hH3
        hPairing
        i k l j
    _ =
      h t
        *
      (
        ∫ x : Point3,
          thirdOrderGradientMajorantDensity
            u t i k l j x
      ) := by
        rw [MeasureTheory.integral_const_mul]
    _ =
      h t
        *
      thirdOrderGradientMajorantEnergy
        u t i k l j := by
          rw [
            integral_thirdOrderGradientMajorantDensity_eq
              hH3
              i k l j
          ]

end Euclidean
end Bridge
end PrimeTensor
