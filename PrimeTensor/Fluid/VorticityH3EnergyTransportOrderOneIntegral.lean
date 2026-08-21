import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderOneBound

/-!
# Integrated first-order H³ transport commutator bound

The preceding module proves the pointwise estimate

    2 |(∂ᵢvⱼ) C₁(i,j)|
      ≤
    h [
      3 (∂ᵢvⱼ)²
        + (∂ₓvⱼ)²
        + (∂ᵧvⱼ)²
        + (∂_zvⱼ)²
    ].

This file integrates that inequality.  It deliberately stops at one fixed
pair `(i,j)`.  The next finite-sum module can then sum the nine coordinate
pairings and collapse the right-hand side to `6 * h(t) * E₁(t)`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable local instance axisFintypeH3EnergyTransportOrderOneIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
The absolute value of one first-order commutator pairing is bounded by the
integral of its pointwise gradient-envelope majorant.
-/
theorem spatialEnergyPairing_firstTransportCommutator_le_integral
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
        H3OrderOneTransportPairingIntegrableAt
          u t
    )
    (i j : PrimeTensor.Axis Depth.three) :
    abs
        (
          spatialEnergyPairing
            (
              spatial3.d
                i
                (loggedVelocityComponent u t j)
            )
            (
              firstTransportCommutator
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i j
            )
        )
      ≤
    ∫ x : Point3,
      h t
        *
      (
        3
            *
          (
            spatial3.d
                i
                (loggedVelocityComponent u t j)
                x
          ) ^ 2
          +
        (
          (
            spatial3.d
                xAxis
                (loggedVelocityComponent u t j)
                x
          ) ^ 2
            +
          (
            (
              spatial3.d
                  yAxis
                  (loggedVelocityComponent u t j)
                  x
            ) ^ 2
              +
            (
              spatial3.d
                  zAxis
                  (loggedVelocityComponent u t j)
                  x
            ) ^ 2
          )
        )
      ) := by

  let prod : Point3 → ℝ :=
    fun x =>
      spatial3.d
          i
          (loggedVelocityComponent u t j)
          x
        *
      firstTransportCommutator
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t i j x

  let majorant : Point3 → ℝ :=
    fun x =>
      h t
        *
      (
        3
            *
          (
            spatial3.d
                i
                (loggedVelocityComponent u t j)
                x
          ) ^ 2
          +
        (
          (
            spatial3.d
                xAxis
                (loggedVelocityComponent u t j)
                x
          ) ^ 2
            +
          (
            (
              spatial3.d
                  yAxis
                  (loggedVelocityComponent u t j)
                  x
            ) ^ 2
              +
            (
              spatial3.d
                  zAxis
                  (loggedVelocityComponent u t j)
                  x
            ) ^ 2
          )
        )
      )

  have hProd :
      MeasureTheory.Integrable
        prod := by

    unfold prod

    exact
      (hPairing i j).1

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

  have hJ :=
    hH3 j

  dsimp only at hJ

  have hFirst :
      ∀ r : PrimeTensor.Axis Depth.three,
        SpatialL2SquareIntegrable
          (
            spatial3.d
              r
              (loggedVelocityComponent u t j)
          ) :=
    hJ.2.1

  have hI :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            (
              spatial3.d
                i
                (loggedVelocityComponent u t j)
                x
            ) ^ 2
        ) := by

    simpa only [SpatialL2SquareIntegrable] using
      hFirst i

  have hX :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            (
              spatial3.d
                xAxis
                (loggedVelocityComponent u t j)
                x
            ) ^ 2
        ) := by

    simpa only [SpatialL2SquareIntegrable] using
      hFirst xAxis

  have hY :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            (
              spatial3.d
                yAxis
                (loggedVelocityComponent u t j)
                x
            ) ^ 2
        ) := by

    simpa only [SpatialL2SquareIntegrable] using
      hFirst yAxis

  have hZ :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            (
              spatial3.d
                zAxis
                (loggedVelocityComponent u t j)
                x
            ) ^ 2
        ) := by

    simpa only [SpatialL2SquareIntegrable] using
      hFirst zAxis

  have hMajorant :
      MeasureTheory.Integrable
        majorant := by

    unfold majorant

    exact
      (
        (hI.const_mul 3).add
          (
            hX.add
              (
                hY.add hZ
              )
          )
      ).const_mul (h t)

  have hPointwise :
      ∀ x : Point3,
        2 * abs (prod x)
          ≤
        majorant x := by

    intro x

    unfold prod majorant

    exact
      firstTransportCommutator_density_le_gradientEnvelope
        hGradient
        i j x

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
                spatial3.d
                  i
                  (loggedVelocityComponent u t j)
              )
              (
                firstTransportCommutator
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u
                  )
                  t i j
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

end Euclidean
end Bridge
end PrimeTensor
