import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderTwoIntegral
import PrimeTensor.Fluid.VorticityH3AxisSum

/-!
# Summed second-order H³ transport estimate

The pointwise and integrated order-two commutator estimates are already proved.
This file performs only the remaining exact bookkeeping.

For fixed `(i,k,j)`, define the quadratic majorant energy corresponding to the
nine second-derivative squares in `secondOrderCommutatorMajorantDensity`.
After summing over all three coordinate indices,

    Σ_j Σ_i Σ_k M₂(i,k,j) = 18 E₂.

Indeed:
* the distinguished `9 |∂ᵢ∂ₖvⱼ|²` term contributes `9 E₂`;
* the family `Σ_r |∂ᵢ∂ₖv_r|²` contributes `3 E₂`;
* the family `Σ_r |∂ᵢ∂ᵣv_j|²` contributes `3 E₂`;
* the family `Σ_r |∂ᵣ∂ₖv_j|²` contributes `3 E₂`.

Thus

    |T₂(t)| ≤ 18 h(t) E₂(t).

No interpolation estimate is used at derivative order two.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyTransportOrderTwoSum
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-! ## The integrated coordinate majorant -/

/--
The square-energy version of `secondOrderCommutatorMajorantDensity`.
-/
noncomputable def secondOrderCommutatorMajorantEnergy
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (i k j : PrimeTensor.Axis Depth.three) : ℝ :=
  9
      *
    spatialSquareEnergy
      (
        spatial3.d
          i
          (
            spatial3.d
              k
              (loggedVelocityComponent u t j)
          )
      )
    +
  (
    (
      spatialSquareEnergy
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (loggedVelocityComponent u t xAxis)
            )
        )
        +
      (
        spatialSquareEnergy
          (
            spatial3.d
              i
              (
                spatial3.d
                  xAxis
                  (loggedVelocityComponent u t j)
              )
          )
          +
        spatialSquareEnergy
          (
            spatial3.d
              xAxis
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t j)
              )
          )
      )
    )
      +
    (
      (
        spatialSquareEnergy
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t yAxis)
              )
          )
          +
        (
          spatialSquareEnergy
            (
              spatial3.d
                i
                (
                  spatial3.d
                    yAxis
                    (loggedVelocityComponent u t j)
                )
            )
            +
          spatialSquareEnergy
            (
              spatial3.d
                yAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
            )
        )
      )
        +
      (
        spatialSquareEnergy
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t zAxis)
              )
          )
          +
        (
          spatialSquareEnergy
            (
              spatial3.d
                i
                (
                  spatial3.d
                    zAxis
                    (loggedVelocityComponent u t j)
                )
            )
            +
          spatialSquareEnergy
            (
              spatial3.d
                zAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
            )
        )
      )
    )
  )

private theorem secondDerivativeSquare_integrable_orderTwoSum
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
    (c r s : PrimeTensor.Axis Depth.three) :
    MeasureTheory.Integrable
      (
        fun x : Point3 =>
          (
            spatial3.d
              r
              (
                spatial3.d
                  s
                  (loggedVelocityComponent u t c)
              )
              x
          ) ^ 2
      ) := by

  have hC :=
    hH3 c

  dsimp only at hC

  simpa only [SpatialL2SquareIntegrable] using
    hC.2.2.1 r s

/--
Integrating the explicit pointwise majorant gives exactly its square-energy
counterpart.
-/
theorem integral_secondOrderCommutatorMajorantDensity_eq
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
    (i k j : PrimeTensor.Axis Depth.three) :
    (
      ∫ x : Point3,
        secondOrderCommutatorMajorantDensity
          u t i k j x
    )
      =
    secondOrderCommutatorMajorantEnergy
      u t i k j := by

  have hF :=
    secondDerivativeSquare_integrable_orderTwoSum
      hH3 j i k

  have hX1 :=
    secondDerivativeSquare_integrable_orderTwoSum
      hH3 xAxis i k

  have hX2 :=
    secondDerivativeSquare_integrable_orderTwoSum
      hH3 j i xAxis

  have hX3 :=
    secondDerivativeSquare_integrable_orderTwoSum
      hH3 j xAxis k

  have hY1 :=
    secondDerivativeSquare_integrable_orderTwoSum
      hH3 yAxis i k

  have hY2 :=
    secondDerivativeSquare_integrable_orderTwoSum
      hH3 j i yAxis

  have hY3 :=
    secondDerivativeSquare_integrable_orderTwoSum
      hH3 j yAxis k

  have hZ1 :=
    secondDerivativeSquare_integrable_orderTwoSum
      hH3 zAxis i k

  have hZ2 :=
    secondDerivativeSquare_integrable_orderTwoSum
      hH3 j i zAxis

  have hZ3 :=
    secondDerivativeSquare_integrable_orderTwoSum
      hH3 j zAxis k

  have hX :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t xAxis)
                )
                x
            ) ^ 2
              +
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      xAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
                +
              (
                spatial3.d
                  xAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
            )
        ) :=
    hX1.add
      (hX2.add hX3)

  have hY :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t yAxis)
                )
                x
            ) ^ 2
              +
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      yAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
                +
              (
                spatial3.d
                  yAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
            )
        ) :=
    hY1.add
      (hY2.add hY3)

  have hZ :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t zAxis)
                )
                x
            ) ^ 2
              +
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      zAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
                +
              (
                spatial3.d
                  zAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
            )
        ) :=
    hZ1.add
      (hZ2.add hZ3)

  have hXYZ :
      MeasureTheory.Integrable
        (
          fun x : Point3 =>
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t xAxis)
                  )
                  x
              ) ^ 2
                +
              (
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        xAxis
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
                  +
                (
                  spatial3.d
                    xAxis
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
              )
            )
              +
            (
              (
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t yAxis)
                    )
                    x
                ) ^ 2
                  +
                (
                  (
                    spatial3.d
                      i
                      (
                        spatial3.d
                          yAxis
                          (loggedVelocityComponent u t j)
                      )
                      x
                  ) ^ 2
                    +
                  (
                    spatial3.d
                      yAxis
                      (
                        spatial3.d
                          k
                          (loggedVelocityComponent u t j)
                      )
                      x
                  ) ^ 2
                )
              )
                +
              (
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t zAxis)
                    )
                    x
                ) ^ 2
                  +
                (
                  (
                    spatial3.d
                      i
                      (
                        spatial3.d
                          zAxis
                          (loggedVelocityComponent u t j)
                      )
                      x
                  ) ^ 2
                    +
                  (
                    spatial3.d
                      zAxis
                      (
                        spatial3.d
                          k
                          (loggedVelocityComponent u t j)
                      )
                      x
                  ) ^ 2
                )
              )
            )
        ) :=
    hX.add
      (hY.add hZ)

  unfold
    secondOrderCommutatorMajorantDensity
    secondOrderCommutatorMajorantEnergy
    spatialSquareEnergy

  have hTop :
      (
        ∫ x : Point3,
          9
              *
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
            +
          (
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t xAxis)
                  )
                  x
              ) ^ 2
                +
              (
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        xAxis
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
                  +
                (
                  spatial3.d
                    xAxis
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
              )
            )
              +
            (
              (
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t yAxis)
                    )
                    x
                ) ^ 2
                  +
                (
                  (
                    spatial3.d
                      i
                      (
                        spatial3.d
                          yAxis
                          (loggedVelocityComponent u t j)
                      )
                      x
                  ) ^ 2
                    +
                  (
                    spatial3.d
                      yAxis
                      (
                        spatial3.d
                          k
                          (loggedVelocityComponent u t j)
                      )
                      x
                  ) ^ 2
                )
              )
                +
              (
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t zAxis)
                    )
                    x
                ) ^ 2
                  +
                (
                  (
                    spatial3.d
                      i
                      (
                        spatial3.d
                          zAxis
                          (loggedVelocityComponent u t j)
                      )
                      x
                  ) ^ 2
                    +
                  (
                    spatial3.d
                      zAxis
                      (
                        spatial3.d
                          k
                          (loggedVelocityComponent u t j)
                      )
                      x
                  ) ^ 2
                )
              )
            )
          )
      )
        =
      (
        ∫ x : Point3,
          9
            *
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t j)
              )
              x
          ) ^ 2
      )
        +
      ∫ x : Point3,
        (
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t xAxis)
              )
              x
          ) ^ 2
            +
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    xAxis
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
              +
            (
              spatial3.d
                xAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
          )
        )
          +
        (
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t yAxis)
                )
                x
            ) ^ 2
              +
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      yAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
                +
              (
                spatial3.d
                  yAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
            )
          )
            +
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t zAxis)
                )
                x
            ) ^ 2
              +
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      zAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
                +
              (
                spatial3.d
                  zAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
            )
          )
        ) := by

    exact
      MeasureTheory.integral_add
        (hF.const_mul 9)
        hXYZ

  rw [hTop]
  rw [MeasureTheory.integral_const_mul]

  have hXInt :
      (
        ∫ x : Point3,
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t xAxis)
              )
              x
          ) ^ 2
            +
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    xAxis
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
              +
            (
              spatial3.d
                xAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
          )
      )
        =
      (
        ∫ x : Point3,
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t xAxis)
              )
              x
          ) ^ 2
      )
        +
      (
        (
          ∫ x : Point3,
            (
              spatial3.d
                i
                (
                  spatial3.d
                    xAxis
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
        )
          +
        ∫ x : Point3,
          (
            spatial3.d
              xAxis
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t j)
              )
              x
          ) ^ 2
      ) := by

    calc
      (
        ∫ x : Point3,
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t xAxis)
              )
              x
          ) ^ 2
            +
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    xAxis
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
              +
            (
              spatial3.d
                xAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
          )
      )
          =
        (
          ∫ x : Point3,
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t xAxis)
                )
                x
            ) ^ 2
        )
          +
        ∫ x : Point3,
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    xAxis
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
              +
            (
              spatial3.d
                xAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
          ) :=
        MeasureTheory.integral_add
          hX1
          (hX2.add hX3)
      _ =
        (
          ∫ x : Point3,
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t xAxis)
                )
                x
            ) ^ 2
        )
          +
        (
          (
            ∫ x : Point3,
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      xAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
          )
            +
          ∫ x : Point3,
            (
              spatial3.d
                xAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
        ) := by
          rw [
            MeasureTheory.integral_add
              hX2
              hX3
          ]

  have hYInt :
      (
        ∫ x : Point3,
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t yAxis)
              )
              x
          ) ^ 2
            +
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    yAxis
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
              +
            (
              spatial3.d
                yAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
          )
      )
        =
      (
        ∫ x : Point3,
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t yAxis)
              )
              x
          ) ^ 2
      )
        +
      (
        (
          ∫ x : Point3,
            (
              spatial3.d
                i
                (
                  spatial3.d
                    yAxis
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
        )
          +
        ∫ x : Point3,
          (
            spatial3.d
              yAxis
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t j)
              )
              x
          ) ^ 2
      ) := by

    calc
      (
        ∫ x : Point3,
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t yAxis)
              )
              x
          ) ^ 2
            +
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    yAxis
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
              +
            (
              spatial3.d
                yAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
          )
      )
          =
        (
          ∫ x : Point3,
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t yAxis)
                )
                x
            ) ^ 2
        )
          +
        ∫ x : Point3,
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    yAxis
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
              +
            (
              spatial3.d
                yAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
          ) :=
        MeasureTheory.integral_add
          hY1
          (hY2.add hY3)
      _ =
        (
          ∫ x : Point3,
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t yAxis)
                )
                x
            ) ^ 2
        )
          +
        (
          (
            ∫ x : Point3,
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      yAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
          )
            +
          ∫ x : Point3,
            (
              spatial3.d
                yAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
        ) := by
          rw [
            MeasureTheory.integral_add
              hY2
              hY3
          ]

  have hZInt :
      (
        ∫ x : Point3,
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t zAxis)
              )
              x
          ) ^ 2
            +
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    zAxis
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
              +
            (
              spatial3.d
                zAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
          )
      )
        =
      (
        ∫ x : Point3,
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t zAxis)
              )
              x
          ) ^ 2
      )
        +
      (
        (
          ∫ x : Point3,
            (
              spatial3.d
                i
                (
                  spatial3.d
                    zAxis
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
        )
          +
        ∫ x : Point3,
          (
            spatial3.d
              zAxis
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t j)
              )
              x
          ) ^ 2
      ) := by

    calc
      (
        ∫ x : Point3,
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t zAxis)
              )
              x
          ) ^ 2
            +
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    zAxis
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
              +
            (
              spatial3.d
                zAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
          )
      )
          =
        (
          ∫ x : Point3,
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t zAxis)
                )
                x
            ) ^ 2
        )
          +
        ∫ x : Point3,
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    zAxis
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
              +
            (
              spatial3.d
                zAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
          ) :=
        MeasureTheory.integral_add
          hZ1
          (hZ2.add hZ3)
      _ =
        (
          ∫ x : Point3,
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t zAxis)
                )
                x
            ) ^ 2
        )
          +
        (
          (
            ∫ x : Point3,
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      zAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
          )
            +
          ∫ x : Point3,
            (
              spatial3.d
                zAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
        ) := by
          rw [
            MeasureTheory.integral_add
              hZ2
              hZ3
          ]

  have hYZInt :
      (
        ∫ x : Point3,
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t yAxis)
                )
                x
            ) ^ 2
              +
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      yAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
                +
              (
                spatial3.d
                  yAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
            )
          )
            +
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t zAxis)
                )
                x
            ) ^ 2
              +
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      zAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
                +
              (
                spatial3.d
                  zAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
            )
          )
      )
        =
      (
        (
          ∫ x : Point3,
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t yAxis)
                )
                x
            ) ^ 2
        )
          +
        (
          (
            ∫ x : Point3,
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      yAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
          )
            +
          ∫ x : Point3,
            (
              spatial3.d
                yAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
        )
      )
        +
      (
        (
          ∫ x : Point3,
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t zAxis)
                )
                x
            ) ^ 2
        )
          +
        (
          (
            ∫ x : Point3,
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      zAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
          )
            +
          ∫ x : Point3,
            (
              spatial3.d
                zAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
        )
      ) := by

    calc
      (
        ∫ x : Point3,
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t yAxis)
                )
                x
            ) ^ 2
              +
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      yAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
                +
              (
                spatial3.d
                  yAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
            )
          )
            +
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t zAxis)
                )
                x
            ) ^ 2
              +
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      zAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
                +
              (
                spatial3.d
                  zAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
            )
          )
      )
          =
        (
          ∫ x : Point3,
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t yAxis)
                  )
                  x
              ) ^ 2
                +
              (
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        yAxis
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
                  +
                (
                  spatial3.d
                    yAxis
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
              )
          )
        )
            +
        (
        ∫ x : Point3,
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t zAxis)
                )
                x
            ) ^ 2
              +
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      zAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
                +
              (
                spatial3.d
                  zAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
            )
        )) :=
        MeasureTheory.integral_add
          hY
          hZ
      _ =
        (
          (
            ∫ x : Point3,
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t yAxis)
                  )
                  x
              ) ^ 2
          )
            +
          (
            (
              ∫ x : Point3,
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        yAxis
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
            )
              +
            ∫ x : Point3,
              (
                spatial3.d
                  yAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
          )
        )
          +
        (
          (
            ∫ x : Point3,
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t zAxis)
                  )
                  x
              ) ^ 2
          )
            +
          (
            (
              ∫ x : Point3,
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        zAxis
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
            )
              +
            ∫ x : Point3,
              (
                spatial3.d
                  zAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
          )
        ) := by
          calc
            _ =
                (
                  (∫ x : Point3,
                    (
                      spatial3.d
                        i
                        (
                          spatial3.d
                            k
                            (loggedVelocityComponent u t yAxis)
                        )
                        x
                    ) ^ 2
                      +
                    (
                      (
                        spatial3.d
                          i
                          (
                            spatial3.d
                              yAxis
                              (loggedVelocityComponent u t j)
                          )
                          x
                      ) ^ 2
                        +
                      (
                        spatial3.d
                          yAxis
                          (
                            spatial3.d
                              k
                              (loggedVelocityComponent u t j)
                          )
                          x
                      ) ^ 2
                    )
                  )
                )
                  +
                (
                  ∫ x : Point3,
                    (
                      spatial3.d
                        i
                        (
                          spatial3.d
                            k
                            (loggedVelocityComponent u t zAxis)
                        )
                        x
                    ) ^ 2
                      +
                    (
                      (
                        spatial3.d
                          i
                          (
                            spatial3.d
                              zAxis
                              (loggedVelocityComponent u t j)
                          )
                          x
                      ) ^ 2
                        +
                      (
                        spatial3.d
                          zAxis
                          (
                            spatial3.d
                              k
                              (loggedVelocityComponent u t j)
                          )
                          x
                      ) ^ 2
                    )
                ) := by
                  rfl
            _ =
                (
                  (
                    ∫ x : Point3,
                      (
                        spatial3.d
                          i
                          (
                            spatial3.d
                              k
                              (loggedVelocityComponent u t yAxis)
                          )
                          x
                      ) ^ 2
                  )
                    +
                  (
                    (
                      ∫ x : Point3,
                        (
                          spatial3.d
                            i
                            (
                              spatial3.d
                                yAxis
                                (loggedVelocityComponent u t j)
                            )
                            x
                        ) ^ 2
                    )
                      +
                    ∫ x : Point3,
                      (
                        spatial3.d
                          yAxis
                          (
                            spatial3.d
                              k
                              (loggedVelocityComponent u t j)
                          )
                          x
                      ) ^ 2
                  )
                )
                  +
                (
                  ∫ x : Point3,
                    (
                      spatial3.d
                        i
                        (
                          spatial3.d
                            k
                            (loggedVelocityComponent u t zAxis)
                        )
                        x
                    ) ^ 2
                      +
                    (
                      (
                        spatial3.d
                          i
                          (
                            spatial3.d
                              zAxis
                              (loggedVelocityComponent u t j)
                          )
                          x
                      ) ^ 2
                        +
                      (
                        spatial3.d
                          zAxis
                          (
                            spatial3.d
                              k
                              (loggedVelocityComponent u t j)
                          )
                          x
                      ) ^ 2
                    )
                ) := by
                  exact congrArg
                    (fun q : ℝ =>
                      q
                        +
                      (
                        ∫ x : Point3,
                          (
                            spatial3.d
                              i
                              (
                                spatial3.d
                                  k
                                  (loggedVelocityComponent u t zAxis)
                              )
                              x
                          ) ^ 2
                            +
                          (
                            (
                              spatial3.d
                                i
                                (
                                  spatial3.d
                                    zAxis
                                    (loggedVelocityComponent u t j)
                                )
                                x
                            ) ^ 2
                              +
                            (
                              spatial3.d
                                zAxis
                                (
                                  spatial3.d
                                    k
                                    (loggedVelocityComponent u t j)
                                )
                                x
                            ) ^ 2
                          )
                      )
                    )
                    hYInt
            _ = _ := by
                  exact congrArg
                    (fun q : ℝ =>
                      (
                        (
                          ∫ x : Point3,
                            (
                              spatial3.d
                                i
                                (
                                  spatial3.d
                                    k
                                    (loggedVelocityComponent u t yAxis)
                                )
                                x
                            ) ^ 2
                        )
                          +
                        (
                          (
                            ∫ x : Point3,
                              (
                                spatial3.d
                                  i
                                  (
                                    spatial3.d
                                      yAxis
                                      (loggedVelocityComponent u t j)
                                  )
                                  x
                              ) ^ 2
                          )
                            +
                          ∫ x : Point3,
                            (
                              spatial3.d
                                yAxis
                                (
                                  spatial3.d
                                    k
                                    (loggedVelocityComponent u t j)
                                )
                                x
                            ) ^ 2
                        )
                      )
                        +
                      q
                    )
                    hZInt

  have hXYZInt :
      (
        ∫ x : Point3,
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t xAxis)
                )
                x
            ) ^ 2
              +
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      xAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
                +
              (
                spatial3.d
                  xAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
            )
          )
            +
          (
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t yAxis)
                  )
                  x
              ) ^ 2
                +
              (
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        yAxis
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
                  +
                (
                  spatial3.d
                    yAxis
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
              )
            )
              +
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t zAxis)
                  )
                  x
              ) ^ 2
                +
              (
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        zAxis
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
                  +
                (
                  spatial3.d
                    zAxis
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
              )
            )
          )
      )
        =
      (
        (
          ∫ x : Point3,
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t xAxis)
                )
                x
            ) ^ 2
        )
          +
        (
          (
            ∫ x : Point3,
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      xAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
          )
            +
          ∫ x : Point3,
            (
              spatial3.d
                xAxis
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
        )
      )
        +
      (
        (
          (
            ∫ x : Point3,
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t yAxis)
                  )
                  x
              ) ^ 2
          )
            +
          (
            (
              ∫ x : Point3,
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        yAxis
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
            )
              +
            ∫ x : Point3,
              (
                spatial3.d
                  yAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
          )
        )
          +
        (
          (
            ∫ x : Point3,
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t zAxis)
                  )
                  x
              ) ^ 2
          )
            +
          (
            (
              ∫ x : Point3,
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        zAxis
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
            )
              +
            ∫ x : Point3,
              (
                spatial3.d
                  zAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
          )
        )
      ) := by

    calc
      (
        ∫ x : Point3,
          (
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t xAxis)
                )
                x
            ) ^ 2
              +
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      xAxis
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
                +
              (
                spatial3.d
                  xAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
            )
          )
            +
          (
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t yAxis)
                  )
                  x
              ) ^ 2
                +
              (
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        yAxis
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
                  +
                (
                  spatial3.d
                    yAxis
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
              )
            )
              +
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t zAxis)
                  )
                  x
              ) ^ 2
                +
              (
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        zAxis
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
                  +
                (
                  spatial3.d
                    zAxis
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
              )
            )
          )
      )
          =
        (
          ∫ x : Point3,
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t xAxis)
                  )
                  x
              ) ^ 2
                +
              (
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        xAxis
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
                  +
                (
                  spatial3.d
                    xAxis
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
              )
          )
        )
            +
        ∫ x : Point3,
          (
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t yAxis)
                  )
                  x
              ) ^ 2
                +
              (
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        yAxis
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
                  +
                (
                  spatial3.d
                    yAxis
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
              )
            )
              +
            (
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t zAxis)
                  )
                  x
              ) ^ 2
                +
              (
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        zAxis
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
                  +
                (
                  spatial3.d
                    zAxis
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
              )
            )
          ) :=
        MeasureTheory.integral_add
          hX
          (hY.add hZ)
      _ =
        (
          (
            ∫ x : Point3,
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t xAxis)
                  )
                  x
              ) ^ 2
          )
            +
          (
            (
              ∫ x : Point3,
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        xAxis
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
            )
              +
            ∫ x : Point3,
              (
                spatial3.d
                  xAxis
                  (
                    spatial3.d
                      k
                      (loggedVelocityComponent u t j)
                  )
                  x
              ) ^ 2
          )
        )
          +
        (
          (
            (
              ∫ x : Point3,
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t yAxis)
                    )
                    x
                ) ^ 2
            )
              +
            (
              (
                ∫ x : Point3,
                  (
                    spatial3.d
                      i
                      (
                        spatial3.d
                          yAxis
                          (loggedVelocityComponent u t j)
                      )
                      x
                  ) ^ 2
              )
                +
              ∫ x : Point3,
                (
                  spatial3.d
                    yAxis
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
            )
          )
            +
          (
            (
              ∫ x : Point3,
                (
                  spatial3.d
                    i
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t zAxis)
                    )
                    x
                ) ^ 2
            )
              +
            (
              (
                ∫ x : Point3,
                  (
                    spatial3.d
                      i
                      (
                        spatial3.d
                          zAxis
                          (loggedVelocityComponent u t j)
                      )
                      x
                  ) ^ 2
              )
                +
              ∫ x : Point3,
                (
                  spatial3.d
                    zAxis
                    (
                      spatial3.d
                        k
                        (loggedVelocityComponent u t j)
                    )
                    x
                ) ^ 2
            )
          )
        ) := by
          rw [hXInt, hYZInt]

  exact
    congrArg
      (fun q : ℝ =>
        (
          9
            *
          ∫ x : Point3,
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
                x
            ) ^ 2
        )
          +
        q
      )
      hXYZInt

/--
One second-order commutator pairing is bounded by the corresponding
square-energy majorant.
-/
theorem spatialEnergyPairing_secondTransportCommutator_le_majorantEnergy
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
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
        H3OrderTwoTransportPairingIntegrableAt
          u t
    )
    (i k j : PrimeTensor.Axis Depth.three) :
    abs
        (
          spatialEnergyPairing
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
            )
            (
              secondTransportCommutator
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k j
            )
        )
      ≤
    h t
      *
    secondOrderCommutatorMajorantEnergy
      u t i k j := by

  calc
    abs
        (
          spatialEnergyPairing
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (loggedVelocityComponent u t j)
                )
            )
            (
              secondTransportCommutator
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k j
            )
        )
        ≤
      ∫ x : Point3,
        h t
          *
        secondOrderCommutatorMajorantDensity
          u t i k j x :=
      spatialEnergyPairing_secondTransportCommutator_le_integral
        hClass
        ht
        hGradient
        hH3
        hPairing
        i k j
    _ =
      h t
        *
      (
        ∫ x : Point3,
          secondOrderCommutatorMajorantDensity
            u t i k j x
      ) := by
        rw [MeasureTheory.integral_const_mul]
    _ =
      h t
        *
      secondOrderCommutatorMajorantEnergy
        u t i k j := by
          rw [
            integral_secondOrderCommutatorMajorantDensity_eq
              hH3
              i k j
          ]

/--
The full triple coordinate sum of second-order majorants is exactly eighteen
copies of the canonical second-order H³ energy.
-/
theorem sum_secondOrderCommutatorMajorantEnergy_eq
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) :
    (
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            secondOrderCommutatorMajorantEnergy
              u t i k j
    )
      =
    18 * velocityH3Energy2At u t := by

  classical

  unfold secondOrderCommutatorMajorantEnergy
  unfold velocityH3Energy2At

  simp only [axis_sum_three]

  ring

/--
The complete order-two H³ transport derivative obeys

    |T₂(t)| ≤ 18 h(t) E₂(t).

This is the complete order-two tame estimate.
-/
theorem velocityH3TransportDerivative2At_le_gradientEnvelope
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
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
      hFlux :
        H3SecondDerivativeTransportFluxVanishesAt
          u t
    )
    (
      hPairing :
        H3OrderTwoTransportPairingIntegrableAt
          u t
    )
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (
      hGradient :
        VelocityGradientEnvelope
          u h t
    ) :
    abs
        (
          velocityH3TransportDerivative2At
            u t
        )
      ≤
    18 * h t * velocityH3Energy2At u t := by

  classical

  rw [
    velocityH3TransportDerivative2At_eq_commutator
      hClass
      ht
      hFlux
      hPairing
  ]

  let pairing :
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      ℝ :=
    fun j i k =>
      spatialEnergyPairing
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (loggedVelocityComponent u t j)
            )
        )
        (
          secondTransportCommutator
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k j
        )

  change
    abs
        (
          ∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                pairing j i k
        )
      ≤
    18 * h t * velocityH3Energy2At u t

  have hK :
      ∀
        (j i : PrimeTensor.Axis Depth.three),
        abs
            (
              ∑ k : PrimeTensor.Axis Depth.three,
                pairing j i k
            )
          ≤
        ∑ k : PrimeTensor.Axis Depth.three,
          abs (pairing j i k) := by

    intro j i

    simpa only [Real.norm_eq_abs] using
      (
        norm_sum_le
          (Finset.univ :
            Finset (PrimeTensor.Axis Depth.three))
          (fun k => pairing j i k)
      )

  have hI :
      ∀ j : PrimeTensor.Axis Depth.three,
        abs
            (
              ∑ i : PrimeTensor.Axis Depth.three,
                ∑ k : PrimeTensor.Axis Depth.three,
                  pairing j i k
            )
          ≤
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            abs (pairing j i k) := by

    intro j

    have hOuterI :
        abs
            (
              ∑ i : PrimeTensor.Axis Depth.three,
                ∑ k : PrimeTensor.Axis Depth.three,
                  pairing j i k
            )
          ≤
        ∑ i : PrimeTensor.Axis Depth.three,
          abs
            (
              ∑ k : PrimeTensor.Axis Depth.three,
                pairing j i k
            ) := by

      simpa only [Real.norm_eq_abs] using
        (
          norm_sum_le
            (Finset.univ :
              Finset (PrimeTensor.Axis Depth.three))
            (
              fun i =>
                ∑ k : PrimeTensor.Axis Depth.three,
                  pairing j i k
            )
        )

    exact
      le_trans
        hOuterI
        (
          Finset.sum_le_sum
            (fun i _ =>
              hK j i)
        )

  have hJ :
      abs
          (
            ∑ j : PrimeTensor.Axis Depth.three,
              ∑ i : PrimeTensor.Axis Depth.three,
                ∑ k : PrimeTensor.Axis Depth.three,
                  pairing j i k
          )
        ≤
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            abs (pairing j i k) := by

    have hOuterJ :
        abs
            (
              ∑ j : PrimeTensor.Axis Depth.three,
                ∑ i : PrimeTensor.Axis Depth.three,
                  ∑ k : PrimeTensor.Axis Depth.three,
                    pairing j i k
            )
          ≤
        ∑ j : PrimeTensor.Axis Depth.three,
          abs
            (
              ∑ i : PrimeTensor.Axis Depth.three,
                ∑ k : PrimeTensor.Axis Depth.three,
                  pairing j i k
            ) := by

      simpa only [Real.norm_eq_abs] using
        (
          norm_sum_le
            (Finset.univ :
              Finset (PrimeTensor.Axis Depth.three))
            (
              fun j =>
                ∑ i : PrimeTensor.Axis Depth.three,
                  ∑ k : PrimeTensor.Axis Depth.three,
                    pairing j i k
            )
        )

    exact
      le_trans
        hOuterJ
        (
          Finset.sum_le_sum
            (fun j _ =>
              hI j)
        )

  have hPairBound :
      (
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              abs (pairing j i k)
      )
        ≤
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            h t
              *
            secondOrderCommutatorMajorantEnergy
              u t i k j := by

    apply Finset.sum_le_sum
    intro j hj

    apply Finset.sum_le_sum
    intro i hi

    apply Finset.sum_le_sum
    intro k hk

    unfold pairing

    exact
      spatialEnergyPairing_secondTransportCommutator_le_majorantEnergy
        hClass
        ht
        hGradient
        hH3
        hPairing
        i k j

  have hScaleSum :
      (
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              h t
                *
              secondOrderCommutatorMajorantEnergy
                u t i k j
      )
        =
      h t
        *
      (
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              secondOrderCommutatorMajorantEnergy
                u t i k j
      ) := by

    simp only [axis_sum_three]

    ring

  calc
    abs
        (
          ∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              ∑ k : PrimeTensor.Axis Depth.three,
                pairing j i k
        )
        ≤
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            abs (pairing j i k) :=
      hJ
    _ ≤
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          ∑ k : PrimeTensor.Axis Depth.three,
            h t
              *
            secondOrderCommutatorMajorantEnergy
              u t i k j :=
      hPairBound
    _ =
      h t
        *
      (
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            ∑ k : PrimeTensor.Axis Depth.three,
              secondOrderCommutatorMajorantEnergy
                u t i k j
      ) :=
      hScaleSum
    _ =
      h t
        *
      (
        18 * velocityH3Energy2At u t
      ) := by
        rw [
          sum_secondOrderCommutatorMajorantEnergy_eq
            u t
        ]
    _ =
      18 * h t * velocityH3Energy2At u t := by
        ring

end Euclidean
end Bridge
end PrimeTensor
