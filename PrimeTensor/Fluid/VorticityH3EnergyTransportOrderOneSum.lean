import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderOneIntegral
import PrimeTensor.Fluid.VorticityH3AxisSum

/-!
# Summed first-order H³ transport bound

This module closes the order-one transport estimate.

For one coordinate pair `(i,j)`, the preceding module gives

    |2 ∫ (∂ᵢvⱼ) C₁(i,j)|
      ≤
    h(t) [
      3 ‖∂ᵢvⱼ‖₂²
        + ‖∂ₓvⱼ‖₂²
        + ‖∂ᵧvⱼ‖₂²
        + ‖∂_zvⱼ‖₂²
    ].

Summing over the three derivative directions gives six copies of the
first-order energy for each velocity component: three from the distinguished
`∂ᵢvⱼ` term and three from the full gradient term.  Summing over velocity
components therefore yields

    |T₁(t)| ≤ 6 h(t) E₁(t).

No Sobolev interpolation enters here; order one is controlled solely by the
pointwise first-gradient envelope, square integrability, and the explicit
whole-space transport cancellation hypotheses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyTransportOrderOneSum
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
The square-energy expression appearing after integration of one first-order
commutator density.
-/
noncomputable def firstOrderCommutatorMajorantEnergy
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (i j : PrimeTensor.Axis Depth.three) : ℝ :=
  3
      *
    spatialSquareEnergy
      (
        spatial3.d
          i
          (loggedVelocityComponent u t j)
      )
    +
  (
    spatialSquareEnergy
      (
        spatial3.d
          xAxis
          (loggedVelocityComponent u t j)
      )
      +
    (
      spatialSquareEnergy
        (
          spatial3.d
            yAxis
            (loggedVelocityComponent u t j)
        )
        +
      spatialSquareEnergy
        (
          spatial3.d
            zAxis
            (loggedVelocityComponent u t j)
        )
    )
  )

/--
The pointwise majorant integral from the previous module is exactly the
corresponding finite combination of first-order square energies.
-/
theorem integral_firstOrderCommutatorMajorant_eq
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {t : ℝ}
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (i j : PrimeTensor.Axis Depth.three) :
    (
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
        )
    )
      =
    h t
      *
    firstOrderCommutatorMajorantEnergy
      u t i j := by

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

  unfold firstOrderCommutatorMajorantEnergy
  unfold spatialSquareEnergy

  rw [MeasureTheory.integral_const_mul]

  have hFunctionSplit :
      (
        fun x : Point3 =>
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
        =
      (
        fun x : Point3 =>
          3
            *
          (
            spatial3.d
                i
                (loggedVelocityComponent u t j)
                x
          ) ^ 2
      )
        +
      (
        (
          fun x : Point3 =>
            (
              spatial3.d
                  xAxis
                  (loggedVelocityComponent u t j)
                  x
            ) ^ 2
        )
          +
        (
          (
            fun x : Point3 =>
              (
                spatial3.d
                    yAxis
                    (loggedVelocityComponent u t j)
                    x
              ) ^ 2
          )
            +
          (
            fun x : Point3 =>
              (
                spatial3.d
                    zAxis
                    (loggedVelocityComponent u t j)
                    x
              ) ^ 2
          )
        )
      ) := by

    funext x
    rfl

  rw [hFunctionSplit]

  have hTopIntegral :
      MeasureTheory.integral
          volume
          (
            (
              fun x : Point3 =>
                3
                  *
                (
                  spatial3.d
                      i
                      (loggedVelocityComponent u t j)
                      x
                ) ^ 2
            )
              +
            (
              (
                fun x : Point3 =>
                  (
                    spatial3.d
                        xAxis
                        (loggedVelocityComponent u t j)
                        x
                  ) ^ 2
              )
                +
              (
                (
                  fun x : Point3 =>
                    (
                      spatial3.d
                          yAxis
                          (loggedVelocityComponent u t j)
                          x
                    ) ^ 2
                )
                  +
                (
                  fun x : Point3 =>
                    (
                      spatial3.d
                          zAxis
                          (loggedVelocityComponent u t j)
                          x
                    ) ^ 2
                )
              )
            )
          )
        =
      (
        ∫ x : Point3,
          3
            *
          (
            spatial3.d
                i
                (loggedVelocityComponent u t j)
                x
          ) ^ 2
      )
        +
      ∫ x : Point3,
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
        ) := by

    change
      (
        ∫ x : Point3,
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
        =
      (
        ∫ x : Point3,
          3
            *
          (
            spatial3.d
                i
                (loggedVelocityComponent u t j)
                x
          ) ^ 2
      )
        +
      ∫ x : Point3,
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

    exact
      MeasureTheory.integral_add
        (hI.const_mul 3)
        (hX.add (hY.add hZ))

  rw [hTopIntegral]

  rw [MeasureTheory.integral_const_mul]

  have hMiddleIntegral :
      (
        ∫ x : Point3,
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
        =
      (
        ∫ x : Point3,
          (
            spatial3.d
                xAxis
                (loggedVelocityComponent u t j)
                x
          ) ^ 2
      )
        +
      ∫ x : Point3,
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
        ) ^ 2 := by

    exact
      MeasureTheory.integral_add
        hX
        (hY.add hZ)

  rw [hMiddleIntegral]

  rw [
    MeasureTheory.integral_add
      hY
      hZ
  ]

/--
One first-order commutator pairing is bounded directly by its square-energy
majorant.
-/
theorem spatialEnergyPairing_firstTransportCommutator_le_majorantEnergy
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
    h t
      *
    firstOrderCommutatorMajorantEnergy
      u t i j := by

  calc
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
        ) :=
      spatialEnergyPairing_firstTransportCommutator_le_integral
        hGradient
        hH3
        hPairing
        i j
    _ =
      h t
        *
      firstOrderCommutatorMajorantEnergy
        u t i j :=
      integral_firstOrderCommutatorMajorant_eq
        hH3
        i j

/--
Summing the coordinate majorants produces exactly six copies of the canonical
first-order H³ energy.
-/
theorem sum_firstOrderCommutatorMajorantEnergy_eq
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) :
    (
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          firstOrderCommutatorMajorantEnergy
            u t i j
    )
      =
    6 * velocityH3Energy1At u t := by

  classical

  unfold firstOrderCommutatorMajorantEnergy
  unfold velocityH3Energy1At

  simp only [axis_sum_three]

  ring

/--
The complete first-order H³ transport derivative obeys the expected tame
estimate

    |T₁(t)| ≤ 6 h(t) E₁(t).

The assumptions separate the analytic inputs cleanly:
* `hFlux` supplies whole-space cancellation of the pure transport piece;
* `hPairing` supplies the pairing integrability needed for that split;
* `hH3` supplies square integrability of the first derivatives;
* `hGradient` supplies the pointwise `L∞` first-gradient envelope.
-/
theorem velocityH3TransportDerivative1At_le_gradientEnvelope
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
        H3FirstDerivativeTransportFluxVanishesAt
          u t
    )
    (
      hPairing :
        H3OrderOneTransportPairingIntegrableAt
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
          velocityH3TransportDerivative1At
            u t
        )
      ≤
    6 * h t * velocityH3Energy1At u t := by

  classical

  rw [
    velocityH3TransportDerivative1At_eq_commutator
      hClass
      ht
      hFlux
      hPairing
  ]

  let pairing :
      PrimeTensor.Axis Depth.three →
      PrimeTensor.Axis Depth.three →
      ℝ :=
    fun j i =>
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

  change
    abs
        (
          ∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              pairing j i
        )
      ≤
    6 * h t * velocityH3Energy1At u t

  have hInner :
      ∀ j : PrimeTensor.Axis Depth.three,
        abs
            (
              ∑ i : PrimeTensor.Axis Depth.three,
                pairing j i
            )
          ≤
        ∑ i : PrimeTensor.Axis Depth.three,
          abs (pairing j i) := by

    intro j

    simpa only [Real.norm_eq_abs] using
      (
        norm_sum_le
          (Finset.univ :
            Finset (PrimeTensor.Axis Depth.three))
          (fun i => pairing j i)
      )

  have hOuter :
      abs
          (
            ∑ j : PrimeTensor.Axis Depth.three,
              ∑ i : PrimeTensor.Axis Depth.three,
                pairing j i
          )
        ≤
      ∑ j : PrimeTensor.Axis Depth.three,
        abs
          (
            ∑ i : PrimeTensor.Axis Depth.three,
              pairing j i
          ) := by

    simpa only [Real.norm_eq_abs] using
      (
        norm_sum_le
          (Finset.univ :
            Finset (PrimeTensor.Axis Depth.three))
          (
            fun j =>
              ∑ i : PrimeTensor.Axis Depth.three,
                pairing j i
          )
      )

  have hTriangle :
      abs
          (
            ∑ j : PrimeTensor.Axis Depth.three,
              ∑ i : PrimeTensor.Axis Depth.three,
                pairing j i
          )
        ≤
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          abs (pairing j i) := by

    exact
      le_trans
        hOuter
        (
          Finset.sum_le_sum
            (fun j _ =>
              hInner j)
        )

  have hPairBound :
      (
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            abs (pairing j i)
      )
        ≤
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          h t
            *
          firstOrderCommutatorMajorantEnergy
            u t i j := by

    apply Finset.sum_le_sum
    intro j hj

    apply Finset.sum_le_sum
    intro i hi

    unfold pairing

    exact
      spatialEnergyPairing_firstTransportCommutator_le_majorantEnergy
        hGradient
        hH3
        hPairing
        i j

  have hScaleSum :
      (
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            h t
              *
            firstOrderCommutatorMajorantEnergy
              u t i j
      )
        =
      h t
        *
      (
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            firstOrderCommutatorMajorantEnergy
              u t i j
      ) := by

    simp only [axis_sum_three]

    ring

  calc
    abs
        (
          ∑ j : PrimeTensor.Axis Depth.three,
            ∑ i : PrimeTensor.Axis Depth.three,
              pairing j i
        )
        ≤
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          abs (pairing j i) :=
      hTriangle
    _ ≤
      ∑ j : PrimeTensor.Axis Depth.three,
        ∑ i : PrimeTensor.Axis Depth.three,
          h t
            *
          firstOrderCommutatorMajorantEnergy
            u t i j :=
      hPairBound
    _ =
      h t
        *
      (
        ∑ j : PrimeTensor.Axis Depth.three,
          ∑ i : PrimeTensor.Axis Depth.three,
            firstOrderCommutatorMajorantEnergy
              u t i j
      ) :=
      hScaleSum
    _ =
      h t
        *
      (
        6 * velocityH3Energy1At u t
      ) := by
        rw [
          sum_firstOrderCommutatorMajorantEnergy_eq
            u t
        ]
    _ =
      6 * h t * velocityH3Energy1At u t := by
        ring

end Euclidean
end Bridge
end PrimeTensor
