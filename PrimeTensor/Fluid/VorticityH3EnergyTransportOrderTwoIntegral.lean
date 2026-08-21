import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderTwoBound

/-!
# Integrated second-order H³ transport commutator bound

The preceding module proves the pointwise estimate

    2 |(∂ᵢ∂ₖvⱼ) C₂(i,k,j)|
      ≤
    h(t) M₂(i,k,j,x),

where `M₂` is an explicit sum of second-derivative squares.

Every square occurring in `M₂` is already part of `VelocityH3IntegrableAt`.
Thus the order-two pointwise estimate integrates directly, with no Sobolev
interpolation and no new analytic hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable local instance axisFintypeH3EnergyTransportOrderTwoIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
Every second derivative square appearing in the canonical H³ energy is
integrable.
-/
private theorem secondDerivativeSquare_integrable
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
The explicit second-order commutator majorant is integrable whenever the
canonical H³ square fields are integrable.
-/
theorem secondOrderCommutatorMajorantDensity_integrable
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
    MeasureTheory.Integrable
      (
        secondOrderCommutatorMajorantDensity
          u t i k j
      ) := by

  have hF :=
    secondDerivativeSquare_integrable
      hH3 j i k

  have hX1 :=
    secondDerivativeSquare_integrable
      hH3 xAxis i k

  have hX2 :=
    secondDerivativeSquare_integrable
      hH3 j i xAxis

  have hX3 :=
    secondDerivativeSquare_integrable
      hH3 j xAxis k

  have hY1 :=
    secondDerivativeSquare_integrable
      hH3 yAxis i k

  have hY2 :=
    secondDerivativeSquare_integrable
      hH3 j i yAxis

  have hY3 :=
    secondDerivativeSquare_integrable
      hH3 j yAxis k

  have hZ1 :=
    secondDerivativeSquare_integrable
      hH3 zAxis i k

  have hZ2 :=
    secondDerivativeSquare_integrable
      hH3 j i zAxis

  have hZ3 :=
    secondDerivativeSquare_integrable
      hH3 j zAxis k

  unfold secondOrderCommutatorMajorantDensity

  exact
    (hF.const_mul 9).add
      (
        (hX1.add (hX2.add hX3)).add
          (
            (hY1.add (hY2.add hY3)).add
              (hZ1.add (hZ2.add hZ3))
          )
      )

/--
The absolute value of one second-order commutator pairing is bounded by the
integral of its pointwise gradient-envelope majorant.
-/
theorem spatialEnergyPairing_secondTransportCommutator_le_integral
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
    ∫ x : Point3,
      h t
        *
      secondOrderCommutatorMajorantDensity
        u t i k j x := by

  let prod : Point3 → ℝ :=
    fun x =>
      spatial3.d
          i
          (
            spatial3.d
              k
              (loggedVelocityComponent u t j)
          )
          x
        *
      secondTransportCommutator
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t i k j x

  let majorant : Point3 → ℝ :=
    fun x =>
      h t
        *
      secondOrderCommutatorMajorantDensity
        u t i k j x

  have hProd :
      MeasureTheory.Integrable
        prod := by

    unfold prod

    have hComponent :
        loggedVelocityComponent u t j
          =
        (
          fun y =>
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u t y
            ).component j
        ) := by
      rfl

    rw [hComponent]

    exact
      (hPairing i k j).1

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
          secondOrderCommutatorMajorantDensity
            u t i k j
        ) :=
    secondOrderCommutatorMajorantDensity_integrable
      hH3 i k j

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
      secondTransportCommutator_density_le_gradientEnvelope
        hClass
        ht
        hGradient
        i k j x

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
