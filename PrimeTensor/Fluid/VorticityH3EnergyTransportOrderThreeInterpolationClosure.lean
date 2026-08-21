import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderThreeInterpolationFrontier

/-!
# Third-order H³ transport: conditional interpolation closure

All algebraic and measure-theoretic work around the top-order transport term is
completed here.

The exact commutator split is lifted through the spatial energy pairing and
through all four finite coordinate sums:

    T₃(t) = G₃(t) + I₃(t).

The gradient contribution `G₃` is already bounded by `24 h(t) E₃(t)`.
Therefore any proof of the explicit interpolation frontier

    |I₃(t)| ≤ C h(t) E₃(t)

immediately yields

    |T₃(t)| ≤ (24 + C) h(t) E₃(t).

No interpolation theorem is proved in this file; the remaining analytic
obligation is used only through `H3OrderThreeInterpolationEstimateAt`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyTransportOrderThreeInterpolationClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
The unsplit four-index sum of third-order commutator pairings.
-/
noncomputable def thirdOrderCommutatorTransportSum
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three,
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
              thirdTransportCommutator
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j
            )

/--
Lift the exact pointwise split `C₃ = G₃ + I₃` through the spatial energy
pairing and the complete four-index coordinate sum.
-/
theorem thirdOrderCommutatorTransportSum_eq_gradient_add_interpolation
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
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
      hGradPairing :
        H3OrderThreeGradientPairingIntegrableAt
          u t
    )
    (
      hInterpPairing :
        H3OrderThreeInterpolationPairingIntegrableAt
          u t
    ) :
    thirdOrderCommutatorTransportSum
        u t
      =
    thirdOrderGradientTransportSum
        u t
      +
    thirdOrderInterpolationTransportSum
        u t := by

  classical

  rcases hClass.pressure_witness with
    ⟨
      p,
      s,
      hp4
    ⟩

  have htNS :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans
        hClass.terminal_start.1
        ht.1,
      ht.2
    ⟩

  unfold
    thirdOrderCommutatorTransportSum
    thirdOrderGradientTransportSum
    thirdOrderInterpolationTransportSum

  rw [← Finset.sum_add_distrib]

  apply Finset.sum_congr rfl
  intro j hj

  rw [← Finset.sum_add_distrib]

  apply Finset.sum_congr rfl
  intro i hi

  rw [← Finset.sum_add_distrib]

  apply Finset.sum_congr rfl
  intro k hk

  rw [← Finset.sum_add_distrib]

  apply Finset.sum_congr rfl
  intro l hl

  let f : ScalarField3 :=
    spatial3.d i
      (
        spatial3.d k
          (
            spatial3.d l
              (loggedVelocityComponent u t j)
          )
      )

  let g : ScalarField3 :=
    thirdTransportCommutatorGradientBlock
      (
        PrimeTensor.Bridge.logSpaceTimeVectorField
          u
      )
      t i k l j

  let q : ScalarField3 :=
    thirdTransportCommutatorInterpolationBlock
      (
        PrimeTensor.Bridge.logSpaceTimeVectorField
          u
      )
      t i k l j

  have hSplit :
      thirdTransportCommutator
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          t i k l j
        =
      fun x : Point3 =>
        g x + q x := by

    funext x

    unfold g q

    exact
      thirdTransportCommutator_eq_gradient_add_interpolation
        s
        htNS
        x
        i k l j

  rw [hSplit]

  change
    spatialEnergyPairing
        f
        (
          fun x : Point3 =>
            g x + q x
        )
      =
    spatialEnergyPairing f g
      +
    spatialEnergyPairing f q

  exact
    spatialEnergyPairing_add_of_integrable
      (hGradPairing i k l j)
      (hInterpPairing i k l j)

/--
The actual third-order H³ transport derivative is exactly the sum of the
already-controlled gradient block and the explicit interpolation frontier.
-/
theorem velocityH3TransportDerivative3At_eq_gradient_add_interpolation
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
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
      hRegular :
        H3OrderThreeTransportRegularityAt
          u t
    )
    (
      hFlux :
        H3ThirdDerivativeTransportFluxVanishesAt
          u t
    )
    (
      hPairing :
        H3OrderThreeTransportPairingIntegrableAt
          u t
    )
    (
      hGradPairing :
        H3OrderThreeGradientPairingIntegrableAt
          u t
    )
    (
      hInterpPairing :
        H3OrderThreeInterpolationPairingIntegrableAt
          u t
    ) :
    velocityH3TransportDerivative3At
        u t
      =
    thirdOrderGradientTransportSum
        u t
      +
    thirdOrderInterpolationTransportSum
        u t := by

  rw [
    velocityH3TransportDerivative3At_eq_commutator
      hClass
      ht
      hRegular
      hFlux
      hPairing
  ]

  change
    thirdOrderCommutatorTransportSum
        u t
      =
    thirdOrderGradientTransportSum
        u t
      +
    thirdOrderInterpolationTransportSum
        u t

  exact
    thirdOrderCommutatorTransportSum_eq_gradient_add_interpolation
      hClass
      ht
      hGradPairing
      hInterpPairing

/--
Conditional closure of the complete third-order transport estimate.

Once the explicit interpolation frontier is discharged with constant `C`, the
whole top-order transport derivative obeys

    |T₃(t)| ≤ (24 + C) h(t) E₃(t).
-/
theorem velocityH3TransportDerivative3At_le_of_interpolation
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {a T t C : ℝ}
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
      hRegular :
        H3OrderThreeTransportRegularityAt
          u t
    )
    (
      hFlux :
        H3ThirdDerivativeTransportFluxVanishesAt
          u t
    )
    (
      hPairing :
        H3OrderThreeTransportPairingIntegrableAt
          u t
    )
    (
      hGradPairing :
        H3OrderThreeGradientPairingIntegrableAt
          u t
    )
    (
      hInterpPairing :
        H3OrderThreeInterpolationPairingIntegrableAt
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
    )
    (
      hInterp :
        H3OrderThreeInterpolationEstimateAt
          u h t C
    ) :
    abs
        (
          velocityH3TransportDerivative3At
            u t
        )
      ≤
    (24 + C) * h t * velocityH3Energy3At u t := by

  rw [
    velocityH3TransportDerivative3At_eq_gradient_add_interpolation
      hClass
      ht
      hRegular
      hFlux
      hPairing
      hGradPairing
      hInterpPairing
  ]

  have hTriangle :
      abs
          (
            thirdOrderGradientTransportSum u t
              +
            thirdOrderInterpolationTransportSum u t
          )
        ≤
      abs
          (
            thirdOrderGradientTransportSum u t
          )
        +
      abs
          (
            thirdOrderInterpolationTransportSum u t
          ) :=
    abs_add_le
      (thirdOrderGradientTransportSum u t)
      (thirdOrderInterpolationTransportSum u t)

  have hGradientBound :
      abs
          (
            thirdOrderGradientTransportSum
              u t
          )
        ≤
      24 * h t * velocityH3Energy3At u t :=
    thirdOrderGradientTransportSum_named_le_gradientEnvelope
      hGradient
      hH3
      hGradPairing

  have hInterpolationBound :
      abs
          (
            thirdOrderInterpolationTransportSum
              u t
          )
        ≤
      C * h t * velocityH3Energy3At u t :=
    hInterp.bound

  calc
    abs
        (
          thirdOrderGradientTransportSum u t
            +
          thirdOrderInterpolationTransportSum u t
        )
        ≤
      abs
          (
            thirdOrderGradientTransportSum u t
          )
        +
      abs
          (
            thirdOrderInterpolationTransportSum u t
          ) :=
      hTriangle
    _ ≤
      24 * h t * velocityH3Energy3At u t
        +
      C * h t * velocityH3Energy3At u t := by
        exact
          add_le_add
            hGradientBound
            hInterpolationBound
    _ =
      (24 + C) * h t * velocityH3Energy3At u t := by
        ring

end Euclidean
end Bridge
end PrimeTensor
