import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderThreeGradientTotalBound

/-!
# Third-order H³ transport: interpolation frontier

The third-order transport commutator has been split exactly into

* a twelve-term `D³u · Du` gradient block, now completely controlled by
  `24 * h(t) * E₃(t)`, and
* a nine-term `D²u · D²u` interpolation block.

This file gives the unresolved block a precise public interface.  No
Gagliardo--Nirenberg/Sobolev estimate is assumed silently.

The remaining analytic target is a constant `C` such that

    |I₃(t)| ≤ C * h(t) * E₃(t),

where `I₃(t)` is the complete four-index sum of interpolation-block pairings.

A later module may prove this interface from a concrete whole-space
Gagliardo--Nirenberg inequality.  Until then, it is an explicit frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyTransportOrderThreeInterpolationFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
The already-controlled twelve-term gradient contribution to the complete
third-order transport commutator.
-/
noncomputable def thirdOrderGradientTransportSum
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
              thirdTransportCommutatorGradientBlock
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j
            )

/--
The unresolved nine-term `D²u · D²u` contribution to the complete third-order
transport commutator.
-/
noncomputable def thirdOrderInterpolationTransportSum
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
              thirdTransportCommutatorInterpolationBlock
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                t i k l j
            )

/--
Integrability of the split interpolation-block pairing.

This is separate from `H3OrderThreeTransportPairingIntegrableAt`, which is an
integrability hypothesis for the unsplit third commutator, and separate from
`H3OrderThreeGradientPairingIntegrableAt`, which concerns the easy block.
-/
def H3OrderThreeInterpolationPairingIntegrableAt
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
          thirdTransportCommutatorInterpolationBlock
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k l j x
      )

/--
The exact remaining analytic estimate at one time.

`C` is the constant supplied by the eventual whole-space interpolation
argument.  Keeping `0 ≤ C` in the interface makes later monotonicity and
total-energy bookkeeping explicit.
-/
def H3OrderThreeInterpolationEstimateAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (h : ℝ → ℝ)
    (t C : ℝ) : Prop :=
  0 ≤ C
    ∧
  abs
      (
        thirdOrderInterpolationTransportSum
          u t
      )
    ≤
  C * h t * velocityH3Energy3At u t

/--
A tail-uniform version of the remaining interpolation estimate.
-/
def H3OrderThreeInterpolationEstimateOnTail
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (h : ℝ → ℝ)
    (a T C : ℝ) : Prop :=
  0 ≤ C
    ∧
  ∀ t : ℝ,
    t ∈ Set.Ioo a T →
      abs
          (
            thirdOrderInterpolationTransportSum
              u t
          )
        ≤
      C * h t * velocityH3Energy3At u t

/--
The completed gradient estimate in the new named-sum notation.
-/
theorem thirdOrderGradientTransportSum_named_le_gradientEnvelope
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
      hGradPairing :
        H3OrderThreeGradientPairingIntegrableAt
          u t
    ) :
    abs
        (
          thirdOrderGradientTransportSum
            u t
        )
      ≤
    24 * h t * velocityH3Energy3At u t := by

  unfold thirdOrderGradientTransportSum

  exact
    thirdOrderGradientTransportSum_le_gradientEnvelope
      hGradient
      hH3
      hGradPairing

/--
Project the pointwise interpolation bound from the explicit frontier package.
-/
theorem H3OrderThreeInterpolationEstimateAt.bound
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {t C : ℝ}
    (
      hInterp :
        H3OrderThreeInterpolationEstimateAt
          u h t C
    ) :
    abs
        (
          thirdOrderInterpolationTransportSum
            u t
        )
      ≤
    C * h t * velocityH3Energy3At u t :=
  hInterp.2

/--
Project the nonnegativity of the interpolation constant.
-/
theorem H3OrderThreeInterpolationEstimateAt.constant_nonneg
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {t C : ℝ}
    (
      hInterp :
        H3OrderThreeInterpolationEstimateAt
          u h t C
    ) :
    0 ≤ C :=
  hInterp.1

end Euclidean
end Bridge
end PrimeTensor
