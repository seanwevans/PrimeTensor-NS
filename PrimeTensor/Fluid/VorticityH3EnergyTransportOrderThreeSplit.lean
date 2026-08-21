import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderThreeExpansion

/-!
# Third-order H³ transport: gradient/interpolation split

The explicit order-three commutator has seven terms per velocity axis.  Four
contain one first derivative and one third derivative; three contain two second
derivatives.

This file separates those two analytic classes canonically:

    C₃ = G₃ + I₃

where `G₃` is the gradient-envelope block and `I₃` is the genuinely new
interpolation block.

No estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/--
The four `D³u · Du` terms contributed by one velocity axis.
-/
noncomputable def thirdTransportCommutatorAxisGradientBlock
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k l j r : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    (
      spatial3.d i
        (spatial3.d k
          (spatial3.d l
            (fun q => (v t q).component r))) x
        *
      spatial3.d r
        (fun q => (v t q).component j) x
    )
      +
    (
      spatial3.d l
        (fun q => (v t q).component r) x
        *
      spatial3.d i
        (spatial3.d k
          (spatial3.d r
            (fun q => (v t q).component j))) x
    )
      +
    (
      spatial3.d k
        (fun q => (v t q).component r) x
        *
      spatial3.d i
        (spatial3.d r
          (spatial3.d l
            (fun q => (v t q).component j))) x
    )
      +
    (
      spatial3.d i
        (fun q => (v t q).component r) x
        *
      spatial3.d r
        (spatial3.d k
          (spatial3.d l
            (fun q => (v t q).component j))) x
    )

/--
The three `D²u · D²u` terms contributed by one velocity axis.
-/
noncomputable def thirdTransportCommutatorAxisInterpolationBlock
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k l j r : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    (
      spatial3.d k
        (spatial3.d l
          (fun q => (v t q).component r)) x
        *
      spatial3.d i
        (spatial3.d r
          (fun q => (v t q).component j)) x
    )
      +
    (
      spatial3.d i
        (spatial3.d l
          (fun q => (v t q).component r)) x
        *
      spatial3.d k
        (spatial3.d r
          (fun q => (v t q).component j)) x
    )
      +
    (
      spatial3.d i
        (spatial3.d k
          (fun q => (v t q).component r)) x
        *
      spatial3.d r
        (spatial3.d l
          (fun q => (v t q).component j)) x
    )

/--
One seven-term axis block is exactly the sum of its four gradient-envelope
terms and three interpolation terms.
-/
theorem thirdTransportCommutatorAxisBlock_eq_gradient_add_interpolation
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    (t : ℝ)
    (x : Point3)
    (i k l j r : PrimeTensor.Axis Depth.three) :
    thirdTransportCommutatorAxisBlock
        v t i k l j r x
      =
    thirdTransportCommutatorAxisGradientBlock
        v t i k l j r x
      +
    thirdTransportCommutatorAxisInterpolationBlock
        v t i k l j r x := by

  unfold
    thirdTransportCommutatorAxisBlock
    secondTransportCommutatorAxisDerivativeBlock
    thirdTransportCommutatorAxisGradientBlock
    thirdTransportCommutatorAxisInterpolationBlock

  ring

/--
The twelve `D³u · Du` terms in the full coordinate-expanded third commutator.
-/
noncomputable def thirdTransportCommutatorGradientBlock
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k l j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    thirdTransportCommutatorAxisGradientBlock
        v t i k l j xAxis x
      +
    (
      thirdTransportCommutatorAxisGradientBlock
          v t i k l j yAxis x
        +
      thirdTransportCommutatorAxisGradientBlock
          v t i k l j zAxis x
    )

/--
The nine `D²u · D²u` terms in the full coordinate-expanded third commutator.
-/
noncomputable def thirdTransportCommutatorInterpolationBlock
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k l j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    thirdTransportCommutatorAxisInterpolationBlock
        v t i k l j xAxis x
      +
    (
      thirdTransportCommutatorAxisInterpolationBlock
          v t i k l j yAxis x
        +
      thirdTransportCommutatorAxisInterpolationBlock
          v t i k l j zAxis x
    )

/--
The full 21-term coordinate expansion splits into the twelve easy
gradient-envelope terms and the nine hard interpolation terms.
-/
theorem thirdTransportCommutatorExpanded_eq_gradient_add_interpolation
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    (t : ℝ)
    (x : Point3)
    (i k l j : PrimeTensor.Axis Depth.three) :
    thirdTransportCommutatorExpanded
        v t i k l j x
      =
    thirdTransportCommutatorGradientBlock
        v t i k l j x
      +
    thirdTransportCommutatorInterpolationBlock
        v t i k l j x := by

  unfold thirdTransportCommutatorExpanded

  rw [
    thirdTransportCommutatorAxisBlock_eq_gradient_add_interpolation
      t x i k l j xAxis,
    thirdTransportCommutatorAxisBlock_eq_gradient_add_interpolation
      t x i k l j yAxis,
    thirdTransportCommutatorAxisBlock_eq_gradient_add_interpolation
      t x i k l j zAxis
  ]

  unfold
    thirdTransportCommutatorGradientBlock
    thirdTransportCommutatorInterpolationBlock

  ring

/--
The abstract third-order commutator itself has the same canonical split.
-/
theorem thirdTransportCommutator_eq_gradient_add_interpolation
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {T t : ℝ}
    (
      s :
        PreterminalNavierStokes3
          v p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (x : Point3)
    (i k l j : PrimeTensor.Axis Depth.three) :
    thirdTransportCommutator
        v t i k l j x
      =
    thirdTransportCommutatorGradientBlock
        v t i k l j x
      +
    thirdTransportCommutatorInterpolationBlock
        v t i k l j x := by

  rw [
    thirdTransportCommutator_eq_expanded
      s ht x i k l j
  ]

  exact
    thirdTransportCommutatorExpanded_eq_gradient_add_interpolation
      t x i k l j

end Euclidean
end Bridge
end PrimeTensor
