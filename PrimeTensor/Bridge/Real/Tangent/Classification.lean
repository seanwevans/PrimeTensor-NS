import PrimeTensor.Bridge.Real.Tangent.Continuity
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Classification of controlled native tangent maps

A native `MulTangentMap` is multiplicative.  Under the canonical logarithmic
equivalence with `ℝ`, it becomes an additive endomorphism of the real line.

The previous bridge proves that intrinsic `ScaleControlled` implies continuity
at zero of this additive conjugate.  Standard topological-group and real-vector
space results then give:

* continuity at zero -> global continuity;
* continuous additive map over `ℝ` -> `ℝ`-linearity.

Since `ℝ` is one-dimensional over itself, the conjugated tangent is therefore
multiplication by the single scalar `T(1)`.

Equivalently, every scale-controlled native tangent map satisfies

    logValue (D x) = slope(D) * logValue x.

This is the canonical scalar derivative coefficient in logarithmic
coordinates.
-/

namespace PrimeTensor
namespace Bridge
namespace MulTangentMap

/--
The real scalar carried by a native tangent morphism: its real additive
conjugate evaluated at `1`.
-/
noncomputable def slope
    (D : PrimeTensor.MulTangentMap) : ℝ :=
  PrimeTensor.Bridge.MulTangentMap.realAdditive D 1

/--
Scale control makes the real additive conjugate globally continuous.
-/
theorem scaleControlled_realAdditive_continuous
    {D : PrimeTensor.MulTangentMap}
    (hControlled :
      PrimeTensor.MulTangentMap.ScaleControlled D) :
    Continuous
      (PrimeTensor.Bridge.MulTangentMap.realAdditive D) := by

  exact
    continuous_of_continuousAt_zero
      (PrimeTensor.Bridge.MulTangentMap.realAdditive D)
      (
        PrimeTensor.Bridge.MulTangentMap.scaleControlled_realAdditive_continuousAt_zero
          hControlled
      )

/--
A scale-controlled native tangent conjugates to multiplication by one real
scalar.
-/
theorem realAdditive_eq_mul_slope
    {D : PrimeTensor.MulTangentMap}
    (hControlled :
      PrimeTensor.MulTangentMap.ScaleControlled D)
    (r : ℝ) :
    PrimeTensor.Bridge.MulTangentMap.realAdditive D r
      =
    r *
      PrimeTensor.Bridge.MulTangentMap.slope D := by

  have hLinear :=
    map_real_smul
      (PrimeTensor.Bridge.MulTangentMap.realAdditive D)
      (
        PrimeTensor.Bridge.MulTangentMap.scaleControlled_realAdditive_continuous
          hControlled
      )
      r
      (1 : ℝ)

  unfold slope

  simpa [smul_eq_mul] using hLinear

/--
Equivalent orientation of the scalar classification.
-/
theorem realAdditive_eq_slope_mul
    {D : PrimeTensor.MulTangentMap}
    (hControlled :
      PrimeTensor.MulTangentMap.ScaleControlled D)
    (r : ℝ) :
    PrimeTensor.Bridge.MulTangentMap.realAdditive D r
      =
    PrimeTensor.Bridge.MulTangentMap.slope D *
      r := by

  rw [
    PrimeTensor.Bridge.MulTangentMap.realAdditive_eq_mul_slope
      hControlled
      r
  ]

  exact mul_comm r _

/--
The logarithmic response of a controlled native tangent is multiplication by
its unique real slope.
-/
theorem logValue_apply_eq_slope_mul
    {D : PrimeTensor.MulTangentMap}
    (hControlled :
      PrimeTensor.MulTangentMap.ScaleControlled D)
    (x : PrimeTensor.MulReal) :
    PrimeTensor.Bridge.MulReal.logValue
        (D x)
      =
    PrimeTensor.Bridge.MulTangentMap.slope D *
      PrimeTensor.Bridge.MulReal.logValue x := by

  have hConj :=
    PrimeTensor.Bridge.MulTangentMap.realConjugate_logValue
      D x

  have hScalar :=
    PrimeTensor.Bridge.MulTangentMap.realAdditive_eq_slope_mul
      hControlled
      (PrimeTensor.Bridge.MulReal.logValue x)

  rw [
    PrimeTensor.Bridge.MulTangentMap.realAdditive_apply
  ] at hScalar

  rw [hConj] at hScalar

  exact hScalar

/--
Right-oriented version of the logarithmic scalar response.
-/
theorem logValue_apply_eq_mul_slope
    {D : PrimeTensor.MulTangentMap}
    (hControlled :
      PrimeTensor.MulTangentMap.ScaleControlled D)
    (x : PrimeTensor.MulReal) :
    PrimeTensor.Bridge.MulReal.logValue
        (D x)
      =
    PrimeTensor.Bridge.MulReal.logValue x *
      PrimeTensor.Bridge.MulTangentMap.slope D := by

  rw [
    PrimeTensor.Bridge.MulTangentMap.logValue_apply_eq_slope_mul
      hControlled
      x
  ]

  exact
    mul_comm
      (PrimeTensor.Bridge.MulTangentMap.slope D)
      (PrimeTensor.Bridge.MulReal.logValue x)

/--
A controlled native tangent is completely determined by its real slope.
-/
theorem eq_of_slope_eq
    {D E : PrimeTensor.MulTangentMap}
    (hD :
      PrimeTensor.MulTangentMap.ScaleControlled D)
    (hE :
      PrimeTensor.MulTangentMap.ScaleControlled E)
    (hSlope :
      PrimeTensor.Bridge.MulTangentMap.slope D =
        PrimeTensor.Bridge.MulTangentMap.slope E) :
    D = E := by

  cases D with
  | mk Dfun Done Dmul Dinv =>
      cases E with
      | mk Efun Eone Emul Einv =>

          congr

          funext x

          apply
            PrimeTensor.Bridge.MulReal.logValue_injective

          rw [
            PrimeTensor.Bridge.MulTangentMap.logValue_apply_eq_slope_mul
              hD
              x,
            PrimeTensor.Bridge.MulTangentMap.logValue_apply_eq_slope_mul
              hE
              x,
            hSlope
          ]

/--
The identity native tangent has scalar slope `1`.
-/
@[simp]
theorem slope_identity :
    PrimeTensor.Bridge.MulTangentMap.slope
        PrimeTensor.MulTangentMap.identity
      =
    1 := by

  unfold slope

  rw [
    PrimeTensor.Bridge.MulTangentMap.realAdditive_apply
  ]

  unfold
    PrimeTensor.Bridge.MulTangentMap.realConjugate

  rw [
    PrimeTensor.MulTangentMap.identity_apply
  ]

  change
    PrimeTensor.Bridge.MulReal.logEquiv
        (
          PrimeTensor.Bridge.MulReal.logEquiv.symm 1
        )
      =
    1

  exact
    PrimeTensor.Bridge.MulReal.logEquiv.apply_symm_apply
      1

/--
The trivial native tangent has scalar slope `0`.
-/
@[simp]
theorem slope_trivial :
    PrimeTensor.Bridge.MulTangentMap.slope
        PrimeTensor.MulTangentMap.trivial
      =
    0 := by

  unfold slope

  rw [
    PrimeTensor.Bridge.MulTangentMap.realAdditive_apply
  ]

  unfold
    PrimeTensor.Bridge.MulTangentMap.realConjugate

  rw [
    PrimeTensor.MulTangentMap.trivial_apply,
    PrimeTensor.Bridge.MulReal.logValue_one
  ]

end MulTangentMap
end Bridge
end PrimeTensor
