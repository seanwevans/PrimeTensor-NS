import PrimeTensor.Bridge.ConcreteLogDifferential
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Concrete Euclidean spatial and temporal differentials

We now specialize the abstract differential interface to ordinary Euclidean
coordinate derivatives.

Recall that

    Point ℝ dim = Axis dim → ℝ,

so the existing point type is already a finite coordinate tuple.  For one axis
`i`, the coordinate line through `x` is obtained by replacing only coordinate
`i` by the real parameter `t`.  The ordinary partial derivative is then the
one-variable derivative of the field restricted to this coordinate line.

Time is specialized to `ℝ`, with the usual one-variable derivative.

These real operators are then pulled back through the completed logarithmic
equivalence to obtain the corresponding native multiplicative spatial and
temporal differentials.

The construction is dimension-generic.  The final section specializes it to
`Depth.three`, giving the concrete three-dimensional carrier used by the
Navier--Stokes bridge.

Important: `deriv` is a total Mathlib operator, so classical-solution
regularity is intentionally handled in a separate layer.  The specification
lemmas below show that whenever a coordinate restriction actually has a
`HasDerivAt`, the differential evaluates to that genuine derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
A coordinate line through a Euclidean point: all coordinates are frozen except
axis `i`, whose value is replaced by `t`.
-/
noncomputable def coordinateLine
    {dim : Depth}
    (x : PrimeTensor.Point ℝ dim)
    (i : PrimeTensor.Axis dim)
    (t : ℝ) :
    PrimeTensor.Point ℝ dim := by

  classical

  exact
    Function.update x i t

@[simp]
theorem coordinateLine_same
    {dim : Depth}
    (x : PrimeTensor.Point ℝ dim)
    (i : PrimeTensor.Axis dim)
    (t : ℝ) :
    coordinateLine x i t i = t := by

  classical

  unfold coordinateLine

  simp

theorem coordinateLine_other
    {dim : Depth}
    (x : PrimeTensor.Point ℝ dim)
    {i j : PrimeTensor.Axis dim}
    (hji : j ≠ i)
    (t : ℝ) :
    coordinateLine x i t j = x j := by

  classical

  unfold coordinateLine

  simp [hji]

@[simp]
theorem coordinateLine_at_base
    {dim : Depth}
    (x : PrimeTensor.Point ℝ dim)
    (i : PrimeTensor.Axis dim) :
    coordinateLine x i (x i) = x := by

  classical

  funext j

  by_cases hji : j = i

  · subst j
    simp [coordinateLine]

  · simp [coordinateLine, hji]

/--
Ordinary Euclidean partial derivative along one coordinate axis.
-/
noncomputable def partialDeriv
    {dim : Depth}
    (i : PrimeTensor.Axis dim)
    (f : PrimeTensor.ScalarField ℝ ℝ dim)
    (x : PrimeTensor.Point ℝ dim) : ℝ :=
  deriv
    (
      fun t : ℝ =>
        f (coordinateLine x i t)
    )
    (x i)

/--
The concrete real spatial differential on `Point ℝ dim`.
-/
noncomputable def spatial
    (dim : Depth) :
    PrimeTensor.Differential ℝ ℝ dim where

  d :=
    fun i f x =>
      partialDeriv i f x

@[simp]
theorem spatial_d
    {dim : Depth}
    (i : PrimeTensor.Axis dim)
    (f : PrimeTensor.ScalarField ℝ ℝ dim)
    (x : PrimeTensor.Point ℝ dim) :
    (spatial dim).d i f x =
      partialDeriv i f x := by
  rfl

/--
Specification of the Euclidean partial derivative at every point where the
coordinate-line restriction has the stated derivative.
-/
theorem partialDeriv_eq_of_hasDerivAt
    {dim : Depth}
    {i : PrimeTensor.Axis dim}
    {f : PrimeTensor.ScalarField ℝ ℝ dim}
    {x : PrimeTensor.Point ℝ dim}
    {v : ℝ}
    (
      h :
        HasDerivAt
          (
            fun t : ℝ =>
              f (coordinateLine x i t)
          )
          v
          (x i)
    ) :
    partialDeriv i f x = v := by

  unfold partialDeriv

  exact h.deriv

/--
Equivalent specification phrased through the `Differential` interface.
-/
theorem spatial_d_eq_of_hasDerivAt
    {dim : Depth}
    {i : PrimeTensor.Axis dim}
    {f : PrimeTensor.ScalarField ℝ ℝ dim}
    {x : PrimeTensor.Point ℝ dim}
    {v : ℝ}
    (
      h :
        HasDerivAt
          (
            fun t : ℝ =>
              f (coordinateLine x i t)
          )
          v
          (x i)
    ) :
    (spatial dim).d i f x = v := by

  exact
    partialDeriv_eq_of_hasDerivAt h

/--
Ordinary one-dimensional real time derivative.
-/
noncomputable def temporal :
    PrimeTensor.TemporalDifferential ℝ ℝ where

  d :=
    fun f t =>
      deriv f t

@[simp]
theorem temporal_d
    (f : ℝ → ℝ)
    (t : ℝ) :
    temporal.d f t =
      deriv f t := by
  rfl

/--
Specification of the real temporal differential whenever the genuine
one-variable derivative exists.
-/
theorem temporal_d_eq_of_hasDerivAt
    {f : ℝ → ℝ}
    {t v : ℝ}
    (h : HasDerivAt f v t) :
    temporal.d f t = v := by

  unfold temporal

  exact h.deriv

/--
Canonical native multiplicative spatial differential over Euclidean
coordinates.
-/
noncomputable def mulSpatial
    (dim : Depth) :
    PrimeTensor.Differential
      ℝ PrimeTensor.MulReal dim :=
  PrimeTensor.Bridge.Differential.logPullback
    (spatial dim)

/--
Canonical native multiplicative time differential over ordinary real time.
-/
noncomputable def mulTemporal :
    PrimeTensor.TemporalDifferential
      ℝ PrimeTensor.MulReal :=
  PrimeTensor.Bridge.TemporalDifferential.logPullback
    temporal

/--
The Euclidean multiplicative spatial differential has exact logarithmic
semantics.
-/
theorem mulSpatial_compatible
    (dim : Depth) :
    PrimeTensor.Bridge.SpatialLogCompatible
      (mulSpatial dim)
      (spatial dim) :=

  PrimeTensor.Bridge.Differential.logPullback_compatible
    (spatial dim)

/--
The Euclidean multiplicative temporal differential has exact logarithmic
semantics.
-/
theorem mulTemporal_compatible :
    PrimeTensor.Bridge.TemporalLogCompatible
      mulTemporal
      temporal :=

  PrimeTensor.Bridge.TemporalDifferential.logPullback_compatible
    temporal

/--
Three-dimensional Euclidean point carrier.
-/
abbrev Point3 :=
  PrimeTensor.Point ℝ Depth.three

/--
Three-dimensional ordinary scalar field.
-/
abbrev ScalarField3 :=
  PrimeTensor.ScalarField ℝ ℝ Depth.three

/--
Three-dimensional ordinary vector field.
-/
abbrev VectorField3 :=
  PrimeTensor.VectorField ℝ ℝ Depth.three

/--
The first conventional spatial axis.
-/
def xAxis :
    PrimeTensor.Axis Depth.three :=
  .first

/--
The second conventional spatial axis.
-/
def yAxis :
    PrimeTensor.Axis Depth.three :=
  .next .first

/--
The third conventional spatial axis.
-/
def zAxis :
    PrimeTensor.Axis Depth.three :=
  .next (.next .first)

/--
The axis fold in dimension three is exactly the expected three-term fold.
-/
@[simp]
theorem axis_fold_three
    {A : Type}
    (op : A → A → A)
    (f : PrimeTensor.Axis Depth.three → A) :
    PrimeTensor.Axis.fold op Depth.three f =
      op
        (f xAxis)
        (
          op
            (f yAxis)
            (f zAxis)
        ) := by
  rfl

/--
Concrete ordinary spatial derivative for three-dimensional Euclidean space.
-/
noncomputable def spatial3 :
    PrimeTensor.Differential
      ℝ ℝ Depth.three :=
  spatial Depth.three

/--
Concrete native multiplicative spatial derivative for three-dimensional
Euclidean space.
-/
noncomputable def mulSpatial3 :
    PrimeTensor.Differential
      ℝ PrimeTensor.MulReal Depth.three :=
  mulSpatial Depth.three

/--
Exact compatibility for the concrete three-dimensional Euclidean spatial
derivative.
-/
theorem mulSpatial3_compatible :
    PrimeTensor.Bridge.SpatialLogCompatible
      mulSpatial3
      spatial3 := by

  exact
    mulSpatial_compatible
      Depth.three

end Euclidean

namespace PrimePairApprox

/--
A multiplicative fluid solution over real time and concrete three-dimensional
Euclidean space maps canonically to the corresponding ordinary real fluid
solution.
-/
noncomputable def LogProductSolution.toRealEuclidean3
    (
      s :
        LogProductSolution
          PrimeTensor.Bridge.Euclidean.mulTemporal
          PrimeTensor.Bridge.Euclidean.mulSpatial3
    ) :
    RealFluid.Solution
      PrimeTensor.Bridge.Euclidean.temporal
      PrimeTensor.Bridge.Euclidean.spatial3 :=

  s.toReal
    PrimeTensor.Bridge.Euclidean.mulTemporal_compatible
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible

@[simp]
theorem LogProductSolution.toRealEuclidean3_velocity
    (
      s :
        LogProductSolution
          PrimeTensor.Bridge.Euclidean.mulTemporal
          PrimeTensor.Bridge.Euclidean.mulSpatial3
    ) :
    s.toRealEuclidean3.velocity =
      logSpaceTimeVectorField s.velocity := by
  rfl

@[simp]
theorem LogProductSolution.toRealEuclidean3_pressure
    (
      s :
        LogProductSolution
          PrimeTensor.Bridge.Euclidean.mulTemporal
          PrimeTensor.Bridge.Euclidean.mulSpatial3
    ) :
    s.toRealEuclidean3.pressure =
      logSpaceTimeScalarField s.pressure := by
  rfl

end PrimePairApprox

end Bridge
end PrimeTensor
