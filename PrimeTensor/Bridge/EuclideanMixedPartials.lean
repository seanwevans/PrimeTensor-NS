import PrimeTensor.Bridge.EuclideanVortexStretching
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Commutation of Euclidean mixed partial derivatives

The concrete Euclidean differential was defined by restricting a scalar field
to one coordinate line and taking the ordinary one-variable derivative.

For the vorticity equation we now need the classical Schwarz/Clairaut fact:

    ∂ᵢ∂ⱼ f = ∂ⱼ∂ᵢ f

for spatially `C²` scalar fields.

Rather than postulating this as an additional fluid hypothesis, this file
connects our coordinate-line derivative to Mathlib's Fréchet derivative and
then invokes symmetry of the second Fréchet derivative.

The key coordinate vector is `axisDirection i`, the ordinary unit vector in
axis `i`.  We prove

    partialDeriv i f x = (fderiv ℝ f x) (axisDirection i)

whenever `f` is differentiable at `x`, and then identify nested partials with

    (fderiv ℝ (fderiv ℝ f) x) eᵢ eⱼ.

For `C²` fields Mathlib proves this bilinear second derivative symmetric,
yielding the desired mixed-partial commutation with no extra assumption.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable local instance axisFintypeMixed
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
The ordinary coordinate unit direction associated with an intrinsic axis.
-/
noncomputable def axisDirection
    {dim : Depth}
    (i : PrimeTensor.Axis dim) :
    PrimeTensor.Point ℝ dim := by

  classical

  exact
    Pi.single i 1

@[simp]
theorem axisDirection_same
    {dim : Depth}
    (i : PrimeTensor.Axis dim) :
    axisDirection i i = 1 := by

  classical

  simp [axisDirection]

theorem axisDirection_other
    {dim : Depth}
    {i j : PrimeTensor.Axis dim}
    (hji : j ≠ i) :
    axisDirection i j = 0 := by

  classical

  simp [axisDirection, hji]

/--
The coordinate line has derivative equal to the corresponding coordinate unit
direction at its base point.
-/
theorem coordinateLine_hasDerivAt
    {dim : Depth}
    (x : PrimeTensor.Point ℝ dim)
    (i : PrimeTensor.Axis dim) :
    HasDerivAt
      (coordinateLine x i)
      (axisDirection i)
      (x i) := by

  classical

  change
    HasDerivAt
      (Function.update x i)
      (Pi.single i 1)
      (x i)

  exact
    hasDerivAt_update
      (𝕜 := ℝ)
      x i (x i)

/--
A genuine coordinate partial derivative is the Fréchet derivative evaluated
on the corresponding coordinate unit direction.
-/
theorem partialDeriv_eq_fderiv_axisDirection
    {dim : Depth}
    {f :
      PrimeTensor.ScalarField ℝ ℝ dim}
    {x : PrimeTensor.Point ℝ dim}
    (i : PrimeTensor.Axis dim)
    (hf : DifferentiableAt ℝ f x) :
    partialDeriv i f x
      =
    (fderiv ℝ f x) (axisDirection i) := by

  have hComp :
      HasDerivAt
        (
          f ∘
            coordinateLine x i
        )
        (
          (fderiv ℝ f x)
            (axisDirection i)
        )
        (x i) := by

    exact
      hf.hasFDerivAt.comp_hasDerivAt_of_eq
        (x i)
        (coordinateLine_hasDerivAt x i)
        (coordinateLine_at_base x i).symm

  unfold partialDeriv

  have hFun :
      (
        fun t : ℝ =>
          f (coordinateLine x i t)
      )
        =
      (
        f ∘
          coordinateLine x i
      ) := by
    rfl

  rw [hFun]

  exact
    hComp.deriv

/--
For a spatially `C¹` field, the coordinate partial is the corresponding
Fréchet directional derivative everywhere.
-/
theorem SpatialC1.partialDeriv_eq_fderiv_axisDirection
    {dim : Depth}
    {f :
      PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC1 f)
    (x : PrimeTensor.Point ℝ dim)
    (i : PrimeTensor.Axis dim) :
    partialDeriv i f x
      =
    (fderiv ℝ f x) (axisDirection i) := by

  apply
    PrimeTensor.Bridge.Euclidean.partialDeriv_eq_fderiv_axisDirection

  exact
    (
      hf.differentiable_one
    ).differentiableAt

/--
The first partial field of a `C²` scalar field is globally represented by the
first Fréchet derivative applied to the corresponding coordinate direction.
-/
theorem SpatialC2.partialDeriv_fun_eq
    {dim : Depth}
    {f :
      PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC2 f)
    (j : PrimeTensor.Axis dim) :
    (
      fun y =>
        partialDeriv j f y
    )
      =
    (
      fun y =>
        (fderiv ℝ f y)
          (axisDirection j)
    ) := by

  funext y

  apply
    partialDeriv_eq_fderiv_axisDirection

  exact
    (
      hf.differentiable
        (by norm_num)
    ) y

/--
For a `C²` scalar field, the derivative map `x ↦ Df(x)` is `C¹`.
-/
theorem SpatialC2.fderiv_contDiff_one
    {dim : Depth}
    {f :
      PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC2 f) :
    ContDiff ℝ 1
      (fderiv ℝ f) := by

  exact
    hf.fderiv_right
      (by norm_num)

/--
For a `C²` scalar field, a fixed directional derivative
`x ↦ Df(x)eⱼ` is `C¹`.
-/
theorem SpatialC2.fderiv_axisDirection_contDiff_one
    {dim : Depth}
    {f :
      PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC2 f)
    (j : PrimeTensor.Axis dim) :
    ContDiff ℝ 1
      (
        fun y =>
          (fderiv ℝ f y)
            (axisDirection j)
      ) := by

  exact
    hf.fderiv_contDiff_one.clm_apply
      contDiff_const

/--
A nested coordinate partial of a `C²` scalar field is the second Fréchet
derivative evaluated on the two coordinate directions.
-/
theorem SpatialC2.secondPartial_eq_fderiv_fderiv
    {dim : Depth}
    {f :
      PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC2 f)
    (x : PrimeTensor.Point ℝ dim)
    (i j : PrimeTensor.Axis dim) :
    partialDeriv i
        (fun y =>
          partialDeriv j f y)
        x
      =
    (
      (fderiv ℝ
        (fderiv ℝ f)
        x)
        (axisDirection i)
    )
      (axisDirection j) := by

  rw [
    hf.partialDeriv_fun_eq j
  ]

  have hDirectionalC1 :=
    hf.fderiv_axisDirection_contDiff_one j

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.partialDeriv_eq_fderiv_axisDirection
      hDirectionalC1
      x i
  ]

  have hFderivDiff :
      DifferentiableAt ℝ
        (fderiv ℝ f)
        x := by

    exact
      (
        hf.fderiv_contDiff_one.differentiable_one
      ).differentiableAt

  have hConstDiff :
      DifferentiableAt ℝ
        (
          fun _ :
            PrimeTensor.Point ℝ dim =>
            axisDirection j
        )
        x :=
    differentiableAt_const
      (c := axisDirection j)

  rw [
    fderiv_clm_apply
      hFderivDiff
      hConstDiff
  ]

  simp

/--
Schwarz/Clairaut theorem for the project's concrete Euclidean partial
derivative: all mixed spatial partials of a `C²` scalar field commute.
-/
theorem SpatialC2.mixedPartial_comm
    {dim : Depth}
    {f :
      PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC2 f)
    (x : PrimeTensor.Point ℝ dim)
    (i j : PrimeTensor.Axis dim) :
    partialDeriv i
        (fun y =>
          partialDeriv j f y)
        x
      =
    partialDeriv j
        (fun y =>
          partialDeriv i f y)
        x := by

  rw [
    hf.secondPartial_eq_fderiv_fderiv
      x i j,
    hf.secondPartial_eq_fderiv_fderiv
      x j i
  ]

  have hSymm :
      IsSymmSndFDerivAt
        ℝ f x := by

    exact
      (
        hf.contDiffAt
      ).isSymmSndFDerivAt
        (by norm_num)

  exact
    hSymm.eq
      (axisDirection i)
      (axisDirection j)

/--
The same commutation theorem stated through the concrete `spatial` differential
interface used by the fluid equations.
-/
theorem SpatialC2.spatial_d_comm
    {dim : Depth}
    {f :
      PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC2 f)
    (x : PrimeTensor.Point ℝ dim)
    (i j : PrimeTensor.Axis dim) :
    (spatial dim).d i
        (
          (spatial dim).d j f
        )
        x
      =
    (spatial dim).d j
        (
          (spatial dim).d i f
        )
        x := by

  change
    partialDeriv i
        (fun y =>
          partialDeriv j f y)
        x
      =
    partialDeriv j
        (fun y =>
          partialDeriv i f y)
        x

  exact
    hf.mixedPartial_comm
      x i j

/--
Every spatial velocity component in a classical 3D solution has commuting
mixed partial derivatives.
-/
theorem ClassicalSolution3.velocity_spatial_d_comm
    (s : ClassicalSolution3)
    (t : ℝ)
    (x : Point3)
    (k i j :
      PrimeTensor.Axis Depth.three) :
    spatial3.d i
        (
          spatial3.d j
            (
              fun y =>
                (s.velocity t y).component k
            )
        )
        x
      =
    spatial3.d j
        (
          spatial3.d i
            (
              fun y =>
                (s.velocity t y).component k
            )
        )
        x := by

  exact
    (
      s.regularity.velocity_spatial
        t k
    ).spatial_d_comm
      x i j

end Euclidean
end Bridge
end PrimeTensor
