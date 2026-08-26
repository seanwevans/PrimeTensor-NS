import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Weak.Derivative
import PrimeTensor.Bridge.Euclidean.Partials.Third
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Transport of PrimeTensor spatial derivatives to the Euclidean Fourier carrier

The concrete fluid fields in PrimeTensor live on

    Point3 = Axis.three → ℝ

with the ordinary finite-product sup norm.  The Fourier / Sobolev solver lives
on

    H3FourierPoint3 = EuclideanSpace ℝ Axis.three.

These are the same finite coordinate tuples with equivalent but distinct
normed-space instance stacks.

The crucial implementation rule in this file is therefore:

* for calculus, use an explicitly constructed linear identity map
  `H3FourierPoint3 →L[ℝ] Point3`;
* for measure transport, reuse the already-green `WithLp.ofLp`
  volume-preserving map;
* connect the two only by pointwise / a.e. equality.

This avoids asking Lean to identify the `EuclideanSpace` and generic
`WithLp/PiLp` additive/module/measurable-space instances definitionally.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal SchwartzMap LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3SpatialTransport
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SpatialTransport :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Canonical finite-dimensional identity map -/

/--
Algebraic identity on the underlying three coordinates, regarded as a map
from the Euclidean carrier to the project's sup-norm carrier.
-/
def h3FourierToPoint3Linear :
    (WithLp 2 Point3) →ₗ[ℝ] Point3 where
  toFun := fun x i => x i
  map_add' := by
    intro x y
    ext i
    simp
  map_smul' := by
    intro c x
    ext i
    simp

/--
The same coordinate identity as a continuous linear map.  Continuity is
automatic because the Euclidean source is finite-dimensional.
-/
noncomputable def h3FourierToPoint3CLM :
    (WithLp 2 Point3) →L[ℝ] Point3 :=
  LinearMap.toContinuousLinearMap h3FourierToPoint3Linear

@[simp]
theorem h3FourierToPoint3CLM_apply
    (x : H3FourierPoint3)
    (i : PrimeTensor.Axis Depth.three) :
    h3FourierToPoint3CLM x i = x i := by
  rfl

/--
Pointwise, the explicit calculus map is the same raw coordinate map as
`WithLp.ofLp`.
-/
theorem h3FourierToPoint3CLM_eq_ofLp :
    (h3FourierToPoint3CLM :
      H3FourierPoint3 → Point3)
      =
    (WithLp.ofLp :
      H3FourierPoint3 → Point3) := by
  funext x
  ext i
  rfl

/-! ## Raw scalar transport -/

/-- A project scalar field viewed on the Euclidean carrier. -/
def h3TransportScalarField
    (f : ScalarField3) :
    H3FourierPoint3 → ℝ :=
  fun x => f (h3FourierToPoint3CLM x)

/--
The Euclidean coordinate direction corresponding to one intrinsic project
axis.
-/
def h3FourierAxisDirection
    (i : PrimeTensor.Axis Depth.three) :
    H3FourierPoint3 :=
  WithLp.toLp 2 (axisDirection i)

@[simp]
theorem h3FourierAxisDirection_apply
    (i j : PrimeTensor.Axis Depth.three) :
    h3FourierAxisDirection i j = axisDirection i j := by
  rfl

@[simp]
theorem h3FourierToPoint3CLM_axisDirection
    (i : PrimeTensor.Axis Depth.three) :
    h3FourierToPoint3CLM
        (h3FourierAxisDirection i)
      =
    axisDirection i := by
  ext j
  rfl

/-! ## A.e. compatibility with the existing L² transport -/

/--
The canonical `L²` transport has the raw representative expected from the
coordinate identity map.
-/
theorem h3ToFourierRealL2_coeFn_eq_transport
    {f : ScalarField3}
    (hf : MemLp f 2 volume) :
    (h3ToFourierRealL2 (hf.toLp f) :
      H3FourierPoint3 → ℝ)
      =ᵐ[volume]
    h3TransportScalarField f := by
  have hComp :
      (h3ToFourierRealL2 (hf.toLp f) :
        H3FourierPoint3 → ℝ)
        =ᵐ[volume]
      fun x =>
        (hf.toLp f)
          ((WithLp.ofLp :
            H3FourierPoint3 → Point3) x) := by
    unfold h3ToFourierRealL2
    exact
      MeasureTheory.Lp.coeFn_compMeasurePreserving
        (hf.toLp f)
        (PiLp.volume_preserving_ofLp
          (PrimeTensor.Axis Depth.three))

  have hPoint :
      (hf.toLp f : Point3 → ℝ)
        =ᵐ[(volume : Measure Point3)]
      f :=
    MeasureTheory.MemLp.coeFn_toLp hf

  have hPointComp :
      (fun x : H3FourierPoint3 =>
        (hf.toLp f)
          ((WithLp.ofLp :
            H3FourierPoint3 → Point3) x))
        =ᵐ[volume]
      fun x : H3FourierPoint3 =>
        f
          ((WithLp.ofLp :
            H3FourierPoint3 → Point3) x) := by
    exact
      (PiLp.volume_preserving_ofLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hPoint

  refine hComp.trans ?_
  filter_upwards [hPointComp] with x hx
  simpa [
    h3TransportScalarField,
    h3FourierToPoint3CLM_eq_ofLp
  ] using hx

/--
The transported raw scalar field is `L²` for the Euclidean carrier's actual
measurable-space instance.
-/
theorem h3TransportScalarField_memLp2
    {f : ScalarField3}
    (hf : MemLp f 2 volume) :
    MemLp (h3TransportScalarField f) 2 volume := by
  let F : H3FourierRealL2 :=
    h3ToFourierRealL2 (hf.toLp f)

  have hF : MemLp (F : H3FourierPoint3 → ℝ) 2 volume :=
    MeasureTheory.Lp.memLp F

  have hAE :
      (F : H3FourierPoint3 → ℝ)
        =ᵐ[volume]
      h3TransportScalarField f := by
    exact h3ToFourierRealL2_coeFn_eq_transport hf

  apply hF.congr_norm
  · exact
      (MeasureTheory.Lp.aestronglyMeasurable F).congr hAE
  · exact hAE.mono fun x hx => by rw [← hx]

/--
The raw-function transport represents exactly the same `L²` class as the
project's existing `h3ToFourierRealL2`.
-/
theorem h3TransportScalarField_toLp_eq
    {f : ScalarField3}
    (hf : MemLp f 2 volume) :
    (h3TransportScalarField_memLp2 hf).toLp
        (h3TransportScalarField f)
      =
    h3ToFourierRealL2 (hf.toLp f) := by
  apply MeasureTheory.Lp.ext
  exact
    (MeasureTheory.MemLp.coeFn_toLp
      (h3TransportScalarField_memLp2 hf)).trans
      (h3ToFourierRealL2_coeFn_eq_transport hf).symm

/--
After complexification, the raw transport is exactly the complex input used by
the project Fourier transform.
-/
theorem h3RealMemLpToComplexL2_transport_eq
    {f : ScalarField3}
    (hf : MemLp f 2 volume) :
    h3RealMemLpToComplexL2
        (h3TransportScalarField_memLp2 hf)
      =
    h3ComplexifyFourierL2
      (h3ToFourierRealL2 (hf.toLp f)) := by
  unfold h3RealMemLpToComplexL2 h3ComplexifyFourierL2
  rw [h3TransportScalarField_toLp_eq hf]

/-! ## Calculus transport -/

/--
A spatially `C¹` PrimeTensor scalar field has, after transport to the Euclidean
carrier, the expected genuine directional derivative in every coordinate
direction.
-/
theorem h3TransportScalarField_hasLineDerivAt
    {f : ScalarField3}
    (hf : SpatialC1 f)
    (i : PrimeTensor.Axis Depth.three)
    (x : WithLp 2 Point3) :
    HasLineDerivAt ℝ
      (fun y : WithLp 2 Point3 => f (h3FourierToPoint3CLM y))
      (spatial3.d i f (h3FourierToPoint3CLM x))
      x
      (WithLp.toLp 2 (axisDirection i)) := by
  have hDiff :
      DifferentiableAt ℝ f
        (h3FourierToPoint3CLM x) :=
    (hf.differentiable_one).differentiableAt

  have hComp :
      HasFDerivAt
        (fun y : WithLp 2 Point3 =>
          f (h3FourierToPoint3CLM y))
        ((fderiv ℝ f
            (h3FourierToPoint3CLM x)).comp
          h3FourierToPoint3CLM)
        x := by
    simpa [Function.comp_def] using
      hDiff.hasFDerivAt.comp
        x
        h3FourierToPoint3CLM.hasFDerivAt

  have hLine :=
    hComp.hasLineDerivAt
      (WithLp.toLp 2 (axisDirection i))

  have hValue :
      ((fderiv ℝ f
          (h3FourierToPoint3CLM x)).comp
        h3FourierToPoint3CLM)
        (WithLp.toLp 2 (axisDirection i))
        =
      spatial3.d i f
        (h3FourierToPoint3CLM x) := by
    rw [ContinuousLinearMap.comp_apply]
    change
      (fderiv ℝ f
        (h3FourierToPoint3CLM x))
        (axisDirection i)
        =
      spatial3.d i f
        (h3FourierToPoint3CLM x)
    exact
      (PrimeTensor.Bridge.Euclidean.SpatialC1.partialDeriv_eq_fderiv_axisDirection
        hf
        (h3FourierToPoint3CLM x)
        i).symm

  rw [← hValue]
  exact hLine

/-! ## Weak derivative after transport -/

/--
An `L²` PrimeTensor coordinate derivative of a spatially `C¹` scalar field is
the weak derivative of the transported `L²` field on the Euclidean carrier.
-/
theorem h3TransportSpatialDerivative_weak
    {f : ScalarField3}
    (hfC1 : SpatialC1 f)
    (i : PrimeTensor.Axis Depth.three)
    (hf : MemLp f 2 volume)
    (hdi : MemLp (spatial3.d i f) 2 volume) :
    H3WeakLineDerivative
      (h3FourierAxisDirection i)
      (h3RealMemLpToComplexL2
        (h3TransportScalarField_memLp2 hf))
      (h3RealMemLpToComplexL2
        (h3TransportScalarField_memLp2 hdi)) := by
  apply h3WeakLineDerivative_of_classical
  intro x
  change
    HasLineDerivAt ℝ
      (fun y : WithLp 2 Point3 =>
        f (h3FourierToPoint3CLM y))
      (spatial3.d i f
        (h3FourierToPoint3CLM (x : WithLp 2 Point3)))
      (x : WithLp 2 Point3)
      (WithLp.toLp 2 (axisDirection i))
  exact
    h3TransportScalarField_hasLineDerivAt
      hfC1 i
      (x : WithLp 2 Point3)

/--
The same weak-derivative statement, rewritten using the project's canonical
real `L²` transport.
-/
theorem h3ToFourierRealL2_spatialDerivative_weak
    {f : ScalarField3}
    (hfC1 : SpatialC1 f)
    (i : PrimeTensor.Axis Depth.three)
    (hf : MemLp f 2 volume)
    (hdi : MemLp (spatial3.d i f) 2 volume) :
    H3WeakLineDerivative
      (h3FourierAxisDirection i)
      (h3ComplexifyFourierL2
        (h3ToFourierRealL2 (hf.toLp f)))
      (h3ComplexifyFourierL2
        (h3ToFourierRealL2
          (hdi.toLp (spatial3.d i f)))) := by
  rw [
    ← h3RealMemLpToComplexL2_transport_eq hf,
    ← h3RealMemLpToComplexL2_transport_eq hdi
  ]
  exact
    h3TransportSpatialDerivative_weak
      hfC1 i hf hdi

end

end Euclidean
end Bridge
end PrimeTensor
