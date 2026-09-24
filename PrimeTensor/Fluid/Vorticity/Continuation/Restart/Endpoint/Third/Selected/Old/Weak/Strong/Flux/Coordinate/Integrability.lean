import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Point3.Derivative.Integral

/-!
# Integrable scalar-flux coordinates from bounded velocity and H¹ scalar data

The selected weak--strong boundary term has the form

    div (v f²)
      =
    Σᵢ ∂ᵢ (vᵢ f²).

`SelectedOldWeakStrongPoint3DerivativeIntegral` reduces each coordinate
integral to two ordinary `L¹` facts:

    vᵢ f² ∈ L¹,
    ∂ᵢ(vᵢ f²) ∈ L¹.

This file proves those facts abstractly from the exact regularity available in
the weak--strong application:

* `vᵢ` and `∂ᵢvᵢ` are bounded;
* `f` and `∂ᵢf` lie in `L²`;
* both fields are spatially `C¹`.

The proof is just Hölder plus the product rule.  Consequently every coordinate
flux derivative has zero whole-space integral.

This isolates the final selected specialization from the measure-theoretic
details: it will only need to supply the selected velocity envelopes and the
`L²` first derivatives of the selected-minus-old difference.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongFluxCoordinateIntegrability
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongFluxCoordinateIntegrability :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A bounded continuous scalar coefficient times the square of an `L²`
function is integrable. -/
theorem scalarFluxCoordinate_integrable_of_bounded_memLp_two
    {v f : ScalarField3}
    (hv : SpatialC1 v)
    (M : ℝ)
    (hvBound :
      ∀ x : Point3,
        ‖v x‖ ≤ M)
    (hf2 :
      MemLp f 2
        (volume : Measure Point3)) :
    Integrable
      (fun x : Point3 =>
        v x * (f x * f x))
      (volume : Measure Point3) := by
  have hff :
      Integrable
        (fun x : Point3 =>
          f x * f x)
        (volume : Measure Point3) :=
    hf2.integrable_mul hf2

  exact
    hff.bdd_mul
      hv.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hvBound)

/-- Under bounded zeroth/first coefficient envelopes and `H¹`-level `L²`
control of `f`, the matching coordinate derivative of `v f²` is integrable. -/
theorem scalarFluxCoordinate_spatial_d_integrable_of_bounded_memLp_two
    {v f : ScalarField3}
    (hv : SpatialC1 v)
    (hf : SpatialC1 f)
    (i : PrimeTensor.Axis Depth.three)
    (M B : ℝ)
    (hvBound :
      ∀ x : Point3,
        ‖v x‖ ≤ M)
    (hdvBound :
      ∀ x : Point3,
        ‖spatial3.d i v x‖ ≤ B)
    (hf2 :
      MemLp f 2
        (volume : Measure Point3))
    (hdf2 :
      MemLp (spatial3.d i f) 2
        (volume : Measure Point3)) :
    Integrable
      (spatial3.d
        i
        (fun x : Point3 =>
          v x * (f x * f x)))
      (volume : Measure Point3) := by
  have hff :
      Integrable
        (fun x : Point3 =>
          f x * f x)
        (volume : Measure Point3) :=
    hf2.integrable_mul hf2

  have hdf_f :
      Integrable
        (fun x : Point3 =>
          spatial3.d i f x * f x)
        (volume : Measure Point3) :=
    hdf2.integrable_mul hf2

  have hf_df :
      Integrable
        (fun x : Point3 =>
          f x * spatial3.d i f x)
        (volume : Measure Point3) :=
    hf2.integrable_mul hdf2

  have hdvContinuous :
      Continuous
        (spatial3.d i v) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hv i

  have hLeft :
      Integrable
        (fun x : Point3 =>
          spatial3.d i v x * (f x * f x))
        (volume : Measure Point3) :=
    hff.bdd_mul
      hdvContinuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hdvBound)

  have hCross :
      Integrable
        (fun x : Point3 =>
          spatial3.d i f x * f x
            +
          f x * spatial3.d i f x)
        (volume : Measure Point3) :=
    hdf_f.add hf_df

  have hRight :
      Integrable
        (fun x : Point3 =>
          v x *
            (spatial3.d i f x * f x
              +
             f x * spatial3.d i f x))
        (volume : Measure Point3) :=
    hCross.bdd_mul
      hv.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hvBound)

  have hRhs :
      Integrable
        (fun x : Point3 =>
          spatial3.d i v x * (f x * f x)
            +
          v x *
            (spatial3.d i f x * f x
              +
             f x * spatial3.d i f x))
        (volume : Measure Point3) :=
    hLeft.add hRight

  have hPointwise :
      spatial3.d
          i
          (fun x : Point3 =>
            v x * (f x * f x))
        =
      fun x : Point3 =>
        spatial3.d i v x * (f x * f x)
          +
        v x *
          (spatial3.d i f x * f x
            +
           f x * spatial3.d i f x) := by
    funext x

    rw [
      SpatialC1.spatial3_d_mul
        hv (hf.mul hf) x i,
      SpatialC1.spatial3_d_mul
        hf hf x i
    ]

  rw [hPointwise]

  exact hRhs

/-- A bounded `C¹` coefficient and `H¹` scalar field have zero whole-space
integral for every matching coordinate derivative of the scalar flux
`v f²`. -/
theorem integral_scalarFluxCoordinate_spatial_d_eq_zero_of_bounded_memLp_two
    {v f : ScalarField3}
    (hv : SpatialC1 v)
    (hf : SpatialC1 f)
    (i : PrimeTensor.Axis Depth.three)
    (M B : ℝ)
    (hvBound :
      ∀ x : Point3,
        ‖v x‖ ≤ M)
    (hdvBound :
      ∀ x : Point3,
        ‖spatial3.d i v x‖ ≤ B)
    (hf2 :
      MemLp f 2
        (volume : Measure Point3))
    (hdf2 :
      MemLp (spatial3.d i f) 2
        (volume : Measure Point3)) :
    (∫ x : Point3,
      spatial3.d
        i
        (fun y : Point3 =>
          v y * (f y * f y))
        x
      ∂volume)
      =
    0 := by
  have hFluxC1 :
      SpatialC1
        (fun x : Point3 =>
          v x * (f x * f x)) :=
    hv.mul (hf.mul hf)

  have hFlux :
      Integrable
        (fun x : Point3 =>
          v x * (f x * f x))
        (volume : Measure Point3) :=
    scalarFluxCoordinate_integrable_of_bounded_memLp_two
      hv M hvBound hf2

  have hFluxDerivative :
      Integrable
        (spatial3.d
          i
          (fun x : Point3 =>
            v x * (f x * f x)))
        (volume : Measure Point3) :=
    scalarFluxCoordinate_spatial_d_integrable_of_bounded_memLp_two
      hv hf i M B hvBound hdvBound hf2 hdf2

  exact
    integral_spatial3_d_eq_zero_of_integrable
      hFluxC1 i hFlux hFluxDerivative

end

end Euclidean
end Bridge
end PrimeTensor
