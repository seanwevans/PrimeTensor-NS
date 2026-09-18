import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.IntegrationByParts.Closure
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Data.Real.ConjExponents

/-!
# Whole-space scalar transport flux coordinates

For one scalar coefficient `v`, one transported scalar `f`, and one coordinate
axis `i`, the transport flux coordinate is

    v f².

The H³ application naturally supplies

* `v ∈ L² ∩ L⁴`,
* `f ∈ L² ∩ L⁴`,
* `∂ᵢf ∈ L²`,
* a pointwise bound on `∂ᵢv`.

These are enough to prove both

    v f² ∈ L¹,
    ∂ᵢ(v f²) ∈ L¹,

and hence, by whole-space line-derivative integration by parts,

    ∫ ∂ᵢ(v f²) = 0.

Unlike the older bounded-coefficient helper used in the restart branch, this
form does not require a pointwise `L∞` bound on `v` itself.  It is therefore
matched directly to the canonical H³/Landau data.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3TransportFluxCoordinate
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TransportFluxCoordinate :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

local instance holderTripleFourFourTwoH3TransportFluxCoordinate :
    ENNReal.HolderTriple
      (4 : ENNReal)
      (4 : ENNReal)
      (2 : ENNReal) := by
  have hReal :
      Real.HolderTriple
        4 4 2 := by
    rw [Real.holderTriple_iff]
    norm_num

  simpa using
    hReal.ennrealOfReal

local instance holderTripleTwoTwoOneH3TransportFluxCoordinate :
    ENNReal.HolderTriple
      (2 : ENNReal)
      (2 : ENNReal)
      (1 : ENNReal) := by
  infer_instance

/-- A coordinate derivative of a spatially `C¹` field is continuous. -/
private theorem spatialC1_spatial_d_continuous_transportFluxCoordinate
    {f : ScalarField3}
    (hf : SpatialC1 f)
    (i : PrimeTensor.Axis Depth.three) :
    Continuous (spatial3.d i f) := by
  have hfun :
      (fun x : Point3 => partialDeriv i f x)
        =
      (fun x : Point3 => (fderiv ℝ f x) (axisDirection i)) := by
    funext x
    exact
      PrimeTensor.Bridge.Euclidean.SpatialC1.partialDeriv_eq_fderiv_axisDirection
        hf x i

  change Continuous (fun x : Point3 => partialDeriv i f x)
  rw [hfun]

  have hfd : ContDiff ℝ 0 (fderiv ℝ f) := by
    unfold SpatialC1 at hf
    exact hf.fderiv_right (by norm_num)

  exact
    (hfd.clm_apply contDiff_const).continuous

/-- An integrable coordinate derivative of an integrable spatially `C¹`
physical scalar field has zero whole-space integral. -/
theorem integral_spatial3_d_eq_zero_of_integrable_transport
    {q : ScalarField3}
    (hqC1 : SpatialC1 q)
    (i : PrimeTensor.Axis Depth.three)
    (hq :
      Integrable q
        (volume : Measure Point3))
    (hdi :
      Integrable (spatial3.d i q)
        (volume : Measure Point3)) :
    (∫ x : Point3,
      spatial3.d i q x
      ∂volume)
      =
    0 := by
  let one : Point3 → ℝ :=
    fun _ => 1

  let zero : Point3 → ℝ :=
    fun _ => 0

  let dq : Point3 → ℝ :=
    spatial3.d i q

  let direction : Point3 :=
    axisDirection i

  have hZeroQ :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (zero x)
            (q x))
        (volume : Measure Point3) := by
    have h0q :
        Integrable
          (fun x : Point3 =>
            (0 : ℝ) * q x)
          (volume : Measure Point3) := by
      simpa only [zero_mul] using
        hq.const_mul (0 : ℝ)

    simpa only [
      zero,
      ContinuousLinearMap.lsmul_apply,
      smul_eq_mul
    ] using h0q

  have hOneDQ :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (one x)
            (dq x))
        (volume : Measure Point3) := by
    simpa only [
      one,
      dq,
      ContinuousLinearMap.lsmul_apply,
      smul_eq_mul,
      one_mul
    ] using hdi

  have hOneQ :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (one x)
            (q x))
        (volume : Measure Point3) := by
    simpa only [
      one,
      ContinuousLinearMap.lsmul_apply,
      smul_eq_mul,
      one_mul
    ] using hq

  have hOneLine
      (x : Point3) :
      HasLineDerivAt ℝ
        one
        (zero x)
        x
        direction := by
    unfold HasLineDerivAt

    simpa only [one, zero] using
      (hasDerivAt_const (0 : ℝ) (1 : ℝ))

  have hqLine
      (x : Point3) :
      HasLineDerivAt ℝ
        q
        (dq x)
        x
        direction := by
    have hDiff :
        DifferentiableAt ℝ q x :=
      hqC1.differentiable_one.differentiableAt

    have hLine :=
      hDiff.hasFDerivAt.hasLineDerivAt direction

    have hValue :
        (fderiv ℝ q x) direction
          =
        dq x := by
      dsimp only [direction, dq]

      exact
        (SpatialC1.partialDeriv_eq_fderiv_axisDirection
          hqC1 x i).symm

    simpa only [hValue] using hLine

  have hIBP :
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (one x)
          (dq x)
        ∂volume)
        =
      -
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (zero x)
          (q x)
        ∂volume := by
    exact
      integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
        (B := ContinuousLinearMap.lsmul ℝ ℝ)
        hZeroQ
        hOneDQ
        hOneQ
        (fun x _ => hOneLine x)
        (fun x _ => hqLine x)

  simpa only [
    one,
    zero,
    dq,
    ContinuousLinearMap.lsmul_apply,
    smul_eq_mul,
    one_mul,
    zero_mul,
    integral_zero,
    neg_zero
  ] using hIBP

/-- Hölder in the `2,4,4` form used by the transport-flux derivative. -/
theorem integrable_mul_mul_of_memLp_two_four_four_transport
    {f g q : ScalarField3}
    (hf :
      MemLp f
        (ENNReal.ofReal 2)
        volume)
    (hg :
      MemLp g
        (ENNReal.ofReal 4)
        volume)
    (hq :
      MemLp q
        (ENNReal.ofReal 4)
        volume) :
    Integrable
      (fun x : Point3 =>
        f x * (g x * q x))
      volume := by
  have hf2 :
      MemLp f (2 : ENNReal) volume := by
    simpa using hf

  have hg4 :
      MemLp g (4 : ENNReal) volume := by
    simpa using hg

  have hq4 :
      MemLp q (4 : ENNReal) volume := by
    simpa using hq

  have hgq2 :
      MemLp
        (fun x : Point3 =>
          g x * q x)
        (2 : ENNReal)
        volume := by
    exact
      hq4.mul' hg4

  have hfgq1 :
      MemLp
        (fun x : Point3 =>
          f x * (g x * q x))
        (1 : ENNReal)
        volume := by
    exact
      hgq2.mul' hf2

  exact
    memLp_one_iff_integrable.mp
      hfgq1

/-- `v ∈ L²` and `f ∈ L⁴` imply `v f² ∈ L¹`. -/
theorem scalarFluxCoordinate_integrable_of_memLp_two_four
    {v f : ScalarField3}
    (hv2 :
      MemLp v
        (ENNReal.ofReal 2)
        volume)
    (hf4 :
      MemLp f
        (ENNReal.ofReal 4)
        volume) :
    Integrable
      (fun x : Point3 =>
        v x * (f x * f x))
      volume := by
  have hv2' :
      MemLp v (2 : ENNReal) volume := by
    simpa using hv2

  have hf4' :
      MemLp f (4 : ENNReal) volume := by
    simpa using hf4

  have hff2 :
      MemLp
        (fun x : Point3 =>
          f x * f x)
        (2 : ENNReal)
        volume := by
    exact
      hf4'.mul' hf4'

  have hFlux1 :
      MemLp
        (fun x : Point3 =>
          v x * (f x * f x))
        (1 : ENNReal)
        volume := by
    exact
      hff2.mul' hv2'

  exact
    memLp_one_iff_integrable.mp
      hFlux1

/-- The matching coordinate derivative of `v f²` is integrable under the
canonical H³ exponent pattern. -/
theorem scalarFluxCoordinate_spatial_d_integrable_of_memLp_four
    {v f : ScalarField3}
    (hv : SpatialC1 v)
    (hf : SpatialC1 f)
    (i : PrimeTensor.Axis Depth.three)
    (B : ℝ)
    (hdvBound :
      ∀ x : Point3,
        ‖spatial3.d i v x‖ ≤ B)
    (hf2 :
      MemLp f
        (ENNReal.ofReal 2)
        volume)
    (hv4 :
      MemLp v
        (ENNReal.ofReal 4)
        volume)
    (hf4 :
      MemLp f
        (ENNReal.ofReal 4)
        volume)
    (hdf2 :
      MemLp (spatial3.d i f)
        (ENNReal.ofReal 2)
        volume) :
    Integrable
      (spatial3.d
        i
        (fun x : Point3 =>
          v x * (f x * f x)))
      volume := by
  have hf2' :
      MemLp f (2 : ENNReal) volume := by
    simpa using hf2

  have hff :
      Integrable
        (fun x : Point3 =>
          f x * f x)
        volume :=
    hf2'.integrable_mul hf2'

  have hdvContinuous :
      Continuous
        (spatial3.d i v) :=
    spatialC1_spatial_d_continuous_transportFluxCoordinate
      hv i

  have hLeft :
      Integrable
        (fun x : Point3 =>
          spatial3.d i v x * (f x * f x))
        volume :=
    hff.bdd_mul
      hdvContinuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hdvBound)

  have hRightOne :
      Integrable
        (fun x : Point3 =>
          v x *
            (spatial3.d i f x * f x))
        volume := by
    have h :=
      integrable_mul_mul_of_memLp_two_four_four_transport
        hdf2
        hv4
        hf4

    simpa [mul_comm, mul_left_comm, mul_assoc] using
      h

  have hRightTwo :
      Integrable
        (fun x : Point3 =>
          v x *
            (f x * spatial3.d i f x))
        volume := by
    have h :=
      integrable_mul_mul_of_memLp_two_four_four_transport
        hdf2
        hv4
        hf4

    simpa [mul_comm, mul_left_comm, mul_assoc] using
      h

  have hRight :
      Integrable
        (fun x : Point3 =>
          v x *
            (
              spatial3.d i f x * f x
                +
              f x * spatial3.d i f x
            ))
        volume := by
    have hSum :
        Integrable
          (fun x : Point3 =>
            v x * (spatial3.d i f x * f x)
              +
            v x * (f x * spatial3.d i f x))
          volume :=
      hRightOne.add hRightTwo

    simpa [mul_add] using
      hSum

  have hRhs :
      Integrable
        (fun x : Point3 =>
          spatial3.d i v x * (f x * f x)
            +
          v x *
            (
              spatial3.d i f x * f x
                +
              f x * spatial3.d i f x
            ))
        volume :=
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
          (
            spatial3.d i f x * f x
              +
            f x * spatial3.d i f x
          ) := by
    funext x

    rw [
      SpatialC1.spatial3_d_mul
        hv (hf.mul hf) x i,
      SpatialC1.spatial3_d_mul
        hf hf x i
    ]

  rw [hPointwise]

  exact hRhs

/-- Canonical H³ exponent data gives zero integral for one coordinate
derivative of `v f²`. -/
theorem integral_scalarFluxCoordinate_spatial_d_eq_zero_of_memLp_four
    {v f : ScalarField3}
    (hv : SpatialC1 v)
    (hf : SpatialC1 f)
    (i : PrimeTensor.Axis Depth.three)
    (B : ℝ)
    (hdvBound :
      ∀ x : Point3,
        ‖spatial3.d i v x‖ ≤ B)
    (hv2 :
      MemLp v
        (ENNReal.ofReal 2)
        volume)
    (hf2 :
      MemLp f
        (ENNReal.ofReal 2)
        volume)
    (hv4 :
      MemLp v
        (ENNReal.ofReal 4)
        volume)
    (hf4 :
      MemLp f
        (ENNReal.ofReal 4)
        volume)
    (hdf2 :
      MemLp (spatial3.d i f)
        (ENNReal.ofReal 2)
        volume) :
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
        volume :=
    scalarFluxCoordinate_integrable_of_memLp_two_four
      hv2
      hf4

  have hFluxDerivative :
      Integrable
        (spatial3.d
          i
          (fun x : Point3 =>
            v x * (f x * f x)))
        volume :=
    scalarFluxCoordinate_spatial_d_integrable_of_memLp_four
      hv hf i B hdvBound hf2 hv4 hf4 hdf2

  exact
    integral_spatial3_d_eq_zero_of_integrable_transport
      hFluxC1
      i
      hFlux
      hFluxDerivative

end

end Euclidean
end Bridge
end PrimeTensor
