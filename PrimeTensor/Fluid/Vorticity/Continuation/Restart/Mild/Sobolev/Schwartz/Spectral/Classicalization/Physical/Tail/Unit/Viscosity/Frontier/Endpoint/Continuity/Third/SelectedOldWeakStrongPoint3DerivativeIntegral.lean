import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWholeSpaceLineDerivative
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Whole-space Point3 coordinate derivatives integrate to zero

`SelectedOldWeakStrongWholeSpaceLineDerivative` proved the Euclidean-carrier
version needed by the Fourier transport layer.  The selected transport flux
itself lives directly on PrimeTensor's physical carrier

    Point3 = Axis.three → ℝ.

The repository already uses Mathlib's multivariate line-derivative
integration-by-parts theorem directly on this carrier.  Testing against the
constant function `1` gives the exact physical-space primitive we need:

    q, ∂ᵢq ∈ L¹
    and q spatially C¹
        ⟹
    ∫ ∂ᵢq = 0.

No cutoff, Fubini decomposition, Fourier transform, or decay hypothesis is
introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongPoint3DerivativeIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongPoint3DerivativeIntegral :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- An integrable coordinate derivative of an integrable spatially `C¹`
physical scalar field has zero whole-space integral. -/
theorem integral_spatial3_d_eq_zero_of_integrable
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

  let v : Point3 :=
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
        v := by
    unfold HasLineDerivAt

    simpa only [one, zero] using
      (hasDerivAt_const (0 : ℝ) (1 : ℝ))

  have hqLine
      (x : Point3) :
      HasLineDerivAt ℝ
        q
        (dq x)
        x
        v := by
    have hDiff :
        DifferentiableAt ℝ q x :=
      (hqC1.differentiable_one).differentiableAt

    have hLine :=
      hDiff.hasFDerivAt.hasLineDerivAt v

    have hValue :
        (fderiv ℝ q x) v
          =
        dq x := by
      dsimp only [v, dq]

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

end

end Euclidean
end Bridge
end PrimeTensor
