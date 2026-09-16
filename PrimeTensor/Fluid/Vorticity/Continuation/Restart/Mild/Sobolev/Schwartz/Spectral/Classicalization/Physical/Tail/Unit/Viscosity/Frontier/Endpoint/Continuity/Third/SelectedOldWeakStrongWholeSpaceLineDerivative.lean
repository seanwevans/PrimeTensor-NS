import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongAlternateSelectedTransportAutomaticIntegrability
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Whole-space line derivatives have zero integral

The remaining alternate weak--strong transport seam is a boundary-at-infinity
statement.  Rather than introducing an explicit cutoff/Fubini construction,
we reuse Mathlib's whole-space line-derivative integration-by-parts theorem.

If `F` and its line derivative `G` are both integrable on a finite-dimensional
real vector space, test the integration-by-parts identity against the constant
function `1`.  Its line derivative is zero, so

    0 = - ∫ G,

hence

    ∫ G = 0.

The second theorem specializes this to PrimeTensor scalar fields transported
from `Point3` to the Euclidean H³ carrier.  It is the exact calculus primitive
needed to annihilate each coordinate derivative in

    div (S D_j²).
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWholeSpaceLineDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- An integrable whole-space line derivative of an integrable real scalar
field has zero integral.

This is integration by parts against the constant test function `1`. -/
theorem integral_lineDerivative_eq_zero_of_integrable
    {F G : H3FourierPoint3 → ℝ}
    (v : H3FourierPoint3)
    (hF : Integrable F (volume : Measure H3FourierPoint3))
    (hG : Integrable G (volume : Measure H3FourierPoint3))
    (hDeriv :
      ∀ x : H3FourierPoint3,
        HasLineDerivAt ℝ F (G x) x v) :
    (∫ x : H3FourierPoint3, G x ∂volume) = 0 := by
  let one : H3FourierPoint3 → ℝ :=
    fun _ => 1

  let zero : H3FourierPoint3 → ℝ :=
    fun _ => 0

  have hGOne :
      Integrable
        (fun x : H3FourierPoint3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (G x)
            (one x))
        (volume : Measure H3FourierPoint3) := by
    simpa only [one, ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_one]
      using hG

  have hFZero :
      Integrable
        (fun x : H3FourierPoint3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (F x)
            (zero x))
        (volume : Measure H3FourierPoint3) := by
    have hz :
        Integrable
          (fun _ : H3FourierPoint3 => (0 : ℝ))
          (volume : Measure H3FourierPoint3) :=
      integrable_zero
        H3FourierPoint3
        ℝ
        (volume : Measure H3FourierPoint3)

    simpa only [
      zero,
      ContinuousLinearMap.lsmul_apply,
      smul_eq_mul,
      mul_zero
    ] using hz

  have hFOne :
      Integrable
        (fun x : H3FourierPoint3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (F x)
            (one x))
        (volume : Measure H3FourierPoint3) := by
    simpa only [one, ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_one]
      using hF

  have hOneDeriv :
      ∀ x : H3FourierPoint3,
        HasLineDerivAt ℝ one (zero x) x v := by
    intro x

    unfold HasLineDerivAt

    simpa only [one, zero] using
      (hasDerivAt_const (0 : ℝ) (1 : ℝ))

  have hIBP :=
    integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (B := ContinuousLinearMap.lsmul ℝ ℝ)
      hGOne
      hFZero
      hFOne
      (fun x _ => hDeriv x)
      (fun x _ => hOneDeriv x)

  have hZero :
      (0 : ℝ)
        =
      -
      (∫ x : H3FourierPoint3, G x ∂volume) := by
    simpa only [
      one,
      zero,
      ContinuousLinearMap.lsmul_apply,
      smul_eq_mul,
      mul_zero,
      mul_one,
      integral_zero
    ] using hIBP

  linarith

/-- Transported form of the preceding theorem.

If a PrimeTensor scalar field `f` is spatially `C¹`, and both `f` and one
coordinate derivative are integrable after transport to the Euclidean H³
carrier, then the transported coordinate derivative has zero whole-space
integral. -/
theorem integral_h3TransportScalarField_spatial_d_eq_zero
    {f : ScalarField3}
    (hfC1 : SpatialC1 f)
    (i : PrimeTensor.Axis Depth.three)
    (hf :
      Integrable
        (h3TransportScalarField f)
        (volume : Measure H3FourierPoint3))
    (hdi :
      Integrable
        (h3TransportScalarField (spatial3.d i f))
        (volume : Measure H3FourierPoint3)) :
    (∫ x : H3FourierPoint3,
      h3TransportScalarField (spatial3.d i f) x
      ∂volume)
      =
    0 := by
  let F : H3FourierPoint3 → ℝ :=
    h3TransportScalarField f

  let G : H3FourierPoint3 → ℝ :=
    h3TransportScalarField (spatial3.d i f)

  let v : H3FourierPoint3 :=
    h3FourierAxisDirection i

  have hDeriv :
      ∀ x : H3FourierPoint3,
        HasLineDerivAt ℝ F (G x) x v := by
    intro x

    dsimp only [F, G, v, h3TransportScalarField]

    exact
      h3TransportScalarField_hasLineDerivAt
        hfC1 i x

  have hZero :=
    integral_lineDerivative_eq_zero_of_integrable
      v
      (by simpa only [F] using hf)
      (by simpa only [G] using hdi)
      hDeriv

  simpa only [G] using hZero

end

end Euclidean
end Bridge
end PrimeTensor
