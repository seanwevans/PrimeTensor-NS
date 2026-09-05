import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Selected.Second.Coordinate.Duhamel.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Arbitrary-parameter selected mixed second-coordinate derivatives

The endpoint branch now proves the mixed second-coordinate Duhamel derivative
at parameter zero and continuity of the resulting mixed derivative field in
space.  This file transports the derivative identity to an arbitrary parameter
on an affine coordinate line.

Consequently, for every pair of coordinate directions `j,k`, the selected
first-coordinate Duhamel derivative in direction `j` is an ordinary `C¹`
function along the `k` coordinate line.  This is the exact coordinatewise
second-order interface needed by the finite-dimensional Hessian assembly.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Filter
open scoped Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterSelectedSecondCoordinateAt
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected mixed second-coordinate derivative identity at an arbitrary
parameter value of the affine `k`-coordinate line. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel_selectedRestart_hasDerivAt_secondCoordinate_at
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i j k : Fin 3)
    (x : H3FourierPoint3)
    (r : ℝ) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    HasDerivAt
      (fun q : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
          ν t W W i j
          (x + q • h3FourierAxisDirection (h3AxisOfFin3 k)))
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
        ν t W W i j k
        (x + r • h3FourierAxisDirection (h3AxisOfFin3 k)))
      r := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 k)

  have h0 :
      HasDerivAt
        (fun q : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
            ν t W W i j ((x + r • e) + q • e))
        (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
          ν t W W i j k (x + r • e))
        0 := by
    simpa [e] using
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel_selectedRestart_hasDerivAt_secondCoordinate
        hν U₀ hA hU₀ ht htR i j k (x + r • e))

  have hShift :
      HasDerivAt (fun q : ℝ => q - r) 1 r := by
    simpa using (hasDerivAt_id r).sub_const r

  have hComp := h0.scomp_of_eq r hShift (by simp)

  have hPoint (q : ℝ) :
      (x + r • e) + (q - r) • e = x + q • e := by
    rw [sub_smul]
    abel

  have hFunEq :
      (fun q : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
          ν t W W i j (x + q • e))
        =ᶠ[𝓝 r]
      ((fun q : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
            ν t W W i j ((x + r • e) + q • e)) ∘
        fun q : ℝ => q - r) := by
    filter_upwards with q
    simp only [Function.comp_apply]
    rw [hPoint q]

  have hTransport := hComp.congr_of_eventuallyEq hFunEq

  have hDerivEq :
      (1 : ℝ) •
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
            ν t W W i j k (x + r • e)
        =
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
        ν t W W i j k (x + r • e) :=
    one_smul ℝ _

  have hFinal := hTransport.congr_deriv hDerivEq
  simpa only [e] using hFinal

/-- Equality form of the arbitrary-parameter selected mixed derivative. -/
theorem deriv_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel_selectedRestart_secondCoordinate_at
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i j k : Fin 3)
    (x : H3FourierPoint3)
    (r : ℝ) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    deriv
      (fun q : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
          ν t W W i j
          (x + q • h3FourierAxisDirection (h3AxisOfFin3 k)))
      r
      =
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
      ν t W W i j k
      (x + r • h3FourierAxisDirection (h3AxisOfFin3 k)) := by
  dsimp only
  exact
    (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel_selectedRestart_hasDerivAt_secondCoordinate_at
      hν U₀ hA hU₀ ht htR i j k x r).deriv

/-- For every pair `j,k`, the selected first-coordinate Duhamel derivative in
direction `j` is `C¹` along the affine `k`-coordinate line. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel_selectedRestart_secondCoordinate_contDiff_one
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i j k : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContDiff ℝ 1
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
          ν t W W i j
          (x + r • h3FourierAxisDirection (h3AxisOfFin3 k))) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 k)

  rw [contDiff_one_iff_deriv]
  constructor
  · intro r
    exact
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel_selectedRestart_hasDerivAt_secondCoordinate_at
        hν U₀ hA hU₀ ht htR i j k x r).differentiableAt
  · have hDerivEq :
        deriv
          (fun r : ℝ =>
            h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
              ν t W W i j (x + r • e))
          =
        fun r : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
            ν t W W i j k (x + r • e) := by
      funext r
      exact
        deriv_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel_selectedRestart_secondCoordinate_at
          hν U₀ hA hU₀ ht htR i j k x r

    rw [hDerivEq]

    exact
      (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel_selectedRestart_continuous
        hν U₀ hA hU₀ ht htR i j k).comp (by fun_prop)

end
end Euclidean
end Bridge
end PrimeTensor
