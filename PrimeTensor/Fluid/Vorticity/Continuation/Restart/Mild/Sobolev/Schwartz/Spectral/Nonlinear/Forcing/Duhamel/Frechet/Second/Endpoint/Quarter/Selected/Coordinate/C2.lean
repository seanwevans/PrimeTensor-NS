import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Selected.Second.Coordinate.At
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Coordinate.C1
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Selected coordinate C² regularity of the nonlinear Duhamel reconstruction

Every selected first-coordinate derivative is now `C¹` along every coordinate
line.  Combining that with the existing first-coordinate derivative identity
for the Duhamel reconstruction upgrades each affine coordinate line of the
selected nonlinear Duhamel term from `C¹` to `C²`.

This is the coordinate-level second-order package consumed by the next
finite-dimensional Hessian/Fréchet assembly.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Filter
open scoped Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterSelectedCoordinateC2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Along the selected restart path, every affine coordinate line of the
nonlinear Duhamel reconstruction is `C²`. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selectedRestart_coordinate_contDiff_two
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContDiff ℝ 2
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t W W i
          (x + r • h3FourierAxisDirection (h3AxisOfFin3 j))) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 j)

  let f : ℝ → ℂ :=
    fun r =>
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t W W i (x + r • e)

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hWbound : ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have htwoA : 0 ≤ 2 * A := by
    positivity

  have hDiff : Differentiable ℝ f := by
    intro r
    dsimp only [f]
    exact
      (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_hasDerivAt_coordinate_at
        hν ht.le htwoA htwoA W W hWcont hWcont
        (fun s _ => hWbound s)
        (fun s _ => hWbound s)
        i j x r).differentiableAt

  have hDerivEq :
      deriv f
        =
      fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
          ν t W W i j (x + r • e) := by
    funext r
    dsimp only [f]
    exact
      (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_hasDerivAt_coordinate_at
        hν ht.le htwoA htwoA W W hWcont hWcont
        (fun s _ => hWbound s)
        (fun s _ => hWbound s)
        i j x r).deriv

  have hDerivC1 : ContDiff ℝ 1 (deriv f) := by
    rw [hDerivEq]
    exact
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel_selectedRestart_secondCoordinate_contDiff_one
        hν U₀ hA hU₀ ht htR i j j x

  have hC2 : ContDiff ℝ (1 + 1) f := by
    exact
      (contDiff_succ_iff_deriv).2
        ⟨hDiff, by simp, hDerivC1⟩

  have hC2' : ContDiff ℝ 2 f := by
    exact hC2.of_le (by norm_num)

  simpa only [f, e] using hC2'

end
end Euclidean
end Bridge
end PrimeTensor
