import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongOldGradientEnvelope

/-!
# Endpoint-independent old velocity envelope

`SelectedOldWeakStrongOldGradientEnvelope` already removed endpoint continuity
from the pointwise first-gradient estimate for the old branch.

The nonlinear pressure-free vorticity estimates also need the corresponding
zeroth-order pointwise bound

    |u_j(t+q,x)| ≤ C₀ (2E).

The endpoint-era vorticity files obtained this through the endpoint-normalized
spectral path, which unnecessarily introduced
`H3PreterminalCanonicalL2EndpointContinuousOnElapsed`.

This file proves the same bound directly from the canonical spectral snapshot

    h3PreterminalTailCanonicalSpectralStateOnElapsed,

whose norm is already bounded by `2E` from `CanonicalH3TailDataFrom` alone and
whose real `C¹` representative is pointwise equal to the genuine old velocity.

Thus both pointwise factors needed by the differentiated-advection estimate,

* `u`,
* `∇u`,

are now endpoint-independent.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldVelocityEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Endpoint-independent uniform pointwise bound for every old logged velocity
component on one closed elapsed interval. -/
theorem norm_loggedVelocityComponent_le_tailH3Envelope_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (j : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    ‖loggedVelocityComponent
        u (t + (q : ℝ)) j x‖
      ≤
    h3RawFourierL1DeweightingCoefficient * (2 * E) := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  let k : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have hOld :
      h3SpectralScalarRealC1RepresentativeOnPoint3
          (U k)
        =
      loggedVelocityComponent
        u (t + (q : ℝ)) j := by
    have h :=
      h3PreterminalTailCanonicalSpectralStateOnElapsed_component_eq_old
        hNS ht hEnd hTail q k

    dsimp only [U, k] at h ⊢

    simpa only [
      h3SpectralVelocityRealC1RepresentativeOnPoint3,
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
    ] using h

  have hEvaluation :
      ‖h3SpectralScalarRealC1RepresentativeOnPoint3
          (U k) x‖
        ≤
      h3RawFourierL1DeweightingCoefficient * ‖U k‖ := by
    exact
      norm_h3SpectralScalarRealC1RepresentativeOnPoint3_apply_le
        (U k) x

  have hCoordinate :
      ‖U k‖ ≤ ‖U‖ := by
    exact
      h3SpectralFinVector_coordinate_norm_le
        U k

  have hState :
      ‖U‖ ≤ 2 * E := by
    dsimp only [U]

    exact
      norm_h3PreterminalTailCanonicalSpectralStateOnElapsed_le_twoE_weakStrong
        hNS ht hEnd hE hTail q

  have hScalar :
      ‖U k‖ ≤ 2 * E :=
    hCoordinate.trans hState

  have hBound :
      ‖h3SpectralScalarRealC1RepresentativeOnPoint3
          (U k) x‖
        ≤
      h3RawFourierL1DeweightingCoefficient * (2 * E) :=
    hEvaluation.trans
      (mul_le_mul_of_nonneg_left
        hScalar
        h3RawFourierL1DeweightingCoefficient_nonneg)

  have hPointEq :
      h3SpectralScalarRealC1RepresentativeOnPoint3
          (U k) x
        =
      loggedVelocityComponent
        u (t + (q : ℝ)) j x :=
    congrFun hOld x

  rw [← hPointEq]

  exact hBound

/-- The same endpoint-independent zeroth-order envelope, phrased through the
old elapsed weak--strong velocity field. -/
theorem h3PreterminalOldElapsedWeakStrongVelocity_component_le_velocityEnvelope
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    abs
      (((h3PreterminalOldElapsedWeakStrongVelocity u t)
        (q : ℝ) x).component j)
      ≤
    h3RawFourierL1DeweightingCoefficient * (2 * E) := by
  change
    abs
      (loggedVelocityComponent
        u (t + (q : ℝ)) j x)
      ≤
    h3RawFourierL1DeweightingCoefficient * (2 * E)

  simpa only [Real.norm_eq_abs] using
    norm_loggedVelocityComponent_le_tailH3Envelope_weakStrong
      hNS ht hEnd hE hTail q j x

end

end Euclidean
end Bridge
end PrimeTensor
