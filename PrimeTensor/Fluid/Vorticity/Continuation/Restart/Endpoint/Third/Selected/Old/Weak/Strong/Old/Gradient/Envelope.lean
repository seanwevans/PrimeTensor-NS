import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Automatic.Spatial.Data
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Preterminal.Canonical.Path

/-!
# Endpoint-independent old first-gradient envelope

The first weak--strong transport estimate was organized using

    (S · ∇)S - (O · ∇)O
      =
    ((S-O) · ∇)S + O · ∇(S-O),

so the surviving quadratic term is controlled by the selected gradient.

There is a symmetric decomposition

    (S · ∇)S - (O · ∇)O
      =
    S · ∇(S-O) + ((S-O) · ∇)O.

This alternate form moves the pure-transport cancellation onto the selected
restart branch.  At positive restart time that branch has the strongest decay
available in the project, while the surviving term only requires a uniform
first-gradient bound for the old branch.

This file proves that old gradient bound directly from
`CanonicalH3TailDataFrom`, with no endpoint-continuity hypothesis.

Every old elapsed slice is its canonical weighted H³ spectral state.  The tail
energy gives the uniform spectral bound `‖U(q)‖ ≤ 2E`; coordinate projection
does not increase the norm; and the existing inverse-Fourier first-derivative
evaluation estimate then gives

    |∂ᵢ Oⱼ(q,x)|
      ≤ C₁ (2E).

Thus the very same explicit envelope already used for the selected branch also
controls the old branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldGradientEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every canonical old spectral snapshot on a strict elapsed interval has
norm at most `2E`, directly from the retained tail H³ bound. -/
theorem norm_h3PreterminalTailCanonicalSpectralStateOnElapsed_le_twoE_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau) :
    ‖h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q‖
      ≤
    2 * E := by
  exact
    norm_h3PreterminalCanonicalSpectralStateOnElapsed_le_twoA
      hNS
      ht
      hEnd
      hE
      (canonicalH3TailDataFrom_integrableOnElapsed
        hEnd hTail)
      (canonicalH3TailDataFrom_energyOnElapsed_le_twoE
        hE hEnd hTail)
      q

/-- Endpoint-independent uniform first-gradient bound for the old elapsed
preterminal velocity.  It uses exactly the same explicit envelope as the
selected restart. -/
theorem h3PreterminalOldElapsedWeakStrongVelocity_spatial_d_le_gradientEnvelope
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
    (j i : PrimeTensor.Axis Depth.three) :
    abs
      (spatial3.d
        i
        (fun y =>
          ((h3PreterminalOldElapsedWeakStrongVelocity u t)
            (q : ℝ) y).component j)
        x)
      ≤
    h3PreterminalSelectedWeakStrongGradientEnvelope E := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  let k : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  let a : Fin 3 :=
    h3ClassicalizationFinOfAxis i

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
      ‖spatial3.d
          i
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (U k))
          x‖
        ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        ‖U k‖ := by
    have h :=
      norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_apply_le
        (U k) a x

    dsimp only [a] at h

    rw [
      h3AxisOfFin3_h3ClassicalizationFinOfAxis i
    ] at h

    exact h

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
      ‖spatial3.d
          i
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (U k))
          x‖
        ≤
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        (2 * E) :=
    hEvaluation.trans
      (mul_le_mul_of_nonneg_left
        hScalar
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg)

  have hDerivativeEq :
      spatial3.d
          i
          (loggedVelocityComponent
            u (t + (q : ℝ)) j)
          x
        =
      spatial3.d
          i
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (U k))
          x := by
    exact
      congrArg
        (fun f : Point3 → ℝ =>
          spatial3.d i f x)
        hOld.symm

  change
    abs
      (spatial3.d
        i
        (loggedVelocityComponent
          u (t + (q : ℝ)) j)
        x)
      ≤
    h3PreterminalSelectedWeakStrongGradientEnvelope E

  rw [hDerivativeEq]

  unfold h3PreterminalSelectedWeakStrongGradientEnvelope

  simpa only [Real.norm_eq_abs] using hBound

end

end Euclidean
end Bridge
end PrimeTensor
