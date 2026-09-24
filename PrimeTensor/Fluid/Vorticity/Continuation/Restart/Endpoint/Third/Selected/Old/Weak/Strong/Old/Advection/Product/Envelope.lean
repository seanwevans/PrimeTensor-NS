import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Old.Velocity.Envelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.RHSExpansion

/-!
# Endpoint-independent old differentiated-advection product envelopes

The pressure-free vorticity route expands one spatial derivative of advection
into the two standard product types

    (∂ₐ uᵢ)(∂ᵢ uⱼ),
    uᵢ (∂ₐ∂ᵢ uⱼ).

The older endpoint-vorticity stack bounded these products using pointwise
velocity and first-gradient envelopes that were routed through an
endpoint-normalized spectral path, hence carried
`H3PreterminalCanonicalL2EndpointContinuousOnElapsed`.

That dependency is unnecessary.

The preceding weak--strong files now provide directly from
`CanonicalH3TailDataFrom`:

    |uᵢ|     ≤ C₀ (2E),
    |∂ₐ uᵢ| ≤ C₁ (2E).

This file transports those endpoint-independent bounds to the two product
majorants.  The remaining factors are exactly first- and second-order spatial
derivatives, which are already controlled in L² by the retained H³ tail.

No endpoint continuity hypothesis occurs below.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldAdvectionProductEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Endpoint-independent first-times-first differentiated-advection product
bound. -/
theorem norm_loggedVelocityComponent_spatial_d_mul_spatial_d_le_tailH3Envelope_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (a i j : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    ‖(
      spatial3.d
          a
          (loggedVelocityComponent
            u (t + (q : ℝ)) i)
          x
        *
      spatial3.d
          i
          (loggedVelocityComponent
            u (t + (q : ℝ)) j)
          x
    )‖
      ≤
    (
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        (2 * E)
    )
      *
    ‖spatial3.d
        i
        (loggedVelocityComponent
          u (t + (q : ℝ)) j)
        x‖ := by
  rw [norm_mul]

  apply
    mul_le_mul_of_nonneg_right
      ?_
      (norm_nonneg _)

  have hGradient :=
    h3PreterminalOldElapsedWeakStrongVelocity_spatial_d_le_gradientEnvelope
      hNS ht hEnd hE hTail
      q x i a

  change
    abs
      (spatial3.d
        a
        (loggedVelocityComponent
          u (t + (q : ℝ)) i)
        x)
      ≤
    h3PreterminalSelectedWeakStrongGradientEnvelope E
    at hGradient

  unfold h3PreterminalSelectedWeakStrongGradientEnvelope at hGradient

  simpa only [Real.norm_eq_abs] using hGradient

/-- Endpoint-independent zeroth-times-second differentiated-advection product
bound. -/
theorem norm_loggedVelocityComponent_mul_spatial_d2_le_tailH3Envelope_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (a i j : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    ‖(
      loggedVelocityComponent
          u (t + (q : ℝ)) i x
        *
      spatial3.d
          a
          (spatial3.d
            i
            (loggedVelocityComponent
              u (t + (q : ℝ)) j))
          x
    )‖
      ≤
    (
      h3RawFourierL1DeweightingCoefficient *
        (2 * E)
    )
      *
    ‖spatial3.d
        a
        (spatial3.d
          i
          (loggedVelocityComponent
            u (t + (q : ℝ)) j))
        x‖ := by
  rw [norm_mul]

  exact
    mul_le_mul_of_nonneg_right
      (norm_loggedVelocityComponent_le_tailH3Envelope_weakStrong
        hNS ht hEnd hE hTail
        q i x)
      (norm_nonneg _)

end

end Euclidean
end Bridge
end PrimeTensor
