import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Cauchy

/-!
# Pointwise endpoint envelopes for differentiated advection products

`RHSExpansion` writes one spatial derivative of advection as the sum of terms

    (∂ₐ uᵢ)(∂ᵢ uⱼ)
    uᵢ (∂ₐ∂ᵢ uⱼ).

`Envelope` already bounds the first factor in each product uniformly on the
closed endpoint interval:

    |∂ₐ uᵢ| ≤ C₁ (2E),
    |uᵢ|    ≤ C₀ (2E).

This file packages those two bounds directly at the product level.  The
remaining factors are precisely first- and second-order velocity derivatives,
so `SquareBound` plus the Cauchy bridge can estimate their compact-test
spatial mass in the next increment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- First-times-first differentiated-advection product: use the endpoint
first-derivative envelope on the left factor. -/
theorem norm_loggedVelocityComponent_spatial_d_mul_spatial_d_le_endpointH3Envelope
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
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
  exact
    mul_le_mul_of_nonneg_right
      (norm_loggedVelocityComponent_spatial_d_le_endpointH3Envelope
        hNS ht hEnd hE hTail hEndpoint
        q a i x)
      (norm_nonneg _)

/-- Zeroth-times-second differentiated-advection product: use the endpoint
velocity envelope on the left factor. -/
theorem norm_loggedVelocityComponent_mul_spatial_d2_le_endpointH3Envelope
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
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
      (norm_loggedVelocityComponent_le_endpointH3Envelope
        hNS ht hEnd hE hTail hEndpoint
        q i x)
      (norm_nonneg _)

end

end Euclidean
end Bridge
end PrimeTensor
