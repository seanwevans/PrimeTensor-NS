import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongOldAdvectionProductIntegrable
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.ProductMass

/-!
# Endpoint-independent compact-test masses for differentiated advection products

`ProductMass` already contains the generic endpoint-free Cauchy bridge

    ∫ ‖ψ‖ ‖g‖
      ≤ C * (‖ψ‖₂ * M^(1/2))

from a pointwise bound `‖g‖ ≤ C ‖f‖` and an `L²` square bound on `f`.

Its two old endpoint specializations carried
`H3PreterminalCanonicalL2EndpointContinuousOnElapsed` only because their
pointwise product envelopes did.

Those envelopes are now available directly from `CanonicalH3TailDataFrom`.
This file therefore reproduces the two quantitative product-mass estimates
with exactly the same constants but no endpoint-continuity hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldAdvectionProductMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongOldAdvectionProductMass :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Compact-test `L¹` mass bound for a first-times-first differentiated
advection product, directly from the retained H³ tail. -/
theorem integral_weakTest_norm_mul_norm_loggedVelocityComponent_spatial_d_mul_spatial_d_le_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau)
    (a i j : PrimeTensor.Axis Depth.three) :
    (∫ x : Point3,
        ‖ψ x‖ *
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
      ∂volume)
      ≤
    (
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        (2 * E)
    )
      *
    (
      h3WeakTestFunctionL2Mass ψ *
        (2 * E) ^ (1 / (2 : ℝ))
    ) := by
  have hs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith [ht.1, q.2.1]
    · linarith [hEnd, q.2.2]

  have hMeas :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS hs

  have hi := hMeas i
  have hj := hMeas j
  dsimp only at hi hj

  let f : ScalarField3 :=
    spatial3.d
      i
      (loggedVelocityComponent
        u (t + (q : ℝ)) j)

  let g : ScalarField3 :=
    fun x =>
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

  have hfMeas :
      AEStronglyMeasurable
        f
        (volume : Measure Point3) := by
    dsimp only [f]
    exact hj.2.1 i

  have hgMeas :
      AEStronglyMeasurable
        g
        (volume : Measure Point3) := by
    dsimp only [g]
    exact
      (hi.2.1 a).mul
        (hj.2.1 i)

  have hBound :
      SpatialL2SquareBound
        f
        (2 * E) := by
    dsimp only [f]
    exact
      loggedVelocityComponent_spatial_d_spatialL2SquareBound_endpoint_twoE
        hEnd hE hTail q i j

  have hC :
      0 ≤
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          (2 * E) := by
    have hCoeff :
        0 ≤
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient :=
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
    have hTwoE : 0 ≤ 2 * E := by
      nlinarith [hE]
    exact mul_nonneg hCoeff hTwoE

  have hPoint :
      ∀ x : Point3,
        ‖g x‖
          ≤
        (
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            (2 * E)
        )
          *
        ‖f x‖ := by
    intro x
    dsimp only [g, f]
    exact
      norm_loggedVelocityComponent_spatial_d_mul_spatial_d_le_tailH3Envelope_weakStrong
        hNS ht hEnd hE hTail
        q a i j x

  simpa only [g, f] using
    integral_weakTest_norm_mul_norm_le_of_pointwise_le_spatialL2SquareBound
      ψ
      hC
      hfMeas
      hgMeas
      hBound
      hPoint

/-- Compact-test `L¹` mass bound for a zeroth-times-second differentiated
advection product, directly from the retained H³ tail. -/
theorem integral_weakTest_norm_mul_norm_loggedVelocityComponent_mul_spatial_d2_le_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau)
    (a i j : PrimeTensor.Axis Depth.three) :
    (∫ x : Point3,
        ‖ψ x‖ *
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
      ∂volume)
      ≤
    (
      h3RawFourierL1DeweightingCoefficient *
        (2 * E)
    )
      *
    (
      h3WeakTestFunctionL2Mass ψ *
        (2 * E) ^ (1 / (2 : ℝ))
    ) := by
  have hs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith [ht.1, q.2.1]
    · linarith [hEnd, q.2.2]

  have hMeas :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS hs

  have hi := hMeas i
  have hj := hMeas j
  dsimp only at hi hj

  let f : ScalarField3 :=
    spatial3.d
      a
      (spatial3.d
        i
        (loggedVelocityComponent
          u (t + (q : ℝ)) j))

  let g : ScalarField3 :=
    fun x =>
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

  have hfMeas :
      AEStronglyMeasurable
        f
        (volume : Measure Point3) := by
    dsimp only [f]
    exact hj.2.2.1 a i

  have hgMeas :
      AEStronglyMeasurable
        g
        (volume : Measure Point3) := by
    dsimp only [g]
    exact
      hi.1.mul
        (hj.2.2.1 a i)

  have hBound :
      SpatialL2SquareBound
        f
        (2 * E) := by
    dsimp only [f]
    exact
      loggedVelocityComponent_spatial_d2_spatialL2SquareBound_endpoint_twoE
        hEnd hE hTail q a i j

  have hC :
      0 ≤
        h3RawFourierL1DeweightingCoefficient *
          (2 * E) := by
    have hCoeff :
        0 ≤ h3RawFourierL1DeweightingCoefficient :=
      h3RawFourierL1DeweightingCoefficient_nonneg
    have hTwoE : 0 ≤ 2 * E := by
      nlinarith [hE]
    exact mul_nonneg hCoeff hTwoE

  have hPoint :
      ∀ x : Point3,
        ‖g x‖
          ≤
        (
          h3RawFourierL1DeweightingCoefficient *
            (2 * E)
        )
          *
        ‖f x‖ := by
    intro x
    dsimp only [g, f]
    exact
      norm_loggedVelocityComponent_mul_spatial_d2_le_tailH3Envelope_weakStrong
        hNS ht hEnd hE hTail
        q a i j x

  simpa only [g, f] using
    integral_weakTest_norm_mul_norm_le_of_pointwise_le_spatialL2SquareBound
      ψ
      hC
      hfMeas
      hgMeas
      hBound
      hPoint

end

end Euclidean
end Bridge
end PrimeTensor
