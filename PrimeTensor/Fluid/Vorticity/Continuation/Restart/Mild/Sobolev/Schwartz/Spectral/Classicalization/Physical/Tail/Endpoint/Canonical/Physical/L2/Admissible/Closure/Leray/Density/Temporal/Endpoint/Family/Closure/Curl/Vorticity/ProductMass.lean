import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.ProductEnvelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Preterminal.Canonical.Energy.Restart.Closure

/-!
# Compact-test spatial mass bounds for differentiated advection products

`ProductEnvelope` gives the two pointwise product bounds occurring in one
spatial derivative of advection.  This file integrates them against a fixed
compact weak test.

The generic helper below combines:

* a pointwise domination `‖g‖ ≤ C ‖f‖`;
* `SpatialL2SquareBound f M`;
* Cauchy--Schwarz against the compact test.

It yields

    ∫ ‖ψ‖ ‖g‖
      ≤ C * (‖ψ‖₂ * M^(1/2)).

The two endpoint specializations then apply this to the exact
first-times-first and zeroth-times-second products from `ProductEnvelope`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EndpointCurlVorticityProductMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3EndpointCurlVorticityProductMass :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Integrate a pointwise constant-times-`L²` domination against a compact weak
test. -/
theorem integral_weakTest_norm_mul_norm_le_of_pointwise_le_spatialL2SquareBound
    (ψ : H3WeakTestFunction)
    {f g : ScalarField3}
    {C M : ℝ}
    (hC : 0 ≤ C)
    (hfMeas :
      AEStronglyMeasurable
        f
        (volume : Measure Point3))
    (hgMeas :
      AEStronglyMeasurable
        g
        (volume : Measure Point3))
    (hBound : SpatialL2SquareBound f M)
    (hPoint :
      ∀ x : Point3,
        ‖g x‖ ≤ C * ‖f x‖) :
    (∫ x : Point3,
        ‖ψ x‖ * ‖g x‖
      ∂volume)
      ≤
    C *
      (
        h3WeakTestFunctionL2Mass ψ *
          M ^ (1 / (2 : ℝ))
      ) := by
  have hψTwo :
      MemLp
        (ψ : Point3 → ℝ)
        2
        (volume : Measure Point3) :=
    ψ.continuous.memLp_of_hasCompactSupport
      ψ.hasCompactSupport

  have hfTwo :
      MemLp
        f
        2
        (volume : Measure Point3) :=
    memLp_two_of_spatialL2SquareBound
      hfMeas hBound

  have hBaseInt :
      Integrable
        (fun x : Point3 =>
          ‖ψ x‖ * ‖f x‖)
        (volume : Measure Point3) := by
    exact
      MemLp.integrable_mul
        hψTwo.norm
        hfTwo.norm

  have hMajorInt :
      Integrable
        (fun x : Point3 =>
          C * (‖ψ x‖ * ‖f x‖))
        (volume : Measure Point3) :=
    hBaseInt.const_mul C

  have hTargetMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          ‖ψ x‖ * ‖g x‖)
        (volume : Measure Point3) :=
    ψ.continuous.aestronglyMeasurable.norm.mul
      hgMeas.norm

  have hPointWeighted :
      ∀ x : Point3,
        ‖ψ x‖ * ‖g x‖
          ≤
        C * (‖ψ x‖ * ‖f x‖) := by
    intro x
    calc
      ‖ψ x‖ * ‖g x‖
          ≤
        ‖ψ x‖ * (C * ‖f x‖) :=
        mul_le_mul_of_nonneg_left
          (hPoint x)
          (norm_nonneg (ψ x))
      _ =
        C * (‖ψ x‖ * ‖f x‖) := by
        ring

  have hTargetInt :
      Integrable
        (fun x : Point3 =>
          ‖ψ x‖ * ‖g x‖)
        (volume : Measure Point3) := by
    refine
      hMajorInt.mono'
        hTargetMeas
        (Filter.Eventually.of_forall ?_)
    intro x
    rw [
      Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg
          (norm_nonneg (ψ x))
          (norm_nonneg (g x)))
    ]
    exact hPointWeighted x

  have hIntegralLe :
      (∫ x : Point3,
          ‖ψ x‖ * ‖g x‖
        ∂volume)
        ≤
      ∫ x : Point3,
        C * (‖ψ x‖ * ‖f x‖)
        ∂volume :=
    integral_mono_ae
      hTargetInt
      hMajorInt
      (Filter.Eventually.of_forall hPointWeighted)

  have hCauchy :=
    integral_weakTest_norm_mul_norm_le_of_spatialL2SquareBound
      ψ hfMeas hBound

  calc
    (∫ x : Point3,
        ‖ψ x‖ * ‖g x‖
      ∂volume)
        ≤
      C *
        (∫ x : Point3,
          ‖ψ x‖ * ‖f x‖
          ∂volume) := by
          simpa only [integral_const_mul] using hIntegralLe
    _ ≤
      C *
        (
          h3WeakTestFunctionL2Mass ψ *
            M ^ (1 / (2 : ℝ))
        ) :=
      mul_le_mul_of_nonneg_left
        hCauchy
        hC

/-- Compact-test `L¹` mass bound for a first-times-first differentiated
advection product. -/
theorem integral_weakTest_norm_mul_norm_loggedVelocityComponent_spatial_d_mul_spatial_d_le_endpointH3
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
      norm_loggedVelocityComponent_spatial_d_mul_spatial_d_le_endpointH3Envelope
        hNS ht hEnd hE hTail hEndpoint
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
advection product. -/
theorem integral_weakTest_norm_mul_norm_loggedVelocityComponent_mul_spatial_d2_le_endpointH3
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
      norm_loggedVelocityComponent_mul_spatial_d2_le_endpointH3Envelope
        hNS ht hEnd hE hTail hEndpoint
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
