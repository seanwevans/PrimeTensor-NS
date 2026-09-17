import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongOldAdvectionProductEnvelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.AdvectionMass

/-!
# Endpoint-independent integrability of differentiated-advection products

The previous increment removed endpoint continuity from the two pointwise
product envelopes

    |(∂ₐuᵢ)(∂ᵢuⱼ)|,
    |uᵢ (∂ₐ∂ᵢuⱼ)|.

The spatial factors left on the right are first- and second-order derivatives
of the old velocity.  Their `L²` square bounds already follow directly from
the canonical H³ tail.  A compact weak test belongs to `L²`, so Cauchy gives
an integrable base product; multiplying by the explicit pointwise envelope
constant preserves integrability.

This file therefore reproduces the two integrability inputs from the older
endpoint `AdvectionMass` stack without
`H3PreterminalCanonicalL2EndpointContinuousOnElapsed`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldAdvectionProductIntegrable
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongOldAdvectionProductIntegrable :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The compact-test-weighted first-times-first differentiated-advection
product is integrable from the H³ tail alone. -/
theorem integrable_weakTestNorm_mul_norm_h3LoggedPreterminalDifferentiatedAdvectionFirstProduct_tailH3_weakStrong
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
    Integrable
      (fun x : Point3 =>
        ‖ψ x‖ *
          ‖h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
              u (t + (q : ℝ)) a i j x‖)
      (volume : Measure Point3) := by
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
      h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
        u (t + (q : ℝ)) a i j x

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
    dsimp only [
      g,
      h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
    ]
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
        (volume : Measure Point3) :=
    MemLp.integrable_mul
      hψTwo.norm
      hfTwo.norm

  let C : ℝ :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      (2 * E)

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

  have hPoint :
      ∀ x : Point3,
        ‖ψ x‖ * ‖g x‖
          ≤
        C * (‖ψ x‖ * ‖f x‖) := by
    intro x

    have hProduct :=
      norm_loggedVelocityComponent_spatial_d_mul_spatial_d_le_tailH3Envelope_weakStrong
        hNS ht hEnd hE hTail
        q a i j x

    dsimp only [g, f, C]

    calc
      ‖ψ x‖ *
          ‖h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
              u (t + (q : ℝ)) a i j x‖
          ≤
        ‖ψ x‖ *
          (
            (
              h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
                (2 * E)
            )
              *
            ‖spatial3.d
                i
                (loggedVelocityComponent
                  u (t + (q : ℝ)) j)
                x‖
          ) := by
            apply mul_le_mul_of_nonneg_left
            · simpa only [
                h3LoggedPreterminalDifferentiatedAdvectionFirstProduct
              ] using hProduct
            · exact norm_nonneg _
      _ =
        (
          h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            (2 * E)
        )
          *
        (
          ‖ψ x‖ *
            ‖spatial3.d
                i
                (loggedVelocityComponent
                  u (t + (q : ℝ)) j)
                x‖
        ) := by ring

  have hInt :
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
    exact hPoint x

  simpa only [g] using hInt

/-- The compact-test-weighted zeroth-times-second differentiated-advection
product is integrable from the H³ tail alone. -/
theorem integrable_weakTestNorm_mul_norm_h3LoggedPreterminalDifferentiatedAdvectionSecondProduct_tailH3_weakStrong
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
    Integrable
      (fun x : Point3 =>
        ‖ψ x‖ *
          ‖h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
              u (t + (q : ℝ)) a i j x‖)
      (volume : Measure Point3) := by
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
      h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
        u (t + (q : ℝ)) a i j x

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
    dsimp only [
      g,
      h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
    ]
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
        (volume : Measure Point3) :=
    MemLp.integrable_mul
      hψTwo.norm
      hfTwo.norm

  let C : ℝ :=
    h3RawFourierL1DeweightingCoefficient *
      (2 * E)

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

  have hPoint :
      ∀ x : Point3,
        ‖ψ x‖ * ‖g x‖
          ≤
        C * (‖ψ x‖ * ‖f x‖) := by
    intro x

    have hProduct :=
      norm_loggedVelocityComponent_mul_spatial_d2_le_tailH3Envelope_weakStrong
        hNS ht hEnd hE hTail
        q a i j x

    dsimp only [g, f, C]

    calc
      ‖ψ x‖ *
          ‖h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
              u (t + (q : ℝ)) a i j x‖
          ≤
        ‖ψ x‖ *
          (
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
                x‖
          ) := by
            apply mul_le_mul_of_nonneg_left
            · simpa only [
                h3LoggedPreterminalDifferentiatedAdvectionSecondProduct
              ] using hProduct
            · exact norm_nonneg _
      _ =
        (
          h3RawFourierL1DeweightingCoefficient *
            (2 * E)
        )
          *
        (
          ‖ψ x‖ *
            ‖spatial3.d
                a
                (spatial3.d
                  i
                  (loggedVelocityComponent
                    u (t + (q : ℝ)) j))
                x‖
        ) := by ring

  have hInt :
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
    exact hPoint x

  simpa only [g] using hInt

end

end Euclidean
end Bridge
end PrimeTensor
