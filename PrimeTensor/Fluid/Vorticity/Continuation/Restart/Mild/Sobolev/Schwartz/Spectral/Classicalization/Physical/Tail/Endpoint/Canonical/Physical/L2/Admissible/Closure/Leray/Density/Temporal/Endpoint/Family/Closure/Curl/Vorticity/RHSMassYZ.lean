import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.RHSMassX

/-!
# Compact-test endpoint mass bounds for the y/z vorticity RHS

`RHSMassX` closed the first pressure-free vorticity component and introduced
the common axis-independent endpoint envelope.  The remaining two components
are cyclic copies of the same four-term argument.

This file adds a reusable integrability helper under four integrable
majorants, then closes both y and z with the same diffusion/advection envelope
already used for x.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EndpointCurlVorticityRHSMassYZ
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3EndpointCurlVorticityRHSMassYZ :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- A nonnegative measurable target dominated by four integrable summands is
integrable. -/
theorem integrable_of_le_four_integrable_majorants
    {f f₁ f₂ f₃ f₄ : Point3 → ℝ}
    (hfMeas :
      AEStronglyMeasurable
        f
        (volume : Measure Point3))
    (hfNonneg :
      ∀ x : Point3,
        0 ≤ f x)
    (hf₁Int :
      Integrable f₁ (volume : Measure Point3))
    (hf₂Int :
      Integrable f₂ (volume : Measure Point3))
    (hf₃Int :
      Integrable f₃ (volume : Measure Point3))
    (hf₄Int :
      Integrable f₄ (volume : Measure Point3))
    (hPoint :
      ∀ x : Point3,
        f x
          ≤
        (f₁ x + f₂ x) + (f₃ x + f₄ x)) :
    Integrable f (volume : Measure Point3) := by
  have hMajorInt :
      Integrable
        (fun x : Point3 =>
          (f₁ x + f₂ x) + (f₃ x + f₄ x))
        (volume : Measure Point3) :=
    (hf₁Int.add hf₂Int).add
      (hf₃Int.add hf₄Int)

  refine
    hMajorInt.mono'
      hfMeas
      (Filter.Eventually.of_forall ?_)

  intro x
  rw [
    Real.norm_eq_abs,
    abs_of_nonneg (hfNonneg x)
  ]
  exact hPoint x

/-- The compact-test-weighted y pressure-free vorticity RHS is integrable on
each closed endpoint slice. -/
theorem integrable_weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSY_endpoint
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
    (q : Set.Icc (0 : ℝ) tau) :
    Integrable
      (fun x : Point3 =>
        ‖ψ x‖ *
          ‖h3LoggedPreterminalVorticityRHSY
              u (t + (q : ℝ)) x‖)
      (volume : Measure Point3) := by
  have hs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith [ht.1, q.2.1]
    · linarith [hEnd, q.2.2]

  let d₁ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            zAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component xAxis))
            x‖

  let d₂ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            xAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component zAxis))
            x‖

  let a₁ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            zAxis
            (fun y =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                y
                xAxis)
            x‖

  let a₂ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            xAxis
            (fun y =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                y
                zAxis)
            x‖

  have hxEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) xAxis
        =
      fun y =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component xAxis := by
    rfl

  have hzEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) zAxis
        =
      fun y =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component zAxis := by
    rfl

  have hd₁Int :
      Integrable d₁ (volume : Measure Point3) := by
    have h :=
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_endpoint
        hNS ht hEnd hE hTail
        ψ q zAxis xAxis
    rw [hxEq] at h
    simpa only [d₁] using h

  have hd₂Int :
      Integrable d₂ (volume : Measure Point3) := by
    have h :=
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_endpoint
        hNS ht hEnd hE hTail
        ψ q xAxis zAxis
    rw [hzEq] at h
    simpa only [d₂] using h

  have ha₁Int :
      Integrable a₁ (volume : Measure Point3) := by
    dsimp only [a₁]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_endpoint
        hNS ht hEnd hE hTail hEndpoint
        ψ q zAxis xAxis

  have ha₂Int :
      Integrable a₂ (volume : Measure Point3) := by
    dsimp only [a₂]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_endpoint
        hNS ht hEnd hE hTail hEndpoint
        ψ q xAxis zAxis

  have hExtMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
            hNS (t + (q : ℝ)) x)
        (volume : Measure Point3) :=
    (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
      hNS (t + (q : ℝ))).continuous.aestronglyMeasurable

  have hRHSMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityRHSY
            u (t + (q : ℝ)) x)
        (volume : Measure Point3) := by
    have hEq :
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityRHSY
            u (t + (q : ℝ)) x)
          =
        fun x : Point3 =>
          h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
            hNS (t + (q : ℝ)) x := by
      funext x
      exact
        (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension_apply_eq_rhs_of_mem
          hNS hs x).symm
    rw [hEq]
    exact hExtMeas

  have hTargetMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          ‖ψ x‖ *
            ‖h3LoggedPreterminalVorticityRHSY
                u (t + (q : ℝ)) x‖)
        (volume : Measure Point3) :=
    ψ.continuous.aestronglyMeasurable.norm.mul
      hRHSMeas.norm

  have hPoint :
      ∀ x : Point3,
        ‖ψ x‖ *
            ‖h3LoggedPreterminalVorticityRHSY
                u (t + (q : ℝ)) x‖
          ≤
        (d₁ x + d₂ x) + (a₁ x + a₂ x) := by
    intro x
    dsimp only [d₁, d₂, a₁, a₂]
    exact
      weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSY_le_four
        hNS hs ψ x

  exact
    integrable_of_le_four_integrable_majorants
      hTargetMeas
      (fun x : Point3 =>
        mul_nonneg
          (norm_nonneg (ψ x))
          (norm_nonneg
            (h3LoggedPreterminalVorticityRHSY
              u (t + (q : ℝ)) x)))
      hd₁Int hd₂Int ha₁Int ha₂Int hPoint

/-- Uniform compact-test spatial mass bound for the y pressure-free vorticity
RHS on every closed endpoint slice. -/
theorem integral_weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSY_le_endpointH3
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
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ x : Point3,
        ‖ψ x‖ *
          ‖h3LoggedPreterminalVorticityRHSY
              u (t + (q : ℝ)) x‖
      ∂volume)
      ≤
    h3EndpointVorticityRHSWeakMassEnvelope E ψ := by
  have hs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith [ht.1, q.2.1]
    · linarith [hEnd, q.2.2]

  let d₁ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            zAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component xAxis))
            x‖

  let d₂ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            xAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component zAxis))
            x‖

  let a₁ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            zAxis
            (fun y =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                y
                xAxis)
            x‖

  let a₂ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            xAxis
            (fun y =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                y
                zAxis)
            x‖

  have hxEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) xAxis
        =
      fun y =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component xAxis := by
    rfl

  have hzEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) zAxis
        =
      fun y =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component zAxis := by
    rfl

  have hd₁Int :
      Integrable d₁ (volume : Measure Point3) := by
    have h :=
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_endpoint
        hNS ht hEnd hE hTail
        ψ q zAxis xAxis
    rw [hxEq] at h
    simpa only [d₁] using h

  have hd₂Int :
      Integrable d₂ (volume : Measure Point3) := by
    have h :=
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_endpoint
        hNS ht hEnd hE hTail
        ψ q xAxis zAxis
    rw [hzEq] at h
    simpa only [d₂] using h

  have ha₁Int :
      Integrable a₁ (volume : Measure Point3) := by
    dsimp only [a₁]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_endpoint
        hNS ht hEnd hE hTail hEndpoint
        ψ q zAxis xAxis

  have ha₂Int :
      Integrable a₂ (volume : Measure Point3) := by
    dsimp only [a₂]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_endpoint
        hNS ht hEnd hE hTail hEndpoint
        ψ q xAxis zAxis

  have hExtMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
            hNS (t + (q : ℝ)) x)
        (volume : Measure Point3) :=
    (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
      hNS (t + (q : ℝ))).continuous.aestronglyMeasurable

  have hRHSMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityRHSY
            u (t + (q : ℝ)) x)
        (volume : Measure Point3) := by
    have hEq :
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityRHSY
            u (t + (q : ℝ)) x)
          =
        fun x : Point3 =>
          h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension
            hNS (t + (q : ℝ)) x := by
      funext x
      exact
        (h3LoggedPreterminalVorticityYTemporalDerivativeContinuousMapExtension_apply_eq_rhs_of_mem
          hNS hs x).symm
    rw [hEq]
    exact hExtMeas

  have hTargetMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          ‖ψ x‖ *
            ‖h3LoggedPreterminalVorticityRHSY
                u (t + (q : ℝ)) x‖)
        (volume : Measure Point3) :=
    ψ.continuous.aestronglyMeasurable.norm.mul
      hRHSMeas.norm

  have hPoint :
      ∀ x : Point3,
        ‖ψ x‖ *
            ‖h3LoggedPreterminalVorticityRHSY
                u (t + (q : ℝ)) x‖
          ≤
        (d₁ x + d₂ x) + (a₁ x + a₂ x) := by
    intro x
    dsimp only [d₁, d₂, a₁, a₂]
    exact
      weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSY_le_four
        hNS hs ψ x

  have hd₁Bound :
      (∫ x : Point3, d₁ x ∂volume)
        ≤
      h3EndpointDifferentiatedDiffusionWeakMassEnvelope E ψ := by
    have h :=
      integral_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_le_endpointH3
        hNS ht hEnd hE hTail
        ψ q zAxis xAxis
    rw [hxEq] at h
    simpa only [
      d₁,
      h3EndpointDifferentiatedDiffusionWeakMassEnvelope
    ] using h

  have hd₂Bound :
      (∫ x : Point3, d₂ x ∂volume)
        ≤
      h3EndpointDifferentiatedDiffusionWeakMassEnvelope E ψ := by
    have h :=
      integral_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_le_endpointH3
        hNS ht hEnd hE hTail
        ψ q xAxis zAxis
    rw [hzEq] at h
    simpa only [
      d₂,
      h3EndpointDifferentiatedDiffusionWeakMassEnvelope
    ] using h

  have ha₁Bound :
      (∫ x : Point3, a₁ x ∂volume)
        ≤
      h3EndpointDifferentiatedAdvectionWeakMassEnvelope E ψ := by
    dsimp only [a₁]
    simpa only [
      h3EndpointDifferentiatedAdvectionWeakMassEnvelope
    ] using
      integral_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_le_endpointH3
        hNS ht hEnd hE hTail hEndpoint
        ψ q zAxis xAxis

  have ha₂Bound :
      (∫ x : Point3, a₂ x ∂volume)
        ≤
      h3EndpointDifferentiatedAdvectionWeakMassEnvelope E ψ := by
    dsimp only [a₂]
    simpa only [
      h3EndpointDifferentiatedAdvectionWeakMassEnvelope
    ] using
      integral_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_le_endpointH3
        hNS ht hEnd hE hTail hEndpoint
        ψ q xAxis zAxis

  have hFinal :=
    integral_le_four_integrable_majorants
      hTargetMeas
      (fun x : Point3 =>
        mul_nonneg
          (norm_nonneg (ψ x))
          (norm_nonneg
            (h3LoggedPreterminalVorticityRHSY
              u (t + (q : ℝ)) x)))
      hd₁Int
      hd₂Int
      ha₁Int
      ha₂Int
      hPoint
      hd₁Bound
      hd₂Bound
      ha₁Bound
      ha₂Bound

  simpa only [
    h3EndpointVorticityRHSWeakMassEnvelope
  ] using hFinal

/-- The compact-test-weighted z pressure-free vorticity RHS is integrable on
each closed endpoint slice. -/
theorem integrable_weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSZ_endpoint
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
    (q : Set.Icc (0 : ℝ) tau) :
    Integrable
      (fun x : Point3 =>
        ‖ψ x‖ *
          ‖h3LoggedPreterminalVorticityRHSZ
              u (t + (q : ℝ)) x‖)
      (volume : Measure Point3) := by
  have hs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith [ht.1, q.2.1]
    · linarith [hEnd, q.2.2]

  let d₁ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            xAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component yAxis))
            x‖

  let d₂ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            yAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component xAxis))
            x‖

  let a₁ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            xAxis
            (fun y =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                y
                yAxis)
            x‖

  let a₂ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            yAxis
            (fun y =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                y
                xAxis)
            x‖

  have hyEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) yAxis
        =
      fun y =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component yAxis := by
    rfl

  have hxEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) xAxis
        =
      fun y =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component xAxis := by
    rfl

  have hd₁Int :
      Integrable d₁ (volume : Measure Point3) := by
    have h :=
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_endpoint
        hNS ht hEnd hE hTail
        ψ q xAxis yAxis
    rw [hyEq] at h
    simpa only [d₁] using h

  have hd₂Int :
      Integrable d₂ (volume : Measure Point3) := by
    have h :=
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_endpoint
        hNS ht hEnd hE hTail
        ψ q yAxis xAxis
    rw [hxEq] at h
    simpa only [d₂] using h

  have ha₁Int :
      Integrable a₁ (volume : Measure Point3) := by
    dsimp only [a₁]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_endpoint
        hNS ht hEnd hE hTail hEndpoint
        ψ q xAxis yAxis

  have ha₂Int :
      Integrable a₂ (volume : Measure Point3) := by
    dsimp only [a₂]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_endpoint
        hNS ht hEnd hE hTail hEndpoint
        ψ q yAxis xAxis

  have hExtMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
            hNS (t + (q : ℝ)) x)
        (volume : Measure Point3) :=
    (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
      hNS (t + (q : ℝ))).continuous.aestronglyMeasurable

  have hRHSMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityRHSZ
            u (t + (q : ℝ)) x)
        (volume : Measure Point3) := by
    have hEq :
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityRHSZ
            u (t + (q : ℝ)) x)
          =
        fun x : Point3 =>
          h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
            hNS (t + (q : ℝ)) x := by
      funext x
      exact
        (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension_apply_eq_rhs_of_mem
          hNS hs x).symm
    rw [hEq]
    exact hExtMeas

  have hTargetMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          ‖ψ x‖ *
            ‖h3LoggedPreterminalVorticityRHSZ
                u (t + (q : ℝ)) x‖)
        (volume : Measure Point3) :=
    ψ.continuous.aestronglyMeasurable.norm.mul
      hRHSMeas.norm

  have hPoint :
      ∀ x : Point3,
        ‖ψ x‖ *
            ‖h3LoggedPreterminalVorticityRHSZ
                u (t + (q : ℝ)) x‖
          ≤
        (d₁ x + d₂ x) + (a₁ x + a₂ x) := by
    intro x
    dsimp only [d₁, d₂, a₁, a₂]
    exact
      weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSZ_le_four
        hNS hs ψ x

  exact
    integrable_of_le_four_integrable_majorants
      hTargetMeas
      (fun x : Point3 =>
        mul_nonneg
          (norm_nonneg (ψ x))
          (norm_nonneg
            (h3LoggedPreterminalVorticityRHSZ
              u (t + (q : ℝ)) x)))
      hd₁Int hd₂Int ha₁Int ha₂Int hPoint

/-- Uniform compact-test spatial mass bound for the z pressure-free vorticity
RHS on every closed endpoint slice. -/
theorem integral_weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSZ_le_endpointH3
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
    (q : Set.Icc (0 : ℝ) tau) :
    (∫ x : Point3,
        ‖ψ x‖ *
          ‖h3LoggedPreterminalVorticityRHSZ
              u (t + (q : ℝ)) x‖
      ∂volume)
      ≤
    h3EndpointVorticityRHSWeakMassEnvelope E ψ := by
  have hs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith [ht.1, q.2.1]
    · linarith [hEnd, q.2.2]

  let d₁ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            xAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component yAxis))
            x‖

  let d₂ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            yAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component xAxis))
            x‖

  let a₁ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            xAxis
            (fun y =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                y
                yAxis)
            x‖

  let a₂ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            yAxis
            (fun y =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                y
                xAxis)
            x‖

  have hyEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) yAxis
        =
      fun y =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component yAxis := by
    rfl

  have hxEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) xAxis
        =
      fun y =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component xAxis := by
    rfl

  have hd₁Int :
      Integrable d₁ (volume : Measure Point3) := by
    have h :=
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_endpoint
        hNS ht hEnd hE hTail
        ψ q xAxis yAxis
    rw [hyEq] at h
    simpa only [d₁] using h

  have hd₂Int :
      Integrable d₂ (volume : Measure Point3) := by
    have h :=
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_endpoint
        hNS ht hEnd hE hTail
        ψ q yAxis xAxis
    rw [hxEq] at h
    simpa only [d₂] using h

  have ha₁Int :
      Integrable a₁ (volume : Measure Point3) := by
    dsimp only [a₁]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_endpoint
        hNS ht hEnd hE hTail hEndpoint
        ψ q xAxis yAxis

  have ha₂Int :
      Integrable a₂ (volume : Measure Point3) := by
    dsimp only [a₂]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_endpoint
        hNS ht hEnd hE hTail hEndpoint
        ψ q yAxis xAxis

  have hExtMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
            hNS (t + (q : ℝ)) x)
        (volume : Measure Point3) :=
    (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
      hNS (t + (q : ℝ))).continuous.aestronglyMeasurable

  have hRHSMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityRHSZ
            u (t + (q : ℝ)) x)
        (volume : Measure Point3) := by
    have hEq :
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityRHSZ
            u (t + (q : ℝ)) x)
          =
        fun x : Point3 =>
          h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension
            hNS (t + (q : ℝ)) x := by
      funext x
      exact
        (h3LoggedPreterminalVorticityZTemporalDerivativeContinuousMapExtension_apply_eq_rhs_of_mem
          hNS hs x).symm
    rw [hEq]
    exact hExtMeas

  have hTargetMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          ‖ψ x‖ *
            ‖h3LoggedPreterminalVorticityRHSZ
                u (t + (q : ℝ)) x‖)
        (volume : Measure Point3) :=
    ψ.continuous.aestronglyMeasurable.norm.mul
      hRHSMeas.norm

  have hPoint :
      ∀ x : Point3,
        ‖ψ x‖ *
            ‖h3LoggedPreterminalVorticityRHSZ
                u (t + (q : ℝ)) x‖
          ≤
        (d₁ x + d₂ x) + (a₁ x + a₂ x) := by
    intro x
    dsimp only [d₁, d₂, a₁, a₂]
    exact
      weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSZ_le_four
        hNS hs ψ x

  have hd₁Bound :
      (∫ x : Point3, d₁ x ∂volume)
        ≤
      h3EndpointDifferentiatedDiffusionWeakMassEnvelope E ψ := by
    have h :=
      integral_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_le_endpointH3
        hNS ht hEnd hE hTail
        ψ q xAxis yAxis
    rw [hyEq] at h
    simpa only [
      d₁,
      h3EndpointDifferentiatedDiffusionWeakMassEnvelope
    ] using h

  have hd₂Bound :
      (∫ x : Point3, d₂ x ∂volume)
        ≤
      h3EndpointDifferentiatedDiffusionWeakMassEnvelope E ψ := by
    have h :=
      integral_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_le_endpointH3
        hNS ht hEnd hE hTail
        ψ q yAxis xAxis
    rw [hxEq] at h
    simpa only [
      d₂,
      h3EndpointDifferentiatedDiffusionWeakMassEnvelope
    ] using h

  have ha₁Bound :
      (∫ x : Point3, a₁ x ∂volume)
        ≤
      h3EndpointDifferentiatedAdvectionWeakMassEnvelope E ψ := by
    dsimp only [a₁]
    simpa only [
      h3EndpointDifferentiatedAdvectionWeakMassEnvelope
    ] using
      integral_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_le_endpointH3
        hNS ht hEnd hE hTail hEndpoint
        ψ q xAxis yAxis

  have ha₂Bound :
      (∫ x : Point3, a₂ x ∂volume)
        ≤
      h3EndpointDifferentiatedAdvectionWeakMassEnvelope E ψ := by
    dsimp only [a₂]
    simpa only [
      h3EndpointDifferentiatedAdvectionWeakMassEnvelope
    ] using
      integral_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_le_endpointH3
        hNS ht hEnd hE hTail hEndpoint
        ψ q yAxis xAxis

  have hFinal :=
    integral_le_four_integrable_majorants
      hTargetMeas
      (fun x : Point3 =>
        mul_nonneg
          (norm_nonneg (ψ x))
          (norm_nonneg
            (h3LoggedPreterminalVorticityRHSZ
              u (t + (q : ℝ)) x)))
      hd₁Int
      hd₂Int
      ha₁Int
      ha₂Int
      hPoint
      hd₁Bound
      hd₂Bound
      ha₁Bound
      ha₂Bound

  simpa only [
    h3EndpointVorticityRHSWeakMassEnvelope
  ] using hFinal

end

end Euclidean
end Bridge
end PrimeTensor
