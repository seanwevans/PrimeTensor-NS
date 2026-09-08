import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.CurlTermIntegrable

/-!
# Compact-test endpoint mass bound for the x-vorticity RHS

The four curl building blocks are now both integrable and quantitatively
bounded.  This file closes the spatial mass estimate for the x-component of
the pressure-free vorticity RHS.

Three common endpoint envelopes are named:

* one differentiated componentwise-Laplacian mass;
* one differentiated advection-component mass;
* the full four-term vorticity RHS mass.

The final envelope is axis-independent, so the y/z components can reuse it
verbatim in the next increment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EndpointCurlVorticityRHSMassX
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3EndpointCurlVorticityRHSMassX :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Common compact-test mass envelope for one differentiated componentwise
Laplacian. -/
noncomputable def h3EndpointDifferentiatedDiffusionWeakMassEnvelope
    (E : ℝ)
    (ψ : H3WeakTestFunction) : ℝ :=
  h3WeakTestFunctionL2Mass ψ *
      (2 * E) ^ (1 / (2 : ℝ))
    +
  (
    h3WeakTestFunctionL2Mass ψ *
        (2 * E) ^ (1 / (2 : ℝ))
      +
    h3WeakTestFunctionL2Mass ψ *
        (2 * E) ^ (1 / (2 : ℝ))
  )

/-- Common compact-test mass envelope for one differentiated advection
component. -/
noncomputable def h3EndpointDifferentiatedAdvectionWeakMassEnvelope
    (E : ℝ)
    (ψ : H3WeakTestFunction) : ℝ :=
  (
    (
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        (2 * E)
    )
      *
    (
      h3WeakTestFunctionL2Mass ψ *
        (2 * E) ^ (1 / (2 : ℝ))
    )
    +
    (
      h3RawFourierL1DeweightingCoefficient *
        (2 * E)
    )
      *
    (
      h3WeakTestFunctionL2Mass ψ *
        (2 * E) ^ (1 / (2 : ℝ))
    )
  )
    +
  (
    (
      (
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          (2 * E)
      )
        *
      (
        h3WeakTestFunctionL2Mass ψ *
          (2 * E) ^ (1 / (2 : ℝ))
      )
      +
      (
        h3RawFourierL1DeweightingCoefficient *
          (2 * E)
      )
        *
      (
        h3WeakTestFunctionL2Mass ψ *
          (2 * E) ^ (1 / (2 : ℝ))
      )
    )
      +
    (
      (
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          (2 * E)
      )
        *
      (
        h3WeakTestFunctionL2Mass ψ *
          (2 * E) ^ (1 / (2 : ℝ))
      )
      +
      (
        h3RawFourierL1DeweightingCoefficient *
          (2 * E)
      )
        *
      (
        h3WeakTestFunctionL2Mass ψ *
          (2 * E) ^ (1 / (2 : ℝ))
      )
    )
  )

/-- Common compact-test mass envelope for any one pressure-free vorticity RHS
component. -/
noncomputable def h3EndpointVorticityRHSWeakMassEnvelope
    (E : ℝ)
    (ψ : H3WeakTestFunction) : ℝ :=
  (
    h3EndpointDifferentiatedDiffusionWeakMassEnvelope E ψ
      +
    h3EndpointDifferentiatedDiffusionWeakMassEnvelope E ψ
  )
    +
  (
    h3EndpointDifferentiatedAdvectionWeakMassEnvelope E ψ
      +
    h3EndpointDifferentiatedAdvectionWeakMassEnvelope E ψ
  )

/-- Generic integration helper for a nonnegative target dominated by four
integrable summands. -/
theorem integral_le_four_integrable_majorants
    {f f₁ f₂ f₃ f₄ : Point3 → ℝ}
    {B₁ B₂ B₃ B₄ : ℝ}
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
        (f₁ x + f₂ x) + (f₃ x + f₄ x))
    (hB₁ :
      (∫ x : Point3, f₁ x ∂volume) ≤ B₁)
    (hB₂ :
      (∫ x : Point3, f₂ x ∂volume) ≤ B₂)
    (hB₃ :
      (∫ x : Point3, f₃ x ∂volume) ≤ B₃)
    (hB₄ :
      (∫ x : Point3, f₄ x ∂volume) ≤ B₄) :
    (∫ x : Point3, f x ∂volume)
      ≤
    (B₁ + B₂) + (B₃ + B₄) := by
  let major : Point3 → ℝ :=
    fun x =>
      (f₁ x + f₂ x) + (f₃ x + f₄ x)

  have hMajorInt :
      Integrable major (volume : Measure Point3) := by
    dsimp only [major]
    exact
      (hf₁Int.add hf₂Int).add
        (hf₃Int.add hf₄Int)

  have hfInt :
      Integrable f (volume : Measure Point3) := by
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

  have hIntegralLe :
      (∫ x : Point3, f x ∂volume)
        ≤
      ∫ x : Point3, major x ∂volume :=
    integral_mono_ae
      hfInt
      hMajorInt
      (Filter.Eventually.of_forall hPoint)

  have hOuter :
      (∫ x : Point3,
          (f₁ x + f₂ x) + (f₃ x + f₄ x)
        ∂volume)
        =
      (∫ x : Point3, f₁ x + f₂ x ∂volume)
        +
      (∫ x : Point3, f₃ x + f₄ x ∂volume) := by
    exact
      integral_add
        (hf₁Int.add hf₂Int)
        (hf₃Int.add hf₄Int)

  have hLeft :
      (∫ x : Point3, f₁ x + f₂ x ∂volume)
        =
      (∫ x : Point3, f₁ x ∂volume)
        +
      (∫ x : Point3, f₂ x ∂volume) := by
    exact integral_add hf₁Int hf₂Int

  have hRight :
      (∫ x : Point3, f₃ x + f₄ x ∂volume)
        =
      (∫ x : Point3, f₃ x ∂volume)
        +
      (∫ x : Point3, f₄ x ∂volume) := by
    exact integral_add hf₃Int hf₄Int

  have hMajorIntegral :
      (∫ x : Point3, major x ∂volume)
        =
      (
        (∫ x : Point3, f₁ x ∂volume)
          +
        (∫ x : Point3, f₂ x ∂volume)
      )
        +
      (
        (∫ x : Point3, f₃ x ∂volume)
          +
        (∫ x : Point3, f₄ x ∂volume)
      ) := by
    dsimp only [major]
    calc
      (∫ x : Point3,
          (f₁ x + f₂ x) + (f₃ x + f₄ x)
        ∂volume)
          =
        (∫ x : Point3, f₁ x + f₂ x ∂volume)
          +
        (∫ x : Point3, f₃ x + f₄ x ∂volume) :=
        hOuter
      _ =
        (
          (∫ x : Point3, f₁ x ∂volume)
            +
          (∫ x : Point3, f₂ x ∂volume)
        )
          +
        (∫ x : Point3, f₃ x + f₄ x ∂volume) := by
        rw [hLeft]
      _ =
        (
          (∫ x : Point3, f₁ x ∂volume)
            +
          (∫ x : Point3, f₂ x ∂volume)
        )
          +
        (
          (∫ x : Point3, f₃ x ∂volume)
            +
          (∫ x : Point3, f₄ x ∂volume)
        ) := by
        rw [hRight]

  rw [hMajorIntegral] at hIntegralLe

  exact
    hIntegralLe.trans
      (by
        gcongr)

/-- The compact-test-weighted x pressure-free vorticity RHS is integrable on
each closed endpoint slice. -/
theorem integrable_weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSX_endpoint
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
          ‖h3LoggedPreterminalVorticityRHSX
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
            yAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component zAxis))
            x‖

  let d₂ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            zAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component yAxis))
            x‖

  let a₁ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            yAxis
            (fun y =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                y
                zAxis)
            x‖

  let a₂ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            zAxis
            (fun y =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                y
                yAxis)
            x‖

  have hzEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) zAxis
        =
      fun y =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component zAxis := by
    rfl

  have hyEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) yAxis
        =
      fun y =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component yAxis := by
    rfl

  have hd₁Int :
      Integrable d₁ (volume : Measure Point3) := by
    have h :=
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_endpoint
        hNS ht hEnd hE hTail
        ψ q yAxis zAxis
    rw [hzEq] at h
    simpa only [d₁] using h

  have hd₂Int :
      Integrable d₂ (volume : Measure Point3) := by
    have h :=
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_endpoint
        hNS ht hEnd hE hTail
        ψ q zAxis yAxis
    rw [hyEq] at h
    simpa only [d₂] using h

  have ha₁Int :
      Integrable a₁ (volume : Measure Point3) := by
    dsimp only [a₁]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_endpoint
        hNS ht hEnd hE hTail hEndpoint
        ψ q yAxis zAxis

  have ha₂Int :
      Integrable a₂ (volume : Measure Point3) := by
    dsimp only [a₂]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_endpoint
        hNS ht hEnd hE hTail hEndpoint
        ψ q zAxis yAxis

  let major : Point3 → ℝ :=
    fun x =>
      (d₁ x + d₂ x) + (a₁ x + a₂ x)

  have hMajorInt :
      Integrable major (volume : Measure Point3) := by
    dsimp only [major]
    exact
      (hd₁Int.add hd₂Int).add
        (ha₁Int.add ha₂Int)

  have hExtMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
            hNS (t + (q : ℝ)) x)
        (volume : Measure Point3) :=
    (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
      hNS (t + (q : ℝ))).continuous.aestronglyMeasurable

  have hRHSMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityRHSX
            u (t + (q : ℝ)) x)
        (volume : Measure Point3) := by
    have hEq :
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityRHSX
            u (t + (q : ℝ)) x)
          =
        fun x : Point3 =>
          h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
            hNS (t + (q : ℝ)) x := by
      funext x
      exact
        (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension_apply_eq_rhs_of_mem
          hNS hs x).symm
    rw [hEq]
    exact hExtMeas

  have hTargetMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          ‖ψ x‖ *
            ‖h3LoggedPreterminalVorticityRHSX
                u (t + (q : ℝ)) x‖)
        (volume : Measure Point3) :=
    ψ.continuous.aestronglyMeasurable.norm.mul
      hRHSMeas.norm

  have hPoint :
      ∀ x : Point3,
        ‖ψ x‖ *
            ‖h3LoggedPreterminalVorticityRHSX
                u (t + (q : ℝ)) x‖
          ≤
        major x := by
    intro x
    dsimp only [major, d₁, d₂, a₁, a₂]
    exact
      weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSX_le_four
        hNS hs ψ x

  have hTargetInt :
      Integrable
        (fun x : Point3 =>
          ‖ψ x‖ *
            ‖h3LoggedPreterminalVorticityRHSX
                u (t + (q : ℝ)) x‖)
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
          (norm_nonneg
            (h3LoggedPreterminalVorticityRHSX
              u (t + (q : ℝ)) x)))
    ]
    exact hPoint x

  exact hTargetInt

/-- Uniform compact-test spatial mass bound for the x pressure-free vorticity
RHS on every closed endpoint slice. -/
theorem integral_weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSX_le_endpointH3
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
          ‖h3LoggedPreterminalVorticityRHSX
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
            yAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component zAxis))
            x‖

  let d₂ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            zAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun y =>
                (logSpaceTimeVectorField
                  u (t + (q : ℝ)) y).component yAxis))
            x‖

  let a₁ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            yAxis
            (fun y =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                y
                zAxis)
            x‖

  let a₂ : Point3 → ℝ :=
    fun x =>
      ‖ψ x‖ *
        ‖spatial3.d
            zAxis
            (fun y =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                y
                yAxis)
            x‖

  have hzEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) zAxis
        =
      fun y =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component zAxis := by
    rfl

  have hyEq :
      loggedVelocityComponent
          u (t + (q : ℝ)) yAxis
        =
      fun y =>
        (logSpaceTimeVectorField
          u (t + (q : ℝ)) y).component yAxis := by
    rfl

  have hd₁Int :
      Integrable d₁ (volume : Measure Point3) := by
    have h :=
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_endpoint
        hNS ht hEnd hE hTail
        ψ q yAxis zAxis
    rw [hzEq] at h
    simpa only [d₁] using h

  have hd₂Int :
      Integrable d₂ (volume : Measure Point3) := by
    have h :=
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_endpoint
        hNS ht hEnd hE hTail
        ψ q zAxis yAxis
    rw [hyEq] at h
    simpa only [d₂] using h

  have ha₁Int :
      Integrable a₁ (volume : Measure Point3) := by
    dsimp only [a₁]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_endpoint
        hNS ht hEnd hE hTail hEndpoint
        ψ q yAxis zAxis

  have ha₂Int :
      Integrable a₂ (volume : Measure Point3) := by
    dsimp only [a₂]
    exact
      integrable_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_realAdvectionComponent_endpoint
        hNS ht hEnd hE hTail hEndpoint
        ψ q zAxis yAxis

  have hExtMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
            hNS (t + (q : ℝ)) x)
        (volume : Measure Point3) :=
    (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
      hNS (t + (q : ℝ))).continuous.aestronglyMeasurable

  have hRHSMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityRHSX
            u (t + (q : ℝ)) x)
        (volume : Measure Point3) := by
    have hEq :
        (fun x : Point3 =>
          h3LoggedPreterminalVorticityRHSX
            u (t + (q : ℝ)) x)
          =
        fun x : Point3 =>
          h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension
            hNS (t + (q : ℝ)) x := by
      funext x
      exact
        (h3LoggedPreterminalVorticityXTemporalDerivativeContinuousMapExtension_apply_eq_rhs_of_mem
          hNS hs x).symm
    rw [hEq]
    exact hExtMeas

  have hTargetMeas :
      AEStronglyMeasurable
        (fun x : Point3 =>
          ‖ψ x‖ *
            ‖h3LoggedPreterminalVorticityRHSX
                u (t + (q : ℝ)) x‖)
        (volume : Measure Point3) :=
    ψ.continuous.aestronglyMeasurable.norm.mul
      hRHSMeas.norm

  have hPoint :
      ∀ x : Point3,
        ‖ψ x‖ *
            ‖h3LoggedPreterminalVorticityRHSX
                u (t + (q : ℝ)) x‖
          ≤
        (d₁ x + d₂ x) + (a₁ x + a₂ x) := by
    intro x
    dsimp only [d₁, d₂, a₁, a₂]
    exact
      weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSX_le_four
        hNS hs ψ x

  have hd₁Bound :
      (∫ x : Point3, d₁ x ∂volume)
        ≤
      h3EndpointDifferentiatedDiffusionWeakMassEnvelope E ψ := by
    have h :=
      integral_weakTestNorm_mul_norm_h3LoggedPreterminal_spatial_d_laplacian_le_endpointH3
        hNS ht hEnd hE hTail
        ψ q yAxis zAxis
    rw [hzEq] at h
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
        ψ q zAxis yAxis
    rw [hyEq] at h
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
        ψ q yAxis zAxis

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
        ψ q zAxis yAxis

  have hFinal :=
    integral_le_four_integrable_majorants
      hTargetMeas
      (fun x : Point3 => by
        exact
          mul_nonneg
            (norm_nonneg (ψ x))
            (norm_nonneg
              (h3LoggedPreterminalVorticityRHSX
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
