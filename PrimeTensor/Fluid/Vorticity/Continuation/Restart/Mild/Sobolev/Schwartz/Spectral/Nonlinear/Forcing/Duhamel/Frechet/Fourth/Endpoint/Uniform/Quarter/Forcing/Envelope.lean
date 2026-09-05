import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.Uniform.Second.Moment.Envelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.Quarter.Forcing.Mass

/-!
# Uniform positive-time quarter forcing envelope

The selected zeroth and first forcing envelopes depend on time only through
the selected state second-moment envelope.  `UniformSecondMomentEnvelope`
replaces that pointwise state quantity by one explicit constant valid on the
whole positive interval `[a,t]`.

This file substitutes that single interval constant into the already-compiled
forcing algebra.  It produces explicit uniform envelopes for

* selected forcing zeroth mass;
* selected forcing first mass;
* selected forcing quarter mass.

No convolution, derivative, divergence, or Leray estimate is reopened.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzUniformQuarterForcingEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Uniform selected first forcing envelope on `[a,t]`. -/
noncomputable def h3SelectedForcingFirstMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  2 *
    ∑ _k : Fin 3,
      ∑ _j : Fin 3,
        (2 * Real.pi) *
          (2 *
            (h3SelectedMildSecondMomentUniformEnvelope ν A a t *
                h3SelectedRestartRawFourierL1Envelope A +
              h3SelectedRestartRawFourierL1Envelope A *
                h3SelectedMildSecondMomentUniformEnvelope ν A a t))

/-- Uniform selected zeroth forcing envelope on `[a,t]`. -/
noncomputable def h3SelectedForcingL1UniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  2 *
    ∑ _k : Fin 3,
      ∑ _j : Fin 3,
        (2 * Real.pi) *
          (h3SelectedRestartRawFourierL1Envelope A *
              h3SelectedRestartRawFourierL1Envelope A
            +
            2 *
              (h3SelectedMildSecondMomentUniformEnvelope ν A a t *
                  h3SelectedRestartRawFourierL1Envelope A +
                h3SelectedRestartRawFourierL1Envelope A *
                  h3SelectedMildSecondMomentUniformEnvelope ν A a t))

/-- Uniform selected quarter forcing envelope on `[a,t]`. -/
noncomputable def h3SelectedForcingQuarterMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  h3SelectedForcingL1UniformEnvelope ν A a t +
    h3SelectedForcingFirstMomentUniformEnvelope ν A a t

/-- The pointwise first forcing envelope is dominated by the interval-uniform
one whenever `r ∈ [a,t]`. -/
theorem h3SelectedForcingFirstMomentEnvelope_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t) :
    h3SelectedForcingFirstMomentEnvelope ν A r
      ≤
    h3SelectedForcingFirstMomentUniformEnvelope ν A a t := by
  have hM2 :=
    h3SelectedMildSecondMomentEnvelope_le_uniform_on
      hν hA ha har hrt

  have hM0 :
      0 ≤ h3SelectedRestartRawFourierL1Envelope A :=
    h3SelectedRestartRawFourierL1Envelope_nonneg hA

  have hLeft :
      h3SelectedMildSecondMomentEnvelope ν A r *
          h3SelectedRestartRawFourierL1Envelope A
        ≤
      h3SelectedMildSecondMomentUniformEnvelope ν A a t *
          h3SelectedRestartRawFourierL1Envelope A :=
    mul_le_mul_of_nonneg_right hM2 hM0

  have hRight :
      h3SelectedRestartRawFourierL1Envelope A *
          h3SelectedMildSecondMomentEnvelope ν A r
        ≤
      h3SelectedRestartRawFourierL1Envelope A *
          h3SelectedMildSecondMomentUniformEnvelope ν A a t :=
    mul_le_mul_of_nonneg_left hM2 hM0

  have hPair :
      h3SelectedMildSecondMomentEnvelope ν A r *
            h3SelectedRestartRawFourierL1Envelope A +
          h3SelectedRestartRawFourierL1Envelope A *
            h3SelectedMildSecondMomentEnvelope ν A r
        ≤
      h3SelectedMildSecondMomentUniformEnvelope ν A a t *
            h3SelectedRestartRawFourierL1Envelope A +
          h3SelectedRestartRawFourierL1Envelope A *
            h3SelectedMildSecondMomentUniformEnvelope ν A a t :=
    add_le_add hLeft hRight

  have hTwo :
      2 *
          (h3SelectedMildSecondMomentEnvelope ν A r *
              h3SelectedRestartRawFourierL1Envelope A +
            h3SelectedRestartRawFourierL1Envelope A *
              h3SelectedMildSecondMomentEnvelope ν A r)
        ≤
      2 *
          (h3SelectedMildSecondMomentUniformEnvelope ν A a t *
              h3SelectedRestartRawFourierL1Envelope A +
            h3SelectedRestartRawFourierL1Envelope A *
              h3SelectedMildSecondMomentUniformEnvelope ν A a t) :=
    mul_le_mul_of_nonneg_left hPair (by norm_num)

  have hTerm :
      ∀ k j : Fin 3,
        (2 * Real.pi) *
            (2 *
              (h3SelectedMildSecondMomentEnvelope ν A r *
                  h3SelectedRestartRawFourierL1Envelope A +
                h3SelectedRestartRawFourierL1Envelope A *
                  h3SelectedMildSecondMomentEnvelope ν A r))
          ≤
        (2 * Real.pi) *
            (2 *
              (h3SelectedMildSecondMomentUniformEnvelope ν A a t *
                  h3SelectedRestartRawFourierL1Envelope A +
                h3SelectedRestartRawFourierL1Envelope A *
                  h3SelectedMildSecondMomentUniformEnvelope ν A a t)) := by
    intro _k _j
    exact
      mul_le_mul_of_nonneg_left hTwo (by positivity)

  have hSum :
      (∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (2 *
                (h3SelectedMildSecondMomentEnvelope ν A r *
                    h3SelectedRestartRawFourierL1Envelope A +
                  h3SelectedRestartRawFourierL1Envelope A *
                    h3SelectedMildSecondMomentEnvelope ν A r)))
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (2 *
              (h3SelectedMildSecondMomentUniformEnvelope ν A a t *
                  h3SelectedRestartRawFourierL1Envelope A +
                h3SelectedRestartRawFourierL1Envelope A *
                  h3SelectedMildSecondMomentUniformEnvelope ν A a t)) := by
    exact
      Finset.sum_le_sum fun k _ =>
        Finset.sum_le_sum fun j _ =>
          hTerm k j

  unfold
    h3SelectedForcingFirstMomentEnvelope
    h3SelectedForcingFirstMomentUniformEnvelope

  exact
    mul_le_mul_of_nonneg_left hSum (by norm_num)

/-- The pointwise zeroth forcing envelope is dominated by the interval-uniform
one whenever `r ∈ [a,t]`. -/
theorem h3SelectedForcingL1Envelope_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t) :
    h3SelectedForcingL1Envelope ν A r
      ≤
    h3SelectedForcingL1UniformEnvelope ν A a t := by
  have hM2 :=
    h3SelectedMildSecondMomentEnvelope_le_uniform_on
      hν hA ha har hrt

  have hM0 :
      0 ≤ h3SelectedRestartRawFourierL1Envelope A :=
    h3SelectedRestartRawFourierL1Envelope_nonneg hA

  have hLeft :
      h3SelectedMildSecondMomentEnvelope ν A r *
          h3SelectedRestartRawFourierL1Envelope A
        ≤
      h3SelectedMildSecondMomentUniformEnvelope ν A a t *
          h3SelectedRestartRawFourierL1Envelope A :=
    mul_le_mul_of_nonneg_right hM2 hM0

  have hRight :
      h3SelectedRestartRawFourierL1Envelope A *
          h3SelectedMildSecondMomentEnvelope ν A r
        ≤
      h3SelectedRestartRawFourierL1Envelope A *
          h3SelectedMildSecondMomentUniformEnvelope ν A a t :=
    mul_le_mul_of_nonneg_left hM2 hM0

  have hPair :
      h3SelectedMildSecondMomentEnvelope ν A r *
            h3SelectedRestartRawFourierL1Envelope A +
          h3SelectedRestartRawFourierL1Envelope A *
            h3SelectedMildSecondMomentEnvelope ν A r
        ≤
      h3SelectedMildSecondMomentUniformEnvelope ν A a t *
            h3SelectedRestartRawFourierL1Envelope A +
          h3SelectedRestartRawFourierL1Envelope A *
            h3SelectedMildSecondMomentUniformEnvelope ν A a t :=
    add_le_add hLeft hRight

  have hTwo :
      2 *
          (h3SelectedMildSecondMomentEnvelope ν A r *
              h3SelectedRestartRawFourierL1Envelope A +
            h3SelectedRestartRawFourierL1Envelope A *
              h3SelectedMildSecondMomentEnvelope ν A r)
        ≤
      2 *
          (h3SelectedMildSecondMomentUniformEnvelope ν A a t *
              h3SelectedRestartRawFourierL1Envelope A +
            h3SelectedRestartRawFourierL1Envelope A *
              h3SelectedMildSecondMomentUniformEnvelope ν A a t) :=
    mul_le_mul_of_nonneg_left hPair (by norm_num)

  have hInside :
      h3SelectedRestartRawFourierL1Envelope A *
            h3SelectedRestartRawFourierL1Envelope A +
          2 *
            (h3SelectedMildSecondMomentEnvelope ν A r *
                h3SelectedRestartRawFourierL1Envelope A +
              h3SelectedRestartRawFourierL1Envelope A *
                h3SelectedMildSecondMomentEnvelope ν A r)
        ≤
      h3SelectedRestartRawFourierL1Envelope A *
            h3SelectedRestartRawFourierL1Envelope A +
          2 *
            (h3SelectedMildSecondMomentUniformEnvelope ν A a t *
                h3SelectedRestartRawFourierL1Envelope A +
              h3SelectedRestartRawFourierL1Envelope A *
                h3SelectedMildSecondMomentUniformEnvelope ν A a t) :=
    add_le_add (le_refl _) hTwo

  have hTerm :
      ∀ k j : Fin 3,
        (2 * Real.pi) *
            (h3SelectedRestartRawFourierL1Envelope A *
                h3SelectedRestartRawFourierL1Envelope A +
              2 *
                (h3SelectedMildSecondMomentEnvelope ν A r *
                    h3SelectedRestartRawFourierL1Envelope A +
                  h3SelectedRestartRawFourierL1Envelope A *
                    h3SelectedMildSecondMomentEnvelope ν A r))
          ≤
        (2 * Real.pi) *
            (h3SelectedRestartRawFourierL1Envelope A *
                h3SelectedRestartRawFourierL1Envelope A +
              2 *
                (h3SelectedMildSecondMomentUniformEnvelope ν A a t *
                    h3SelectedRestartRawFourierL1Envelope A +
                  h3SelectedRestartRawFourierL1Envelope A *
                    h3SelectedMildSecondMomentUniformEnvelope ν A a t)) := by
    intro _k _j
    exact
      mul_le_mul_of_nonneg_left hInside (by positivity)

  have hSum :
      (∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (h3SelectedRestartRawFourierL1Envelope A *
                  h3SelectedRestartRawFourierL1Envelope A +
                2 *
                  (h3SelectedMildSecondMomentEnvelope ν A r *
                      h3SelectedRestartRawFourierL1Envelope A +
                    h3SelectedRestartRawFourierL1Envelope A *
                      h3SelectedMildSecondMomentEnvelope ν A r)))
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3SelectedRestartRawFourierL1Envelope A *
                h3SelectedRestartRawFourierL1Envelope A +
              2 *
                (h3SelectedMildSecondMomentUniformEnvelope ν A a t *
                    h3SelectedRestartRawFourierL1Envelope A +
                  h3SelectedRestartRawFourierL1Envelope A *
                    h3SelectedMildSecondMomentUniformEnvelope ν A a t)) := by
    exact
      Finset.sum_le_sum fun k _ =>
        Finset.sum_le_sum fun j _ =>
          hTerm k j

  unfold
    h3SelectedForcingL1Envelope
    h3SelectedForcingL1UniformEnvelope

  exact
    mul_le_mul_of_nonneg_left hSum (by norm_num)

/-- The pointwise selected quarter forcing envelope is dominated by the one
interval-uniform quarter envelope. -/
theorem h3SelectedForcingQuarterMomentEnvelope_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t) :
    h3SelectedForcingQuarterMomentEnvelope ν A r
      ≤
    h3SelectedForcingQuarterMomentUniformEnvelope ν A a t := by
  unfold
    h3SelectedForcingQuarterMomentEnvelope
    h3SelectedForcingQuarterMomentUniformEnvelope

  exact
    add_le_add
      (h3SelectedForcingL1Envelope_le_uniform_on
        hν hA ha har hrt)
      (h3SelectedForcingFirstMomentEnvelope_le_uniform_on
        hν hA ha har hrt)

/-- Every selected forcing coordinate has quarter raw Fourier mass bounded by
one explicit constant throughout `[a,t]`. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_quarterMass_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3RawFinLerayOuterProductDivergenceQuarterMass
        (W r) (W r) i
      ≤
    h3SelectedForcingQuarterMomentUniformEnvelope ν A a t := by
  dsimp only

  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have hrR :
      r ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hrt htR

  have hPoint :=
    h3RawFinLerayOuterProductDivergence_selectedRestart_quarterMass_le
      hν U₀ hA hU₀ hr hrR i

  exact
    le_trans hPoint
      (h3SelectedForcingQuarterMomentEnvelope_le_uniform_on
        hν hA.le ha har hrt)

end
end Euclidean
end Bridge
end PrimeTensor
