import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.FourierL2HeatGeneratorQuotientState
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Physical L² temporal admissibility: strong heat-generator convergence

The previous file packages the positive heat difference quotient directly in
raw Fourier `L²` and identifies both that quotient and its target generator by
exact a.e. representatives.

This file performs the quotient-safe dominated-convergence step.  For one
weighted H³ scalar state `G`, the pointwise residual

    Q_h(ξ) - A(ξ)

tends to zero from the right and is dominated by twice the zero-time generator.
Squaring gives an integrable `L¹` majorant because the packaged generator is
itself in `L²`.

Consequently the actual raw Fourier `L²` quotient converges strongly from the
right to `ν Δ̂_L² G`.  This is the analytic core of the forthcoming
right-derivative theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2HeatGeneratorConvergence
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Squared pointwise residual between the raw heat quotient and its zero-time
generator. -/
noncomputable def h3RawFourierL2HeatGeneratorResidualSq
    (ν h : ℝ)
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ‖h3RawFourierL2HeatQuotientRawAmplitude ν h G ξ
      -
    h3RawFourierL2HeatGeneratorRawAmplitude ν G ξ‖ ^ 2

/-- The squared residual is a.e. strongly measurable for every increment. -/
theorem h3RawFourierL2HeatGeneratorResidualSq_aestronglyMeasurable
    (ν h : ℝ)
    (G : H3SpectralScalarState) :
    AEStronglyMeasurable
      (h3RawFourierL2HeatGeneratorResidualSq ν h G)
      (volume : Measure H3FourierPoint3) := by
  have hRawMeas :
      AEStronglyMeasurable
        (h3SpectralScalarRawFourier G)
        (volume : Measure H3FourierPoint3) :=
    (h3SpectralScalarRawFourier_memLp2 G).1

  have hSymbolMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3HeatFourierSymbol ν h ξ)
        (volume : Measure H3FourierPoint3) :=
    (continuous_h3HeatFourierSymbol ν h).aestronglyMeasurable

  have hQMeas :
      AEStronglyMeasurable
        (h3RawFourierL2HeatQuotientRawAmplitude
          ν h G)
        (volume : Measure H3FourierPoint3) := by
    unfold h3RawFourierL2HeatQuotientRawAmplitude
    exact
      AEStronglyMeasurable.const_smul
        ((hSymbolMeas.mul hRawMeas).sub hRawMeas)
        h⁻¹

  have hGeneratorMeas :
      AEStronglyMeasurable
        (h3RawFourierL2HeatGeneratorRawAmplitude
          ν G)
        (volume : Measure H3FourierPoint3) := by
    have hStateMeas :
        AEStronglyMeasurable
          (((h3RawFourierL2HeatGeneratorState
              ν G :
            H3FourierComplexL2) :
            H3FourierPoint3 → ℂ))
          (volume : Measure H3FourierPoint3) :=
      (MeasureTheory.Lp.memLp
        (h3RawFourierL2HeatGeneratorState ν G)).1

    exact
      hStateMeas.congr
        (h3RawFourierL2HeatGeneratorState_ae
          ν G)

  unfold h3RawFourierL2HeatGeneratorResidualSq
  exact
    AEStronglyMeasurable.pow
      (hQMeas.sub hGeneratorMeas).norm
      2

/-- Frequencywise, the squared quotient residual tends to zero from the
right. -/
theorem tendsto_h3RawFourierL2HeatGeneratorResidualSq_zero_right
    (ν : ℝ)
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    Tendsto
      (fun h : ℝ =>
        h3RawFourierL2HeatGeneratorResidualSq
          ν h G ξ)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝 0) := by
  have hQ :=
    tendsto_h3RawFourierL2HeatQuotientRawAmplitude_zero_right
      ν G ξ

  have hDiff :
      Tendsto
        (fun h : ℝ =>
          h3RawFourierL2HeatQuotientRawAmplitude
              ν h G ξ
            -
          h3RawFourierL2HeatGeneratorRawAmplitude
            ν G ξ)
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 0) := by
    simpa using
      hQ.sub_const
        (h3RawFourierL2HeatGeneratorRawAmplitude
          ν G ξ)

  have hNorm :
      Tendsto
        (fun h : ℝ =>
          ‖h3RawFourierL2HeatQuotientRawAmplitude
              ν h G ξ
            -
          h3RawFourierL2HeatGeneratorRawAmplitude
            ν G ξ‖)
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 0) := by
    simpa using hDiff.norm

  have hSq := hNorm.pow 2

  have hZeroSq :
      (0 : ℝ) ^ 2 = 0 := by
    norm_num

  rw [hZeroSq] at hSq

  simpa only [
    h3RawFourierL2HeatGeneratorResidualSq
  ] using hSq

/-- A positive heat quotient residual is bounded by four times the squared
generator density. -/
theorem h3RawFourierL2HeatGeneratorResidualSq_le_four_generator
    {ν h : ℝ}
    (hν : 0 ≤ ν)
    (hh : 0 < h)
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3RawFourierL2HeatGeneratorResidualSq
        ν h G ξ
      ≤
    4 *
      ‖h3RawFourierL2HeatGeneratorRawAmplitude
        ν G ξ‖ ^ 2 := by
  have hQ :=
    norm_h3RawFourierL2HeatQuotientRawAmplitude_le_generator
      hν hh G ξ

  have hTwo :
      ‖h3RawFourierL2HeatQuotientRawAmplitude
            ν h G ξ
          -
        h3RawFourierL2HeatGeneratorRawAmplitude
          ν G ξ‖
        ≤
      2 *
        ‖h3RawFourierL2HeatGeneratorRawAmplitude
          ν G ξ‖ := by
    calc
      ‖h3RawFourierL2HeatQuotientRawAmplitude
            ν h G ξ
          -
        h3RawFourierL2HeatGeneratorRawAmplitude
          ν G ξ‖
          ≤
        ‖h3RawFourierL2HeatQuotientRawAmplitude
            ν h G ξ‖
          +
        ‖h3RawFourierL2HeatGeneratorRawAmplitude
          ν G ξ‖ :=
            norm_sub_le _ _
      _ ≤
        ‖h3RawFourierL2HeatGeneratorRawAmplitude
            ν G ξ‖
          +
        ‖h3RawFourierL2HeatGeneratorRawAmplitude
            ν G ξ‖ := by
              exact
                add_le_add hQ (le_refl _)
      _ =
        2 *
          ‖h3RawFourierL2HeatGeneratorRawAmplitude
            ν G ξ‖ := by
              ring

  have hSq :
      ‖h3RawFourierL2HeatQuotientRawAmplitude
            ν h G ξ
          -
        h3RawFourierL2HeatGeneratorRawAmplitude
          ν G ξ‖ ^ 2
        ≤
      (2 *
        ‖h3RawFourierL2HeatGeneratorRawAmplitude
          ν G ξ‖) ^ 2 := by
    exact
      (sq_le_sq₀
        (norm_nonneg _)
        (mul_nonneg (by norm_num) (norm_nonneg _))).2
        hTwo

  unfold h3RawFourierL2HeatGeneratorResidualSq

  calc
    ‖h3RawFourierL2HeatQuotientRawAmplitude
          ν h G ξ
        -
      h3RawFourierL2HeatGeneratorRawAmplitude
        ν G ξ‖ ^ 2
        ≤
      (2 *
        ‖h3RawFourierL2HeatGeneratorRawAmplitude
          ν G ξ‖) ^ 2 :=
      hSq
    _ =
      4 *
        ‖h3RawFourierL2HeatGeneratorRawAmplitude
          ν G ξ‖ ^ 2 := by
            ring

/-- The squared `L²` distance from the quotient state to its generator is the
integral of the raw squared residual. -/
theorem h3RawFourierL2HeatQuotientState_sub_generator_norm_sq
    {ν h : ℝ}
    (hν : 0 ≤ ν)
    (hh : 0 < h)
    (G : H3SpectralScalarState) :
    ‖h3RawFourierL2HeatQuotientState
          ν h hν G
        -
      h3RawFourierL2HeatGeneratorState
        ν G‖ ^ 2
      =
    ∫ ξ : H3FourierPoint3,
      h3RawFourierL2HeatGeneratorResidualSq
        ν h G ξ := by
  rw [h3FourierComplexL2_norm_sq_eq_integral_norm_sq]

  apply integral_congr_ae

  filter_upwards [
    MeasureTheory.Lp.coeFn_sub
      (h3RawFourierL2HeatQuotientState
        ν h hν G)
      (h3RawFourierL2HeatGeneratorState
        ν G),
    h3RawFourierL2HeatQuotientState_ae_of_pos
      hν hh G,
    h3RawFourierL2HeatGeneratorState_ae
      ν G
  ] with ξ hSubξ hQξ hGeneratorξ

  rw [hSubξ]
  simp only [Pi.sub_apply]
  rw [hQξ, hGeneratorξ]
  rfl

/-- The actual raw Fourier `L²` heat quotient converges strongly from the right
to the quotient-safe generator. -/
theorem tendsto_h3RawFourierL2HeatQuotientState_zero_right
    (ν : ℝ)
    (hν : 0 ≤ ν)
    (G : H3SpectralScalarState) :
    Tendsto
      (fun h : ℝ =>
        h3RawFourierL2HeatQuotientState
          ν h hν G)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3RawFourierL2HeatGeneratorState
          ν G)) := by
  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      4 *
        ‖((h3RawFourierL2HeatGeneratorState
            ν G :
          H3FourierComplexL2) ξ)‖ ^ 2

  have hFMeas :
      ∀ᶠ h : ℝ in (𝓝[Set.Ioi (0 : ℝ)] 0),
        AEStronglyMeasurable
          (h3RawFourierL2HeatGeneratorResidualSq
            ν h G)
          (volume : Measure H3FourierPoint3) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact
      h3RawFourierL2HeatGeneratorResidualSq_aestronglyMeasurable
        ν h G

  have hBound :
      ∀ᶠ h : ℝ in (𝓝[Set.Ioi (0 : ℝ)] 0),
        ∀ᵐ ξ : H3FourierPoint3
            ∂(volume : Measure H3FourierPoint3),
          ‖h3RawFourierL2HeatGeneratorResidualSq
              ν h G ξ‖
            ≤
          bound ξ := by
    filter_upwards [self_mem_nhdsWithin] with h hh

    have hGeneratorAe :=
      h3RawFourierL2HeatGeneratorState_ae
        ν G

    filter_upwards [hGeneratorAe] with ξ hGeneratorξ

    have hRawBound :=
      h3RawFourierL2HeatGeneratorResidualSq_le_four_generator
        hν hh G ξ

    have hResidualNonneg :
        0 ≤
          h3RawFourierL2HeatGeneratorResidualSq
            ν h G ξ := by
      unfold h3RawFourierL2HeatGeneratorResidualSq
      positivity

    dsimp only [bound]

    rw [Real.norm_eq_abs, abs_of_nonneg hResidualNonneg]

    rw [← hGeneratorξ] at hRawBound

    exact hRawBound

  have hBoundIntegrable :
      Integrable
        bound
        (volume : Measure H3FourierPoint3) := by
    have hGeneratorSqIntegrable :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖((h3RawFourierL2HeatGeneratorState
                ν G :
              H3FourierComplexL2) ξ)‖ ^ 2)
          (volume : Measure H3FourierPoint3) :=
      (MeasureTheory.Lp.memLp
        (h3RawFourierL2HeatGeneratorState
          ν G)).integrable_norm_pow
        (by norm_num)

    dsimp only [bound]

    exact
      Integrable.const_mul
        hGeneratorSqIntegrable
        4

  have hPointwise :
      ∀ᵐ ξ : H3FourierPoint3
          ∂(volume : Measure H3FourierPoint3),
        Tendsto
          (fun h : ℝ =>
            h3RawFourierL2HeatGeneratorResidualSq
              ν h G ξ)
          (𝓝[Set.Ioi (0 : ℝ)] 0)
          (𝓝 0) := by
    filter_upwards with ξ
    exact
      tendsto_h3RawFourierL2HeatGeneratorResidualSq_zero_right
        ν G ξ

  have hIntegral :
      Tendsto
        (fun h : ℝ =>
          ∫ ξ : H3FourierPoint3,
            h3RawFourierL2HeatGeneratorResidualSq
              ν h G ξ)
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 0) := by
    simpa using
      (MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (μ := (volume : Measure H3FourierPoint3))
        (l := (𝓝[Set.Ioi (0 : ℝ)] 0))
        (F := fun h : ℝ =>
          h3RawFourierL2HeatGeneratorResidualSq
            ν h G)
        (f := fun _ : H3FourierPoint3 => (0 : ℝ))
        (bound := bound)
        hFMeas
        hBound
        hBoundIntegrable
        hPointwise)

  have hNormSqEq :
      ∀ᶠ h : ℝ in (𝓝[Set.Ioi (0 : ℝ)] 0),
        ‖h3RawFourierL2HeatQuotientState
              ν h hν G
            -
          h3RawFourierL2HeatGeneratorState
            ν G‖ ^ 2
          =
        ∫ ξ : H3FourierPoint3,
          h3RawFourierL2HeatGeneratorResidualSq
            ν h G ξ := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact
      h3RawFourierL2HeatQuotientState_sub_generator_norm_sq
        hν hh G

  have hNormSq :
      Tendsto
        (fun h : ℝ =>
          ‖h3RawFourierL2HeatQuotientState
                ν h hν G
              -
            h3RawFourierL2HeatGeneratorState
              ν G‖ ^ 2)
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝 0) := by
    exact
      Tendsto.congr'
        (Filter.EventuallyEq.symm hNormSqEq)
        hIntegral

  have hSqrt :=
    (Real.continuous_sqrt.tendsto 0).comp
      hNormSq

  change
    Tendsto
      (fun h : ℝ =>
        Real.sqrt
          (‖h3RawFourierL2HeatQuotientState
                ν h hν G
              -
            h3RawFourierL2HeatGeneratorState
              ν G‖ ^ 2))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝 (Real.sqrt 0)) at hSqrt

  apply tendsto_iff_norm_sub_tendsto_zero.2

  simpa only [
    Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_zero
  ] using hSqrt

end

end Euclidean
end Bridge
end PrimeTensor
