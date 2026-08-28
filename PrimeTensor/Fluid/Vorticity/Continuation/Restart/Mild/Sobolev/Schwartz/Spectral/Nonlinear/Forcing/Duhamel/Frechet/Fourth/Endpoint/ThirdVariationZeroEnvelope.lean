import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdVariationStateEnvelope

/-!
# Closing the unweighted state envelope in the full-third variation argument

`ThirdVariationStateEnvelope` reduces the full-third variation Fubini step to
uniform positive-time envelopes for two coordinatewise raw Fourier masses:

    m₀(W(r)_k),
    m₉/₄(W(r)_k).

The zeroth moment is already controlled quantitatively by the H³ solver norm.
Indeed deweighting is multiplication by the reciprocal exact H³ weight
`W₃⁻¹`, which belongs to `L²`.  Hölder therefore gives

    m₀(G) ≤ C_dw ‖G‖,

where `C_dw` is the fixed `L²` norm of the reciprocal weight.

The selected restart path is globally bounded in the spectral H³ state by
`2 A`, and each coordinate norm is bounded by the velocity-state sup norm.
Thus

    m₀(W(r)_k) ≤ C_dw (2 A)

uniformly for every real time `r`.

This file packages that estimate and feeds it into the state-envelope Fubini
criterion.  Above this checkpoint, the only remaining numerical hypothesis is
a uniform positive-time `9/4` raw Fourier mass envelope.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzThirdVariationZeroEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Fixed Hölder/deweighting coefficient: the real `L²` size of the reciprocal
H³ spectral weight, written in its explicit integral form. -/
noncomputable def h3RawFourierL1DeweightingCoefficient : ℝ :=
  (∫ ξ : H3FourierPoint3,
      ‖h3SobolevFrequencyWeightInvComplex ξ‖ ^ (2 : ℝ))
    ^ ((1 : ℝ) / 2)

/-- The deweighting coefficient is nonnegative. -/
theorem h3RawFourierL1DeweightingCoefficient_nonneg :
    0 ≤ h3RawFourierL1DeweightingCoefficient := by
  unfold h3RawFourierL1DeweightingCoefficient
  exact
    Real.rpow_nonneg
      (integral_nonneg fun ξ => by
        exact Real.rpow_nonneg (norm_nonneg _) _)
      _

/-- For an actual `L²` package, the explicit square-integral Hölder factor is
exactly its norm. -/
theorem h3SpectralScalarState_integral_norm_sq_rpow_half_eq_norm
    (G : H3SpectralScalarState) :
    (∫ ξ : H3FourierPoint3,
        ‖G ξ‖ ^ (2 : ℝ))
      ^ ((1 : ℝ) / 2)
      =
    ‖G‖ := by
  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 => G ξ)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.Lp.aestronglyMeasurable G

  have hLp :
      MeasureTheory.lpNorm
          (fun ξ : H3FourierPoint3 => G ξ)
          (2 : ENNReal)
          (volume : Measure H3FourierPoint3)
        =
      (∫ ξ : H3FourierPoint3,
          ‖G ξ‖ ^ ((2 : ENNReal).toReal))
        ^ ((2 : ENNReal).toReal)⁻¹ :=
    MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
      (p := (2 : ENNReal))
      (by norm_num)
      (by norm_num)
      hMeas

  have hLpNorm :
      MeasureTheory.lpNorm
          (fun ξ : H3FourierPoint3 => G ξ)
          (2 : ENNReal)
          (volume : Measure H3FourierPoint3)
        =
      ‖G‖ := by
    calc
      MeasureTheory.lpNorm
          (fun ξ : H3FourierPoint3 => G ξ)
          (2 : ENNReal)
          (volume : Measure H3FourierPoint3)
          =
        (MeasureTheory.eLpNorm
          (fun ξ : H3FourierPoint3 => G ξ)
          (2 : ENNReal)
          (volume : Measure H3FourierPoint3)).toReal :=
        (MeasureTheory.toReal_eLpNorm hMeas).symm
      _ = ‖G‖ := by
        simpa using (MeasureTheory.Lp.norm_def G).symm

  rw [hLpNorm] at hLp
  norm_num at hLp ⊢
  exact hLp.symm

/-- Quantitative H³ deweighting: raw Fourier `L¹` mass is bounded by a fixed
deweighting coefficient times the weighted spectral `L²` norm. -/
theorem h3SpectralScalarRawFourierL1Mass_le_norm
    (G : H3SpectralScalarState) :
    h3SpectralScalarRawFourierL1Mass G
      ≤
    h3RawFourierL1DeweightingCoefficient * ‖G‖ := by
  have hInv2 :
      MemLp
        h3SobolevFrequencyWeightInvComplex
        (ENNReal.ofReal (2 : ℝ))
        (volume : Measure H3FourierPoint3) := by
    simpa using h3SobolevFrequencyWeightInvComplex_memLp2

  have hG2 :
      MemLp
        (fun ξ : H3FourierPoint3 => G ξ)
        (ENNReal.ofReal (2 : ℝ))
        (volume : Measure H3FourierPoint3) := by
    simpa using (MeasureTheory.Lp.memLp G)

  have hHolder :=
    MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      Real.HolderConjugate.two_two
      hInv2
      hG2

  have hHolder' :
      (∫ ξ : H3FourierPoint3,
          ‖h3SobolevFrequencyWeightInvComplex ξ‖ *
            ‖G ξ‖)
        ≤
      h3RawFourierL1DeweightingCoefficient * ‖G‖ := by
    rw [← h3SpectralScalarState_integral_norm_sq_rpow_half_eq_norm G]
    unfold h3RawFourierL1DeweightingCoefficient
    simpa using hHolder

  unfold h3SpectralScalarRawFourierL1Mass
  unfold h3SpectralScalarRawFourier
  simpa only [norm_mul] using hHolder'

/-- Uniform unweighted raw Fourier envelope supplied by the global selected
restart-path H³ bound. -/
noncomputable def h3SelectedRestartRawFourierL1Envelope
    (A : ℝ) : ℝ :=
  h3RawFourierL1DeweightingCoefficient * (2 * A)

theorem h3SelectedRestartRawFourierL1Envelope_nonneg
    {A : ℝ}
    (hA : 0 ≤ A) :
    0 ≤ h3SelectedRestartRawFourierL1Envelope A := by
  unfold h3SelectedRestartRawFourierL1Envelope
  exact
    mul_nonneg
      h3RawFourierL1DeweightingCoefficient_nonneg
      (mul_nonneg (by norm_num) hA)

/-- Every coordinate of the selected restart path has the same explicit raw
Fourier `L¹` mass bound, uniformly for all real times. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1Mass_le
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (r : ℝ)
    (k : Fin 3) :
    h3SpectralScalarRawFourierL1Mass
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ r k)
      ≤
    h3SelectedRestartRawFourierL1Envelope A := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hScalar :
      h3SpectralScalarRawFourierL1Mass (W r k)
        ≤
      h3RawFourierL1DeweightingCoefficient * ‖W r k‖ :=
    h3SpectralScalarRawFourierL1Mass_le_norm (W r k)

  have hCoord :
      ‖W r k‖ ≤ ‖W r‖ :=
    h3SpectralVelocity_coordinate_norm_le (W r) k

  have hWb :=
    h3SpectralFinHeatLerayMildSolutionPhysicalExtension_continuous_bounded
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀
      hA
      hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)

  have hPath :
      ‖W r‖ ≤ 2 * A := by
    dsimp only [W]
    simpa only [
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
    ] using hWb.2 r

  have hC0 :
      0 ≤ h3RawFourierL1DeweightingCoefficient :=
    h3RawFourierL1DeweightingCoefficient_nonneg

  calc
    h3SpectralScalarRawFourierL1Mass (W r k)
        ≤
      h3RawFourierL1DeweightingCoefficient * ‖W r k‖ :=
      hScalar
    _ ≤
      h3RawFourierL1DeweightingCoefficient * ‖W r‖ :=
      mul_le_mul_of_nonneg_left hCoord hC0
    _ ≤
      h3RawFourierL1DeweightingCoefficient * (2 * A) :=
      mul_le_mul_of_nonneg_left hPath hC0
    _ =
      h3SelectedRestartRawFourierL1Envelope A := by
      rfl

/-- Interval form consumed by the full-third state-envelope criterion. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1Mass_intervalEnvelope
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    ∀ r ∈ Set.Icc a t, ∀ k : Fin 3,
      h3SpectralScalarRawFourierL1Mass
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ r k)
        ≤
      h3SelectedRestartRawFourierL1Envelope A := by
  intro r _hr k
  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1Mass_le
      hν U₀ hA hU₀ r k

/-- The full-third terminal variation Fubini step now needs only a numerical
positive-time `9/4` state envelope; the unweighted envelope is automatic from
the selected restart-ball bound. -/
theorem h3SelectedDuhamelTailThirdVariationComplexKernel_fubini_integrable_of_nineQuarterStateEnvelope
    {ν A a t M9 : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hM9 : 0 ≤ M9)
    (hState9 :
      ∀ r ∈ Set.Icc a t, ∀ k : Fin 3,
        h3SpectralScalarRawFourierNineQuarterMass
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ r k)
          ≤ M9)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailThirdVariationComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
        (volume : Measure H3FourierPoint3)) := by
  apply
    h3SelectedDuhamelTailThirdVariationComplexKernel_fubini_integrable_of_stateEnvelope
      (M0 := h3SelectedRestartRawFourierL1Envelope A)
      (M9 := M9)
      hν U₀ hA hU₀
      ha hat htR
      (h3SelectedRestartRawFourierL1Envelope_nonneg hA.le)
      hM9

  · exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1Mass_intervalEnvelope
        (a := a) (t := t)
        hν U₀ hA hU₀

  · exact hState9

end
end Euclidean
end Bridge
end PrimeTensor
