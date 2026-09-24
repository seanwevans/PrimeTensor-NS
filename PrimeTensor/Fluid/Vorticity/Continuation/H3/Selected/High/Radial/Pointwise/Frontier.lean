import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.High.Radial.Fourier.L2.Frontier

/-!
# Reduce selected radial fourth/fifth Fourier L² to pointwise weighted envelopes

The preceding reduction isolated the remaining diffusion-side analytic target:

    |ξ|⁴ raw(W(q)) ∈ L²,
    |ξ|⁵ raw(W(q)) ∈ L².

The selected positive-time moment induction already gives the corresponding
weighted `L¹` statements at every finite natural order.  Therefore a finite
pointwise bound on the same weighted amplitude is enough:

    g ∈ L¹,  0 ≤ |g| ≤ B
      ==> |g|² ≤ B |g|
      ==> g ∈ L².

This file packages exactly that bridge.  It does not assume that the existing
"L¹ moment envelopes" are pointwise frequency bounds; the new hypothesis is
explicitly a genuine pointwise bound.

After this reduction, the high-diffusion frontier is reduced to obtaining
finite pointwise envelopes for the selected fourth/fifth weighted raw Fourier
amplitudes.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedHighRadialPointwiseFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Generic weighted L¹ + pointwise bound -> weighted L² -/

private theorem memLp_two_radialRawWeight_of_integrable_of_pointwise_bound
    (n : ℕ)
    (H : H3SpectralScalarState)
    (hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ n *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3))
    (B : ℝ)
    (_hB : 0 ≤ B)
    (hBound :
      ∀ ξ : H3FourierPoint3,
        ‖((‖ξ‖ ^ n : ℝ) : ℂ) *
            h3SpectralScalarRawFourier H ξ‖
          ≤ B) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ n : ℝ) : ℂ) *
          h3SpectralScalarRawFourier H ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  let g : H3FourierPoint3 → ℂ :=
    fun ξ =>
      ((‖ξ‖ ^ n : ℝ) : ℂ) *
        h3SpectralScalarRawFourier H ξ

  have hWeightContinuous :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ n : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_norm.pow n)

  have hMeas :
      AEStronglyMeasurable
        g
        (volume : Measure H3FourierPoint3) := by
    dsimp only [g]
    exact
      hWeightContinuous.aestronglyMeasurable.mul
        (h3SpectralScalarRawFourier_memLp2 H).1

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          B *
            (‖ξ‖ ^ n *
              ‖h3SpectralScalarRawFourier H ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul B

  rw [
    memLp_two_iff_integrable_sq_norm
      hMeas
  ]

  have hSqMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖g ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    (hMeas.norm.aemeasurable.pow_const 2).aestronglyMeasurable

  refine hMajor.mono' hSqMeas ?_

  filter_upwards with ξ

  have hWeight0 :
      0 ≤ ‖ξ‖ ^ n :=
    pow_nonneg (norm_nonneg ξ) n

  have hScalar0 :
      0 ≤
        ‖ξ‖ ^ n *
          ‖h3SpectralScalarRawFourier H ξ‖ :=
    mul_nonneg hWeight0 (norm_nonneg _)

  have hNormEq :
      ‖g ξ‖
        =
      ‖ξ‖ ^ n *
        ‖h3SpectralScalarRawFourier H ξ‖ := by
    dsimp only [g]
    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hWeight0
    ]

  have hBound' :
      ‖ξ‖ ^ n *
          ‖h3SpectralScalarRawFourier H ξ‖
        ≤
      B := by
    rw [← hNormEq]
    exact hBound ξ

  have hSqLe :
      (‖ξ‖ ^ n *
          ‖h3SpectralScalarRawFourier H ξ‖) ^ 2
        ≤
      B *
        (‖ξ‖ ^ n *
          ‖h3SpectralScalarRawFourier H ξ‖) := by
    calc
      (‖ξ‖ ^ n *
          ‖h3SpectralScalarRawFourier H ξ‖) ^ 2
          =
        (‖ξ‖ ^ n *
          ‖h3SpectralScalarRawFourier H ξ‖) *
        (‖ξ‖ ^ n *
          ‖h3SpectralScalarRawFourier H ξ‖) := by
            ring
      _ ≤
        B *
          (‖ξ‖ ^ n *
            ‖h3SpectralScalarRawFourier H ξ‖) :=
        mul_le_mul_of_nonneg_right
          hBound'
          hScalar0

  change
    ‖(‖g ξ‖ ^ 2 : ℝ)‖
      ≤
    B *
      (‖ξ‖ ^ n *
        ‖h3SpectralScalarRawFourier H ξ‖)

  rw [
    Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖g ξ‖),
    hNormEq
  ]

  exact hSqLe

/-! ## Genuine pointwise weighted-envelope frontier -/

/--
At every strict positive selected restart time, each coordinate has finite
pointwise fourth- and fifth-radial raw Fourier envelopes.

These are genuine frequencywise bounds, unlike the existing named "moment
envelopes", which bound weighted `L¹` masses.
-/
def H3CanonicalSelectedFourthFifthRadialRawFourierPointwiseEnvelopeOnRestartRadius :
    Prop :=
  ∀
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t₀ : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t₀ T E),
      ∀ q : ℝ,
        q ∈
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius (1 : ℝ) E) →
        let U₀ : H3SpectralVelocityState :=
          h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail
        let hA : 0 < E :=
          lt_of_lt_of_le zero_lt_one hE
        let hU₀ : ‖U₀‖ ≤ E :=
          norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            (one_pos : (0 : ℝ) < 1)
            U₀ hA hU₀
        ∃ B4 B5 : ℝ,
          0 ≤ B4
            ∧
          0 ≤ B5
            ∧
          (
            ∀ (j : Fin 3) (ξ : H3FourierPoint3),
              ‖h3SelectedRawFourierFourthRadialWeight
                  (W q j) ξ‖
                ≤ B4
          )
            ∧
          (
            ∀ (j : Fin 3) (ξ : H3FourierPoint3),
              ‖h3SelectedRawFourierFifthRadialWeight
                  (W q j) ξ‖
                ≤ B5
          )

/-! ## Pointwise weighted envelopes close the radial L² frontier -/

theorem h3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius_of_pointwiseEnvelope
    (hPointwise :
      H3CanonicalSelectedFourthFifthRadialRawFourierPointwiseEnvelopeOnRestartRadius) :
    H3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius := by

  intro E u T t₀ hNS ht₀ hE hTail q hq

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalSelectedDecoderAnchorState
      hNS ht₀ hTail

  let hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalSelectedDecoderAnchorState_le
      hNS ht₀ hE hTail

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀

  obtain ⟨B4, B5, hB4, hB5, h4, h5⟩ :=
    hPointwise E u T t₀ hNS ht₀ hE hTail q hq

  dsimp only at h4 h5 ⊢

  constructor

  · intro j

    have hMoment :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 4 *
              ‖h3SpectralScalarRawFourier
                (W q j) ξ‖)
          (volume : Measure H3FourierPoint3) := by
      dsimp only [W, U₀, hA, hU₀]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
          4
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          hq.1
          hq.2.le
          j

    have hLp :=
      memLp_two_radialRawWeight_of_integrable_of_pointwise_bound
        4
        (W q j)
        hMoment
        B4
        hB4
        (by
          intro ξ
          simpa only [
            h3SelectedRawFourierFourthRadialWeight
          ] using h4 j ξ)

    change
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 4 : ℝ) : ℂ) *
            h3SpectralScalarRawFourier
              (W q j) ξ)
        2
        (volume : Measure H3FourierPoint3)

    exact hLp

  · intro j

    have hMoment :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 5 *
              ‖h3SpectralScalarRawFourier
                (W q j) ξ‖)
          (volume : Measure H3FourierPoint3) := by
      dsimp only [W, U₀, hA, hU₀]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
          5
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalSelectedDecoderAnchorState
            hNS ht₀ hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalSelectedDecoderAnchorState_le
            hNS ht₀ hE hTail)
          hq.1
          hq.2.le
          j

    have hLp :=
      memLp_two_radialRawWeight_of_integrable_of_pointwise_bound
        5
        (W q j)
        hMoment
        B5
        hB5
        (by
          intro ξ
          simpa only [
            h3SelectedRawFourierFifthRadialWeight
          ] using h5 j ξ)

    change
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 5 : ℝ) : ℂ) *
            h3SpectralScalarRawFourier
              (W q j) ξ)
        2
        (volume : Measure H3FourierPoint3)

    exact hLp

/-! ## BKM closure at the pointwise weighted selected Fourier frontier -/

theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_selectedRadialFourthFifthPointwiseEnvelope_of_transportPressure_of_fullScalarEnergy
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hDerivative :
      H3PathEnergyClassProducesOrderEnergyDerivativeIdentities)
    (hPointwise :
      H3CanonicalSelectedFourthFifthRadialRawFourierPointwiseEnvelopeOnRestartRadius)
    (hTP :
      H3PathEnergyClassProducesTransportPressureMemLp2)
    (hFull :
      H3PathEnergyClassProducesFullScalarEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_derivativeIdentities_of_selectedRadialFourthFifthRawFourier_of_transportPressure_of_fullScalarEnergy
      hLow
      hDerivative
      (h3CanonicalSelectedFourthFifthRadialRawFourierMemLp2OnRestartRadius_of_pointwiseEnvelope
        hPointwise)
      hTP
      hFull

end

end Euclidean
end Bridge
end PrimeTensor
