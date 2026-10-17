import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzMatchedCubicDerivative244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Second.Velocity.L2.Closure
import Mathlib.Analysis.Fourier.LpSpace

/-!
# The actual second Schwartz derivatives of matched compact weighted H³ states

The compiled cubic-derivative checkpoint identifies all 81 third derivatives
of a real Schwartz inverse spectrum with the canonical physical cubic L² jets.
Here we construct the missing quadratic multiplier as an actual Fourier L²
state from the existing quadratic radial H³ estimate. The `2π` normalization
is kept exactly.

For any smooth-compact weighted spectral state F represented by g, its
canonical deweighted complex Schwartz packet S has raw Fourier L² amplitude
exactly h3SpectralScalarRawFourierL2 F. The same real Schwartz inverse ψ
then has BOTH quadratic and cubic derivatives exactly equal to the respective
physical L² multiplier packages. No unmatched approximation sequence occurs.

Only the second-order comparison is new here; the final E₂/E₃ convergence
and physical solenoidal approximation are later obligations.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology FourierTransform
open scoped ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeMatchedSecondDerivative244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every quadratic Fourier coordinate multiplier belongs to genuine L²,
using the existing H³ radial quadratic baseline and no Sobolev upgrade. -/
theorem h3SpectralScalarRawSecondCoordinate_memLp2_244
    (a b : A3) (F : H3SpectralScalarState) :
    MemLp
      (fun ξ : V3 =>
        h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis a) ξ *
          (h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis b) ξ *
            h3SpectralScalarRawFourier F ξ))
      2 (volume : Measure V3) := by
  have hMeas :
      AEStronglyMeasurable
        (fun ξ : V3 =>
          h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis a) ξ *
            (h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis b) ξ *
              h3SpectralScalarRawFourier F ξ))
        (volume : Measure V3) := by
    exact
      (h3FourierDerivativeSymbol_continuous
        (h3ClassicalizationFinOfAxis a)).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous
          (h3ClassicalizationFinOfAxis b)).aestronglyMeasurable.mul
          (h3SpectralScalarRawFourier_memLp2 F).1)
  have hRadial :
      MemLp
        (fun ξ : V3 => ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
          h3SpectralScalarRawFourier F ξ)
        2 (volume : Measure V3) :=
    h3SpectralScalarRawFourier_quadraticWeight_memLp2 F
  refine hRadial.of_le_mul (c := (2 * Real.pi) ^ 2) hMeas ?_
  filter_upwards with ξ
  rw [norm_mul, norm_mul]
  have ha := norm_h3FourierDerivativeSymbol_le_gradientMagnitude
    (h3ClassicalizationFinOfAxis a) ξ
  have hb := norm_h3FourierDerivativeSymbol_le_gradientMagnitude
    (h3ClassicalizationFinOfAxis b) ξ
  have hGrad : 0 ≤ h3FourierGradientMagnitude ξ := by
    unfold h3FourierGradientMagnitude
    positivity
  calc
    ‖h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis a) ξ‖ *
      (‖h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis b) ξ‖ *
        ‖h3SpectralScalarRawFourier F ξ‖)
        ≤ h3FourierGradientMagnitude ξ *
            (‖h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis b) ξ‖ *
              ‖h3SpectralScalarRawFourier F ξ‖) := by
          exact mul_le_mul_of_nonneg_right ha
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            ‖h3SpectralScalarRawFourier F ξ‖) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) hGrad
    _ = (2 * Real.pi) ^ 2 *
          ‖((‖ξ‖ ^ 2 : ℝ) : ℂ) *
            h3SpectralScalarRawFourier F ξ‖ := by
          unfold h3FourierGradientMagnitude
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          rw [abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 2)]
          ring

/-- The second coordinate multiplier as a quotient-safe Fourier L² object. -/
noncomputable def h3SpectralScalarRawSecondCoordinateFourierL2_244
    (a b : A3) (F : H3SpectralScalarState) : H3FourierComplexL2 :=
  (h3SpectralScalarRawSecondCoordinate_memLp2_244 a b F).toLp
    (fun ξ : V3 =>
      h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis a) ξ *
        (h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis b) ξ *
          h3SpectralScalarRawFourier F ξ))

/-- Concrete a.e. multiplier representative of the quadratic Fourier state. -/
theorem h3SpectralScalarRawSecondCoordinateFourierL2_ae244
    (a b : A3) (F : H3SpectralScalarState) :
    (h3SpectralScalarRawSecondCoordinateFourierL2_244 a b F :
      V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 =>
        h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis a) ξ *
          (h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis b) ξ *
            h3SpectralScalarRawFourier F ξ)) :=
  MemLp.coeFn_toLp (h3SpectralScalarRawSecondCoordinate_memLp2_244 a b F)

/-- Canonical real physical second-order reconstruction of a weighted state. -/
noncomputable def h3SpectralScalarRawSecondCoordinatePhysicalL2_244
    (a b : A3) (F : H3SpectralScalarState) : H3ScalarL2 :=
  h3FromFourierRealL2
    (h3RealPartFourierL2
      ((MeasureTheory.Lp.fourierTransformₗᵢ V3 ℂ).symm
        (h3SpectralScalarRawSecondCoordinateFourierL2_244 a b F)))

/-- The second multiplier of a spectrum S is exactly the Fourier transform
of the literal second Schwartz derivative of its inverse. -/
theorem h3Schwartz_fourier_secondOfInverse_apply244
    (S : SchwartzMap V3 ℂ) (a b : A3) (ξ : V3) :
    𝓕 (∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b} (𝓕⁻ S))) ξ =
    h3FourierDerivativeSymbol2
      (h3ClassicalizationFinOfAxis a)
      (h3ClassicalizationFinOfAxis b) ξ * S ξ := by
  rw [h3Schwartz_fourier_secondDerivative_apply244,
    FourierTransform.fourier_fourierInv_eq]

/-- Exact Fourier L² equality: a weighted state's quadratic multiplier is
the Fourier transform of the second derivative of the SAME inverse packet. -/
theorem h3SpectralScalarRawSecondCoordinateFourierL2_schwartzDerivative244
    (F : H3SpectralScalarState) (S : SchwartzMap V3 ℂ)
    (hRaw : h3SpectralScalarRawFourierL2 F =
      S.toLp 2 (volume : Measure V3)) (a b : A3) :
    h3SpectralScalarRawSecondCoordinateFourierL2_244 a b F =
      (𝓕 (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b} (𝓕⁻ S)))).toLp
          2 (volume : Measure V3) := by
  have hRawAE :
      h3SpectralScalarRawFourier F =ᵐ[volume]
        (S : V3 → ℂ) := by
    have h := h3SpectralScalarRawFourierL2_ae F
    rw [hRaw] at h
    exact h.symm.trans (S.coeFn_toLp 2 (volume : Measure V3))
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarRawSecondCoordinateFourierL2_ae244 a b F,
    hRawAE,
    (𝓕 (∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b} (𝓕⁻ S)))).coeFn_toLp
        2 (volume : Measure V3)
  ] with ξ hSecond hRawAt hDerivative
  rw [hSecond, hDerivative, hRawAt]
  rw [h3Schwartz_fourier_secondOfInverse_apply244]
  unfold h3FourierDerivativeSymbol2
  ring

/-- The quadratic physical reconstruction equals the L² class of the
LITERAL second real Schwartz derivative, with no jet-matching premise. -/
theorem h3SpectralScalarRawSecondCoordinatePhysicalL2_realSchwartzDerivative244
    (F : H3SpectralScalarState) (S : SchwartzMap V3 ℂ)
    (hRaw : h3SpectralScalarRawFourierL2 F =
      S.toLp 2 (volume : Measure V3)) (a b : A3) :
    h3SpectralScalarRawSecondCoordinatePhysicalL2_244 a b F =
      h3FromFourierRealL2
        ((∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b}
            (h3RawSchwartzPhysicalRealInverse244 S))).toLp
              2 (volume : Measure V3)) := by
  let D : SchwartzMap V3 ℂ :=
    ∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b} (𝓕⁻ S))
  have hFourier :
      h3SpectralScalarRawSecondCoordinateFourierL2_244 a b F =
        (𝓕 D).toLp 2 (volume : Measure V3) :=
    h3SpectralScalarRawSecondCoordinateFourierL2_schwartzDerivative244
      F S hRaw a b
  have hInv :
      (MeasureTheory.Lp.fourierTransformₗᵢ V3 ℂ).symm
        ((𝓕 D).toLp 2 (volume : Measure V3)) =
          D.toLp 2 (volume : Measure V3) := by
    change 𝓕⁻ ((𝓕 D).toLp 2 (volume : Measure V3)) =
      D.toLp 2 (volume : Measure V3)
    simpa only [FourierTransform.fourierInv_fourier_eq] using
      (SchwartzMap.toLp_fourierInv_eq (𝓕 D))
  unfold h3SpectralScalarRawSecondCoordinatePhysicalL2_244
  rw [hFourier, hInv]
  rw [h3RealPartFourierL2_schwartz_toLp244 D]
  simp only [h3RawSchwartzPhysicalRealInverse244,
    h3ComplexSchwartzRealPart_secondDerivative244]
  rfl

/-- One and the same compact weighted state and real physical Schwartz map
match the zeroth, all 27 second, and all 81 third-order real L² jets. -/
theorem exists_h3SmoothCompactWeighted_realSchwartzExactSecondThird244
    (G : H3SpectralScalarState) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : H3SpectralScalarState,
    ∃ ψ : SchwartzMap V3 ℝ,
      ‖G - F‖ < ε ∧
      h3SpectralScalarDecodeRealL2 F =
        ψ.toLp 2 (volume : Measure V3) ∧
      (∀ a b : A3,
        h3SpectralScalarRawSecondCoordinatePhysicalL2_244 a b F =
          h3FromFourierRealL2
            ((∂_{h3FourierAxisDirection a}
              (∂_{h3FourierAxisDirection b} ψ)).toLp
                2 (volume : Measure V3))) ∧
      (∀ a b c : A3,
        h3SpectralScalarRawThirdCoordinatePhysicalL2 a b c F =
          h3FromFourierRealL2
            ((∂_{h3FourierAxisDirection a}
              (∂_{h3FourierAxisDirection b}
                (∂_{h3FourierAxisDirection c} ψ))).toLp
                  2 (volume : Measure V3))) := by
  obtain ⟨F, ⟨g, hg, hcompact, hsmooth⟩, hClose⟩ :=
    exists_h3SmoothCompact_spectralApprox_norm G hε
  let S : SchwartzMap V3 ℂ :=
    h3SmoothCompactDeweightedSchwartz g hcompact hsmooth
  let ψ : SchwartzMap V3 ℝ :=
    h3RawSchwartzPhysicalRealInverse244 S
  have hRaw :
      h3SpectralScalarRawFourierL2 F =
        S.toLp 2 (volume : Measure V3) :=
    h3SpectralScalarRawFourierL2_eq_deweightedSchwartz_toLp
      F g hg hcompact hsmooth
  have hDecode :
      h3SpectralScalarDecodeRealL2 F =
        ψ.toLp 2 (volume : Measure V3) := by
    change h3RealPartFourierL2
      ((MeasureTheory.Lp.fourierTransformₗᵢ V3 ℂ).symm
        (h3SpectralScalarRawFourierL2 F)) =
          (h3RawSchwartzPhysicalRealInverse244 S).toLp
            2 (volume : Measure V3)
    rw [hRaw]
    have hInv :
        (MeasureTheory.Lp.fourierTransformₗᵢ V3 ℂ).symm
          (S.toLp 2 (volume : Measure V3)) =
          (𝓕⁻ S).toLp 2 (volume : Measure V3) := by
      change 𝓕⁻ (S.toLp 2 (volume : Measure V3)) =
        (𝓕⁻ S).toLp 2 (volume : Measure V3)
      exact SchwartzMap.toLp_fourierInv_eq S
    rw [hInv]
    exact h3RealPartFourierL2_schwartz_toLp244 (𝓕⁻ S)
  refine ⟨F, ψ, hClose, hDecode, ?_, ?_⟩
  · intro a b
    exact h3SpectralScalarRawSecondCoordinatePhysicalL2_realSchwartzDerivative244
      F S hRaw a b
  · intro a b c
    exact h3SpectralScalarRawThirdCoordinatePhysicalL2_realSchwartzDerivative244
      F S hRaw a b c

end
end PrimeTensor.FirstMonomialTriad
