import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Cubic.Difference.Interpolation

/-!
# Classicalization: quartic Fourier difference interpolation

The selected positive-time path has every finite natural Fourier moment.
The cubic continuity layer used the elementary interpolation

    |ξ|³ ≤ R³ + R⁻¹ |ξ|⁴

to turn H³ continuity plus a local fourth-moment envelope into continuity of
the cubic weighted raw-Fourier difference mass.

The order-four step is identical:

    |ξ|⁴ ≤ R⁴ + R⁻¹ |ξ|⁵.

Consequently

    M₄(F - G)
      ≤ R⁴ C_dw ‖F - G‖
        + R⁻¹ (M₅(F) + M₅(G)).

This is the exact topology bridge needed for fourth spatial jet time
continuity.  The generic natural-moment induction already supplies the local
fifth-moment envelope, so no new Navier--Stokes estimate occurs here.

The repeated `n` versus `n+1` structure is intentionally left explicit at this
checkpoint; it is now a clear candidate for later order-generic extraction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationQuarticDifferenceInterpolation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Elementary quartic low/high-frequency inequality. -/
theorem norm_pow_four_le_radius_four_add_inv_mul_five
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 4
      ≤
    R ^ 4 + R⁻¹ * ‖ξ‖ ^ 5 := by
  have hx0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have hR0 : 0 ≤ R := hR.le

  by_cases hxR : ‖ξ‖ ≤ R

  · have hpow :
        ‖ξ‖ ^ 4 ≤ R ^ 4 :=
      pow_le_pow_left₀ hx0 hxR 4

    have htail0 :
        0 ≤ R⁻¹ * ‖ξ‖ ^ 5 := by
      exact
        mul_nonneg
          (inv_nonneg.mpr hR0)
          (pow_nonneg hx0 5)

    exact le_add_of_le_of_nonneg hpow htail0

  · have hRx : R ≤ ‖ξ‖ :=
      le_of_lt (lt_of_not_ge hxR)

    have hx4 : 0 ≤ ‖ξ‖ ^ 4 :=
      pow_nonneg hx0 4

    have hmul :
        R * ‖ξ‖ ^ 4 ≤ ‖ξ‖ * ‖ξ‖ ^ 4 :=
      mul_le_mul_of_nonneg_right hRx hx4

    have hfive :
        ‖ξ‖ ^ 4 ≤ R⁻¹ * ‖ξ‖ ^ 5 := by
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ hR).2
      calc
        ‖ξ‖ ^ 4 * R = R * ‖ξ‖ ^ 4 := by ring
        _ ≤ ‖ξ‖ * ‖ξ‖ ^ 4 := hmul
        _ = ‖ξ‖ ^ 5 := by ring

    exact
      le_add_of_nonneg_of_le
        (pow_nonneg hR0 4)
        hfive

/-- Pointwise quartic difference majorant underlying the interpolation lemma. -/
theorem h3RawFourier_quarticDifference_pointwise_le
    (F G : H3SpectralScalarState)
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 4 *
        ‖h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ‖
      ≤
    R ^ 4 *
        ‖h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ‖
      +
    R⁻¹ *
      (‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier F ξ‖ +
        ‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier G ξ‖) := by
  have hweight :=
    norm_pow_four_le_radius_four_add_inv_mul_five hR ξ

  have hdiff0 :
      0 ≤
        ‖h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ‖ :=
    norm_nonneg _

  have hfirst :
      ‖ξ‖ ^ 4 *
          ‖h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ‖
        ≤
      (R ^ 4 + R⁻¹ * ‖ξ‖ ^ 5) *
          ‖h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ‖ :=
    mul_le_mul_of_nonneg_right hweight hdiff0

  have hsub :
      ‖h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ‖
        ≤
      ‖h3SpectralScalarRawFourier F ξ‖ +
        ‖h3SpectralScalarRawFourier G ξ‖ :=
    norm_sub_le _ _

  have hcoeff0 :
      0 ≤ R⁻¹ * ‖ξ‖ ^ 5 := by
    exact
      mul_nonneg
        (inv_nonneg.mpr hR.le)
        (pow_nonneg (norm_nonneg ξ) 5)

  calc
    ‖ξ‖ ^ 4 *
        ‖h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ‖
        ≤
      (R ^ 4 + R⁻¹ * ‖ξ‖ ^ 5) *
        ‖h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ‖ :=
      hfirst
    _ =
      R ^ 4 *
          ‖h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ‖
        +
      (R⁻¹ * ‖ξ‖ ^ 5) *
          ‖h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ‖ := by
      ring
    _ ≤
      R ^ 4 *
          ‖h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ‖
        +
      (R⁻¹ * ‖ξ‖ ^ 5) *
          (‖h3SpectralScalarRawFourier F ξ‖ +
            ‖h3SpectralScalarRawFourier G ξ‖) := by
      exact
        add_le_add
          (le_refl _)
          (mul_le_mul_of_nonneg_left hsub hcoeff0)
    _ =
      R ^ 4 *
          ‖h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ‖
        +
      R⁻¹ *
        (‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier F ξ‖ +
          ‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier G ξ‖) := by
      ring

/-- Quartic Fourier difference controlled by raw `L¹` difference and endpoint
fifth moments. -/
theorem h3SpectralScalarRawFourierMomentMass_four_sub_le
    (F G : H3SpectralScalarState)
    {R : ℝ}
    (hR : 0 < R)
    (hF5 : H3RawFourierMomentIntegrable (5 : ℝ) F)
    (hG5 : H3RawFourierMomentIntegrable (5 : ℝ) G) :
    h3SpectralScalarRawFourierMomentMass (4 : ℝ) (F - G)
      ≤
    R ^ 4 * h3SpectralScalarRawFourierL1Mass (F - G)
      +
    R⁻¹ *
      (h3SpectralScalarRawFourierMomentMass (5 : ℝ) F +
        h3SpectralScalarRawFourierMomentMass (5 : ℝ) G) := by
  have hWeight4 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (4 : ℝ) ξ = ‖ξ‖ ^ 4 := by
    intro ξ
    exact h3FourierMomentWeight_natCast 4 ξ

  have hWeight5 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (5 : ℝ) ξ = ‖ξ‖ ^ 5 := by
    intro ξ
    exact h3FourierMomentWeight_natCast 5 ξ

  have hRawSubAE0 :=
    h3SpectralScalarRawFourier_sub_ae F G

  have hRawSubAE :
      h3SpectralScalarRawFourier (F - G)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ) := by
    simpa only [
      axisFintypeH3SchwartzClassicalizationQuarticDifferenceInterpolation,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hRawSubAE0

  have hRawSub0 :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 (F - G))

  have hRawSub :
      Integrable
        (h3SpectralScalarRawFourier (F - G))
        (volume : Measure H3FourierPoint3) := by
    simpa only [
      axisFintypeH3SchwartzClassicalizationQuarticDifferenceInterpolation,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hRawSub0

  have hRawSubNorm :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRawSub.norm

  have hF5' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hF5
    refine hF5.congr ?_
    filter_upwards with ξ
    rw [hWeight5 ξ]

  have hG5' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hG5
    refine hG5.congr ?_
    filter_upwards with ξ
    rw [hWeight5 ξ]

  have hMass4Sub :
      h3SpectralScalarRawFourierMomentMass (4 : ℝ) (F - G)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖h3SpectralScalarRawFourier (F - G) ξ‖ := by
    unfold h3SpectralScalarRawFourierMomentMass
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hWeight4 ξ]

  have hMass5F :
      h3SpectralScalarRawFourierMomentMass (5 : ℝ) F
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier F ξ‖ := by
    unfold h3SpectralScalarRawFourierMomentMass
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hWeight5 ξ]

  have hMass5G :
      h3SpectralScalarRawFourierMomentMass (5 : ℝ) G
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier G ξ‖ := by
    unfold h3SpectralScalarRawFourierMomentMass
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hWeight5 ξ]

  have hMass0Sub :
      h3SpectralScalarRawFourierL1Mass (F - G)
        =
      ∫ ξ : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier (F - G) ξ‖ := by
    unfold h3SpectralScalarRawFourierL1Mass
    simp only [
      axisFintypeH3SchwartzClassicalizationQuarticDifferenceInterpolation,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ]

  let major : H3FourierPoint3 → ℝ :=
    fun ξ =>
      R ^ 4 *
          ‖h3SpectralScalarRawFourier (F - G) ξ‖
        +
      R⁻¹ *
        (‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier F ξ‖ +
          ‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier G ξ‖)

  have hMajor :
      Integrable major
        (volume : Measure H3FourierPoint3) := by
    dsimp only [major]
    exact
      (hRawSubNorm.const_mul (R ^ 4)).add
        ((hF5'.add hG5').const_mul R⁻¹)

  have hLeftMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    ((continuous_norm.pow 4).aestronglyMeasurable.mul
      hRawSubNorm.aestronglyMeasurable)

  have hLeft :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajor.mono' hLeftMeas ?_
    exact hRawSubAE.mono (fun ξ hξ => by
      dsimp only [major]
      rw [hξ]
      have hPoint :=
        h3RawFourier_quarticDifference_pointwise_le
          F G hR ξ
      have hNonneg :
          0 ≤
            ‖ξ‖ ^ 4 *
              ‖h3SpectralScalarRawFourier F ξ -
                h3SpectralScalarRawFourier G ξ‖ :=
        mul_nonneg
          (pow_nonneg (norm_nonneg ξ) 4)
          (norm_nonneg _)
      simpa only [
        Real.norm_eq_abs,
        abs_of_nonneg hNonneg
      ] using hPoint)

  have hInt :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, major ξ := by
    apply integral_mono_ae hLeft hMajor
    exact hRawSubAE.mono (fun ξ hξ => by
      dsimp only [major]
      rw [hξ]
      exact
        h3RawFourier_quarticDifference_pointwise_le
          F G hR ξ)

  have hLowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          R ^ 4 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRawSubNorm.const_mul (R ^ 4)

  have hTailSumInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier F ξ‖ +
            ‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hF5'.add hG5'

  have hTailInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          R⁻¹ *
            (‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier F ξ‖ +
              ‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hTailSumInt.const_mul R⁻¹

  have hSplit :
      (∫ ξ : H3FourierPoint3,
          R ^ 4 *
              ‖h3SpectralScalarRawFourier (F - G) ξ‖
            +
          R⁻¹ *
            (‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier F ξ‖ +
              ‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier G ξ‖))
        =
      (∫ ξ : H3FourierPoint3,
          R ^ 4 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        +
      ∫ ξ : H3FourierPoint3,
        R⁻¹ *
          (‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier F ξ‖ +
            ‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier G ξ‖) :=
    integral_add hLowInt hTailInt

  have hMajorIntegral :
      (∫ ξ : H3FourierPoint3, major ξ)
        =
      R ^ 4 *
          h3SpectralScalarRawFourierL1Mass (F - G)
        +
      R⁻¹ *
        (h3SpectralScalarRawFourierMomentMass (5 : ℝ) F +
          h3SpectralScalarRawFourierMomentMass (5 : ℝ) G) := by
    calc
      (∫ ξ : H3FourierPoint3, major ξ)
          =
        (∫ ξ : H3FourierPoint3,
            R ^ 4 *
              ‖h3SpectralScalarRawFourier (F - G) ξ‖)
          +
        ∫ ξ : H3FourierPoint3,
          R⁻¹ *
            (‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier F ξ‖ +
              ‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier G ξ‖) := by
        dsimp only [major]
        exact hSplit
      _ =
        R ^ 4 *
            (∫ ξ : H3FourierPoint3,
              ‖h3SpectralScalarRawFourier (F - G) ξ‖)
          +
        R⁻¹ *
          (∫ ξ : H3FourierPoint3,
            (‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier F ξ‖ +
              ‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier G ξ‖)) := by
        rw [integral_const_mul, integral_const_mul]
      _ =
        R ^ 4 *
            (∫ ξ : H3FourierPoint3,
              ‖h3SpectralScalarRawFourier (F - G) ξ‖)
          +
        R⁻¹ *
          ((∫ ξ : H3FourierPoint3,
              ‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier F ξ‖)
            +
            ∫ ξ : H3FourierPoint3,
              ‖ξ‖ ^ 5 * ‖h3SpectralScalarRawFourier G ξ‖) := by
        rw [integral_add hF5' hG5']
      _ =
        R ^ 4 *
            h3SpectralScalarRawFourierL1Mass (F - G)
          +
        R⁻¹ *
          (h3SpectralScalarRawFourierMomentMass (5 : ℝ) F +
            h3SpectralScalarRawFourierMomentMass (5 : ℝ) G) := by
        rw [hMass0Sub, hMass5F, hMass5G]

  rw [hMass4Sub]
  rw [hMajorIntegral] at hInt
  exact hInt

/-- Topology-ready quartic interpolation: the low-frequency term is bounded
directly by the H³ norm difference. -/
theorem h3SpectralScalarRawFourierMomentMass_four_sub_le_norm
    (F G : H3SpectralScalarState)
    {R : ℝ}
    (hR : 0 < R)
    (hF5 : H3RawFourierMomentIntegrable (5 : ℝ) F)
    (hG5 : H3RawFourierMomentIntegrable (5 : ℝ) G) :
    h3SpectralScalarRawFourierMomentMass (4 : ℝ) (F - G)
      ≤
    (R ^ 4 * h3RawFourierL1DeweightingCoefficient) * ‖F - G‖
      +
    R⁻¹ *
      (h3SpectralScalarRawFourierMomentMass (5 : ℝ) F +
        h3SpectralScalarRawFourierMomentMass (5 : ℝ) G) := by
  have hInterp :=
    h3SpectralScalarRawFourierMomentMass_four_sub_le
      F G hR hF5 hG5

  have hLow :=
    h3SpectralScalarRawFourierL1Mass_le_norm (F - G)

  have hR4 :
      0 ≤ R ^ 4 :=
    pow_nonneg hR.le 4

  have hLow' :
      R ^ 4 * h3SpectralScalarRawFourierL1Mass (F - G)
        ≤
      R ^ 4 *
        (h3RawFourierL1DeweightingCoefficient * ‖F - G‖) :=
    mul_le_mul_of_nonneg_left hLow hR4

  calc
    h3SpectralScalarRawFourierMomentMass (4 : ℝ) (F - G)
        ≤
      R ^ 4 * h3SpectralScalarRawFourierL1Mass (F - G)
        +
      R⁻¹ *
        (h3SpectralScalarRawFourierMomentMass (5 : ℝ) F +
          h3SpectralScalarRawFourierMomentMass (5 : ℝ) G) :=
      hInterp
    _ ≤
      R ^ 4 *
          (h3RawFourierL1DeweightingCoefficient * ‖F - G‖)
        +
      R⁻¹ *
        (h3SpectralScalarRawFourierMomentMass (5 : ℝ) F +
          h3SpectralScalarRawFourierMomentMass (5 : ℝ) G) := by
      exact add_le_add hLow' (le_refl _)
    _ =
      (R ^ 4 * h3RawFourierL1DeweightingCoefficient) * ‖F - G‖
        +
      R⁻¹ *
        (h3SpectralScalarRawFourierMomentMass (5 : ℝ) F +
          h3SpectralScalarRawFourierMomentMass (5 : ℝ) G) := by
      ring

end
end Euclidean
end Bridge
end PrimeTensor
