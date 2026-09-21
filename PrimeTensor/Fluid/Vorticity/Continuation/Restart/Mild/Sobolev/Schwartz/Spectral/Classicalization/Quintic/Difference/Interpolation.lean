import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quartic.Difference.Interpolation

/-!
# Classicalization: quintic Fourier difference interpolation

The selected positive-time path has every finite natural Fourier moment.
The quartic continuity layer uses

    |ξ|⁴ ≤ R⁴ + R⁻¹ |ξ|⁵.

The order-five step is identical:

    |ξ|⁵ ≤ R⁵ + R⁻¹ |ξ|⁶.

Consequently

    M₅(F - G)
      ≤ R⁵ C_dw ‖F - G‖
        + R⁻¹ (M₆(F) + M₆(G)).

This is the topology bridge needed for fifth spatial jet time continuity.
The natural-moment induction already supplies the local sixth-moment envelope,
so no new Navier--Stokes estimate occurs here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationQuinticDifferenceInterpolation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Elementary quintic low/high-frequency inequality. -/
theorem norm_pow_five_le_radius_five_add_inv_mul_six
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 5
      ≤
    R ^ 5 + R⁻¹ * ‖ξ‖ ^ 6 := by
  have hx0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have hR0 : 0 ≤ R := hR.le

  by_cases hxR : ‖ξ‖ ≤ R

  · have hpow :
        ‖ξ‖ ^ 5 ≤ R ^ 5 :=
      pow_le_pow_left₀ hx0 hxR 5

    have htail0 :
        0 ≤ R⁻¹ * ‖ξ‖ ^ 6 := by
      exact
        mul_nonneg
          (inv_nonneg.mpr hR0)
          (pow_nonneg hx0 6)

    exact le_add_of_le_of_nonneg hpow htail0

  · have hRx : R ≤ ‖ξ‖ :=
      le_of_lt (lt_of_not_ge hxR)

    have hx5 : 0 ≤ ‖ξ‖ ^ 5 :=
      pow_nonneg hx0 5

    have hmul :
        R * ‖ξ‖ ^ 5 ≤ ‖ξ‖ * ‖ξ‖ ^ 5 :=
      mul_le_mul_of_nonneg_right hRx hx5

    have hsix :
        ‖ξ‖ ^ 5 ≤ R⁻¹ * ‖ξ‖ ^ 6 := by
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ hR).2
      calc
        ‖ξ‖ ^ 5 * R = R * ‖ξ‖ ^ 5 := by ring
        _ ≤ ‖ξ‖ * ‖ξ‖ ^ 5 := hmul
        _ = ‖ξ‖ ^ 6 := by ring

    exact
      le_add_of_nonneg_of_le
        (pow_nonneg hR0 5)
        hsix

/-- Pointwise quintic difference majorant underlying the interpolation lemma. -/
theorem h3RawFourier_quinticDifference_pointwise_le
    (F G : H3SpectralScalarState)
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 5 *
        ‖h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ‖
      ≤
    R ^ 5 *
        ‖h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ‖
      +
    R⁻¹ *
      (‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier F ξ‖ +
        ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier G ξ‖) := by
  have hweight :=
    norm_pow_five_le_radius_five_add_inv_mul_six hR ξ

  have hdiff0 :
      0 ≤
        ‖h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ‖ :=
    norm_nonneg _

  have hfirst :
      ‖ξ‖ ^ 5 *
          ‖h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ‖
        ≤
      (R ^ 5 + R⁻¹ * ‖ξ‖ ^ 6) *
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
      0 ≤ R⁻¹ * ‖ξ‖ ^ 6 := by
    exact
      mul_nonneg
        (inv_nonneg.mpr hR.le)
        (pow_nonneg (norm_nonneg ξ) 6)

  calc
    ‖ξ‖ ^ 5 *
        ‖h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ‖
        ≤
      (R ^ 5 + R⁻¹ * ‖ξ‖ ^ 6) *
        ‖h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ‖ :=
      hfirst
    _ =
      R ^ 5 *
          ‖h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ‖
        +
      (R⁻¹ * ‖ξ‖ ^ 6) *
          ‖h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ‖ := by
      ring
    _ ≤
      R ^ 5 *
          ‖h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ‖
        +
      (R⁻¹ * ‖ξ‖ ^ 6) *
          (‖h3SpectralScalarRawFourier F ξ‖ +
            ‖h3SpectralScalarRawFourier G ξ‖) := by
      exact
        add_le_add
          (le_refl _)
          (mul_le_mul_of_nonneg_left hsub hcoeff0)
    _ =
      R ^ 5 *
          ‖h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ‖
        +
      R⁻¹ *
        (‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier F ξ‖ +
          ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier G ξ‖) := by
      ring

/-- Quintic Fourier difference controlled by raw `L¹` difference and endpoint
sixth moments. -/
theorem h3SpectralScalarRawFourierMomentMass_five_sub_le
    (F G : H3SpectralScalarState)
    {R : ℝ}
    (hR : 0 < R)
    (hF6 : H3RawFourierMomentIntegrable (6 : ℝ) F)
    (hG6 : H3RawFourierMomentIntegrable (6 : ℝ) G) :
    h3SpectralScalarRawFourierMomentMass (5 : ℝ) (F - G)
      ≤
    R ^ 5 * h3SpectralScalarRawFourierL1Mass (F - G)
      +
    R⁻¹ *
      (h3SpectralScalarRawFourierMomentMass (6 : ℝ) F +
        h3SpectralScalarRawFourierMomentMass (6 : ℝ) G) := by
  have hWeight5 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (5 : ℝ) ξ = ‖ξ‖ ^ 5 := by
    intro ξ
    exact h3FourierMomentWeight_natCast 5 ξ

  have hWeight6 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (6 : ℝ) ξ = ‖ξ‖ ^ 6 := by
    intro ξ
    exact h3FourierMomentWeight_natCast 6 ξ

  have hRawSubAE0 :=
    h3SpectralScalarRawFourier_sub_ae F G

  have hRawSubAE :
      h3SpectralScalarRawFourier (F - G)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ) := by
    simpa only [
      axisFintypeH3SchwartzClassicalizationQuinticDifferenceInterpolation,
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
      axisFintypeH3SchwartzClassicalizationQuinticDifferenceInterpolation,
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

  have hF6' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hF6
    refine hF6.congr ?_
    filter_upwards with ξ
    rw [hWeight6 ξ]

  have hG6' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hG6
    refine hG6.congr ?_
    filter_upwards with ξ
    rw [hWeight6 ξ]

  have hMass5Sub :
      h3SpectralScalarRawFourierMomentMass (5 : ℝ) (F - G)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 5 *
          ‖h3SpectralScalarRawFourier (F - G) ξ‖ := by
    unfold h3SpectralScalarRawFourierMomentMass
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hWeight5 ξ]

  have hMass6F :
      h3SpectralScalarRawFourierMomentMass (6 : ℝ) F
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier F ξ‖ := by
    unfold h3SpectralScalarRawFourierMomentMass
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hWeight6 ξ]

  have hMass6G :
      h3SpectralScalarRawFourierMomentMass (6 : ℝ) G
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier G ξ‖ := by
    unfold h3SpectralScalarRawFourierMomentMass
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hWeight6 ξ]

  have hMass0Sub :
      h3SpectralScalarRawFourierL1Mass (F - G)
        =
      ∫ ξ : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier (F - G) ξ‖ := by
    unfold h3SpectralScalarRawFourierL1Mass
    simp only [
      axisFintypeH3SchwartzClassicalizationQuinticDifferenceInterpolation,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ]

  let major : H3FourierPoint3 → ℝ :=
    fun ξ =>
      R ^ 5 *
          ‖h3SpectralScalarRawFourier (F - G) ξ‖
        +
      R⁻¹ *
        (‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier F ξ‖ +
          ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier G ξ‖)

  have hMajor :
      Integrable major
        (volume : Measure H3FourierPoint3) := by
    dsimp only [major]
    exact
      (hRawSubNorm.const_mul (R ^ 5)).add
        ((hF6'.add hG6').const_mul R⁻¹)

  have hLeftMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    ((continuous_norm.pow 5).aestronglyMeasurable.mul
      hRawSubNorm.aestronglyMeasurable)

  have hLeft :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajor.mono' hLeftMeas ?_
    exact hRawSubAE.mono (fun ξ hξ => by
      dsimp only [major]
      rw [hξ]
      have hPoint :=
        h3RawFourier_quinticDifference_pointwise_le
          F G hR ξ
      have hNonneg :
          0 ≤
            ‖ξ‖ ^ 5 *
              ‖h3SpectralScalarRawFourier F ξ -
                h3SpectralScalarRawFourier G ξ‖ :=
        mul_nonneg
          (pow_nonneg (norm_nonneg ξ) 5)
          (norm_nonneg _)
      simpa only [
        Real.norm_eq_abs,
        abs_of_nonneg hNonneg
      ] using hPoint)

  have hInt :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, major ξ := by
    apply integral_mono_ae hLeft hMajor
    exact hRawSubAE.mono (fun ξ hξ => by
      dsimp only [major]
      rw [hξ]
      exact
        h3RawFourier_quinticDifference_pointwise_le
          F G hR ξ)

  have hLowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          R ^ 5 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRawSubNorm.const_mul (R ^ 5)

  have hTailSumInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier F ξ‖ +
            ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hF6'.add hG6'

  have hTailInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          R⁻¹ *
            (‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier F ξ‖ +
              ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hTailSumInt.const_mul R⁻¹

  have hSplit :
      (∫ ξ : H3FourierPoint3,
          R ^ 5 *
              ‖h3SpectralScalarRawFourier (F - G) ξ‖
            +
          R⁻¹ *
            (‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier F ξ‖ +
              ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier G ξ‖))
        =
      (∫ ξ : H3FourierPoint3,
          R ^ 5 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        +
      ∫ ξ : H3FourierPoint3,
        R⁻¹ *
          (‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier F ξ‖ +
            ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier G ξ‖) :=
    integral_add hLowInt hTailInt

  have hMajorIntegral :
      (∫ ξ : H3FourierPoint3, major ξ)
        =
      R ^ 5 *
          h3SpectralScalarRawFourierL1Mass (F - G)
        +
      R⁻¹ *
        (h3SpectralScalarRawFourierMomentMass (6 : ℝ) F +
          h3SpectralScalarRawFourierMomentMass (6 : ℝ) G) := by
    calc
      (∫ ξ : H3FourierPoint3, major ξ)
          =
        (∫ ξ : H3FourierPoint3,
            R ^ 5 *
              ‖h3SpectralScalarRawFourier (F - G) ξ‖)
          +
        ∫ ξ : H3FourierPoint3,
          R⁻¹ *
            (‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier F ξ‖ +
              ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier G ξ‖) := by
        dsimp only [major]
        exact hSplit
      _ =
        R ^ 5 *
            (∫ ξ : H3FourierPoint3,
              ‖h3SpectralScalarRawFourier (F - G) ξ‖)
          +
        R⁻¹ *
          (∫ ξ : H3FourierPoint3,
            (‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier F ξ‖ +
              ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier G ξ‖)) := by
        rw [integral_const_mul, integral_const_mul]
      _ =
        R ^ 5 *
            (∫ ξ : H3FourierPoint3,
              ‖h3SpectralScalarRawFourier (F - G) ξ‖)
          +
        R⁻¹ *
          ((∫ ξ : H3FourierPoint3,
              ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier F ξ‖)
            +
            ∫ ξ : H3FourierPoint3,
              ‖ξ‖ ^ 6 * ‖h3SpectralScalarRawFourier G ξ‖) := by
        rw [integral_add hF6' hG6']
      _ =
        R ^ 5 *
            h3SpectralScalarRawFourierL1Mass (F - G)
          +
        R⁻¹ *
          (h3SpectralScalarRawFourierMomentMass (6 : ℝ) F +
            h3SpectralScalarRawFourierMomentMass (6 : ℝ) G) := by
        rw [hMass0Sub, hMass6F, hMass6G]

  rw [hMass5Sub]
  rw [hMajorIntegral] at hInt
  exact hInt

/-- Topology-ready quintic interpolation: the low-frequency term is bounded
directly by the H³ norm difference. -/
theorem h3SpectralScalarRawFourierMomentMass_five_sub_le_norm
    (F G : H3SpectralScalarState)
    {R : ℝ}
    (hR : 0 < R)
    (hF6 : H3RawFourierMomentIntegrable (6 : ℝ) F)
    (hG6 : H3RawFourierMomentIntegrable (6 : ℝ) G) :
    h3SpectralScalarRawFourierMomentMass (5 : ℝ) (F - G)
      ≤
    (R ^ 5 * h3RawFourierL1DeweightingCoefficient) * ‖F - G‖
      +
    R⁻¹ *
      (h3SpectralScalarRawFourierMomentMass (6 : ℝ) F +
        h3SpectralScalarRawFourierMomentMass (6 : ℝ) G) := by
  have hInterp :=
    h3SpectralScalarRawFourierMomentMass_five_sub_le
      F G hR hF6 hG6

  have hLow :=
    h3SpectralScalarRawFourierL1Mass_le_norm (F - G)

  have hR5 :
      0 ≤ R ^ 5 :=
    pow_nonneg hR.le 5

  have hLow' :
      R ^ 5 * h3SpectralScalarRawFourierL1Mass (F - G)
        ≤
      R ^ 5 *
        (h3RawFourierL1DeweightingCoefficient * ‖F - G‖) :=
    mul_le_mul_of_nonneg_left hLow hR5

  calc
    h3SpectralScalarRawFourierMomentMass (5 : ℝ) (F - G)
        ≤
      R ^ 5 * h3SpectralScalarRawFourierL1Mass (F - G)
        +
      R⁻¹ *
        (h3SpectralScalarRawFourierMomentMass (6 : ℝ) F +
          h3SpectralScalarRawFourierMomentMass (6 : ℝ) G) :=
      hInterp
    _ ≤
      R ^ 5 *
          (h3RawFourierL1DeweightingCoefficient * ‖F - G‖)
        +
      R⁻¹ *
        (h3SpectralScalarRawFourierMomentMass (6 : ℝ) F +
          h3SpectralScalarRawFourierMomentMass (6 : ℝ) G) := by
      exact add_le_add hLow' (le_refl _)
    _ =
      (R ^ 5 * h3RawFourierL1DeweightingCoefficient) * ‖F - G‖
        +
      R⁻¹ *
        (h3SpectralScalarRawFourierMomentMass (6 : ℝ) F +
          h3SpectralScalarRawFourierMomentMass (6 : ℝ) G) := by
      ring

end
end Euclidean
end Bridge
end PrimeTensor
