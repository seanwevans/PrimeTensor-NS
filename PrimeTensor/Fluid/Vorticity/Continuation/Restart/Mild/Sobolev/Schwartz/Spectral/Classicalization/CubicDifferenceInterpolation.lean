import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpatialRegularity

/-!
# Classicalization: cubic Fourier difference interpolation

The selected positive-time path now has every finite natural Fourier moment.
To turn those static moment bounds into time continuity of the third spatial
jet, one needs a topology bridge.

For a frequency radius `R > 0`,

    |ξ|³ ≤ R³ + R⁻¹ |ξ|⁴.

Applied to the difference of two spectral states, this gives

    M₃(F - G)
      ≤ R³ m₀(F - G)
        + R⁻¹ (M₄(F) + M₄(G)).

The unweighted raw Fourier difference is controlled by the H³ norm through
the already-compiled deweighting estimate.  Hence

    M₃(F - G)
      ≤ R³ C_dw ‖F - G‖
        + R⁻¹ (M₄(F) + M₄(G)).

This is the exact interpolation mechanism required for third-jet time
continuity: choose `R` large using a local uniform fourth-moment bound, then
use continuity of the selected H³ path to make the first term small.

No new Navier--Stokes estimate occurs here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- Use exactly the axis `Fintype` chosen by the generic moment algebra.
This keeps `H3FourierPoint3`, its norm, and `volume` definitionally aligned
with `H3RawFourierMomentIntegrable` and the generic moment masses. -/
noncomputable local instance axisFintypeH3SchwartzClassicalizationCubicDifferenceInterpolation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/- The imported H³ bridge already provides
`h3SpectralScalarRawFourier_sub_ae`, the almost-everywhere subtraction
identity for the raw Fourier representative. -/

/-- Elementary low/high-frequency inequality without introducing measurable
frequency regions. -/
theorem norm_pow_three_le_radius_three_add_inv_mul_four
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 3
      ≤
    R ^ 3 + R⁻¹ * ‖ξ‖ ^ 4 := by
  have hx0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have hR0 : 0 ≤ R := hR.le

  by_cases hxR : ‖ξ‖ ≤ R

  · have hpow :
        ‖ξ‖ ^ 3 ≤ R ^ 3 :=
      pow_le_pow_left₀ hx0 hxR 3

    have htail0 :
        0 ≤ R⁻¹ * ‖ξ‖ ^ 4 := by
      exact mul_nonneg (inv_nonneg.mpr hR0) (pow_nonneg hx0 4)

    exact le_add_of_le_of_nonneg hpow htail0

  · have hRx : R ≤ ‖ξ‖ :=
      le_of_lt (lt_of_not_ge hxR)

    have hx3 : 0 ≤ ‖ξ‖ ^ 3 :=
      pow_nonneg hx0 3

    have hmul :
        R * ‖ξ‖ ^ 3 ≤ ‖ξ‖ * ‖ξ‖ ^ 3 :=
      mul_le_mul_of_nonneg_right hRx hx3

    have hfour :
        ‖ξ‖ ^ 3 ≤ R⁻¹ * ‖ξ‖ ^ 4 := by
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ hR).2
      calc
        ‖ξ‖ ^ 3 * R = R * ‖ξ‖ ^ 3 := by ring
        _ ≤ ‖ξ‖ * ‖ξ‖ ^ 3 := hmul
        _ = ‖ξ‖ ^ 4 := by ring

    exact le_add_of_nonneg_of_le (pow_nonneg hR0 3) hfour

/-- Pointwise cubic difference majorant underlying the interpolation lemma.
This is stated for the literal pointwise difference; the `Lp` subtraction
representative is connected to it almost everywhere above. -/
theorem h3RawFourier_cubicDifference_pointwise_le
    (F G : H3SpectralScalarState)
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 3 *
        ‖h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ‖
      ≤
    R ^ 3 *
        ‖h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ‖
      +
    R⁻¹ *
      (‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier F ξ‖ +
        ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier G ξ‖) := by
  have hweight :=
    norm_pow_three_le_radius_three_add_inv_mul_four hR ξ

  have hdiff0 :
      0 ≤
        ‖h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ‖ :=
    norm_nonneg _

  have hfirst :
      ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ‖
        ≤
      (R ^ 3 + R⁻¹ * ‖ξ‖ ^ 4) *
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
      0 ≤ R⁻¹ * ‖ξ‖ ^ 4 := by
    exact
      mul_nonneg
        (inv_nonneg.mpr hR.le)
        (pow_nonneg (norm_nonneg ξ) 4)

  calc
    ‖ξ‖ ^ 3 *
        ‖h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ‖
        ≤
      (R ^ 3 + R⁻¹ * ‖ξ‖ ^ 4) *
        ‖h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ‖ :=
      hfirst
    _ =
      R ^ 3 *
          ‖h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ‖
        +
      (R⁻¹ * ‖ξ‖ ^ 4) *
          ‖h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ‖ := by
      ring
    _ ≤
      R ^ 3 *
          ‖h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ‖
        +
      (R⁻¹ * ‖ξ‖ ^ 4) *
          (‖h3SpectralScalarRawFourier F ξ‖ +
            ‖h3SpectralScalarRawFourier G ξ‖) := by
      exact
        add_le_add
          (le_refl _)
          (mul_le_mul_of_nonneg_left hsub hcoeff0)
    _ =
      R ^ 3 *
          ‖h3SpectralScalarRawFourier F ξ -
            h3SpectralScalarRawFourier G ξ‖
        +
      R⁻¹ *
        (‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier F ξ‖ +
          ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier G ξ‖) := by
      ring

/-- Cubic Fourier difference controlled by raw `L¹` difference and endpoint
fourth moments. -/
theorem h3SpectralScalarRawFourierMomentMass_three_sub_le
    (F G : H3SpectralScalarState)
    {R : ℝ}
    (hR : 0 < R)
    (hF4 : H3RawFourierMomentIntegrable (4 : ℝ) F)
    (hG4 : H3RawFourierMomentIntegrable (4 : ℝ) G) :
    h3SpectralScalarRawFourierMomentMass (3 : ℝ) (F - G)
      ≤
    R ^ 3 * h3SpectralScalarRawFourierL1Mass (F - G)
      +
    R⁻¹ *
      (h3SpectralScalarRawFourierMomentMass (4 : ℝ) F +
        h3SpectralScalarRawFourierMomentMass (4 : ℝ) G) := by
  have hWeight3 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (3 : ℝ) ξ = ‖ξ‖ ^ 3 := by
    intro ξ
    exact h3FourierMomentWeight_natCast 3 ξ

  have hWeight4 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (4 : ℝ) ξ = ‖ξ‖ ^ 4 := by
    intro ξ
    exact h3FourierMomentWeight_natCast 4 ξ

  have hRawSubAE0 :=
    h3SpectralScalarRawFourier_sub_ae F G

  have hRawSubAE :
      h3SpectralScalarRawFourier (F - G)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ) := by
    simpa only [
      axisFintypeH3SchwartzClassicalizationCubicDifferenceInterpolation,
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
      axisFintypeH3SchwartzClassicalizationCubicDifferenceInterpolation,
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

  have hF4' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hF4
    refine hF4.congr ?_
    filter_upwards with ξ
    rw [hWeight4 ξ]

  have hG4' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hG4
    refine hG4.congr ?_
    filter_upwards with ξ
    rw [hWeight4 ξ]

  have hMass3Sub :
      h3SpectralScalarRawFourierMomentMass (3 : ℝ) (F - G)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarRawFourier (F - G) ξ‖ := by
    unfold h3SpectralScalarRawFourierMomentMass
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hWeight3 ξ]

  have hMass4F :
      h3SpectralScalarRawFourierMomentMass (4 : ℝ) F
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier F ξ‖ := by
    unfold h3SpectralScalarRawFourierMomentMass
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hWeight4 ξ]

  have hMass4G :
      h3SpectralScalarRawFourierMomentMass (4 : ℝ) G
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier G ξ‖ := by
    unfold h3SpectralScalarRawFourierMomentMass
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hWeight4 ξ]

  have hMass0Sub :
      h3SpectralScalarRawFourierL1Mass (F - G)
        =
      ∫ ξ : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier (F - G) ξ‖ := by
    unfold h3SpectralScalarRawFourierL1Mass
    simp only [
      axisFintypeH3SchwartzClassicalizationCubicDifferenceInterpolation,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ]

  let major : H3FourierPoint3 → ℝ :=
    fun ξ =>
      R ^ 3 *
          ‖h3SpectralScalarRawFourier (F - G) ξ‖
        +
      R⁻¹ *
        (‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier F ξ‖ +
          ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier G ξ‖)

  have hMajor :
      Integrable major
        (volume : Measure H3FourierPoint3) := by
    dsimp only [major]
    exact
      (hRawSubNorm.const_mul (R ^ 3)).add
        ((hF4'.add hG4').const_mul R⁻¹)

  have hLeftMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((continuous_norm.pow 3).aestronglyMeasurable.mul
        hRawSubNorm.aestronglyMeasurable)

  have hLeft :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajor.mono' hLeftMeas ?_
    exact hRawSubAE.mono (fun ξ hξ => by
      dsimp only [major]
      rw [hξ]
      have hPoint :=
        h3RawFourier_cubicDifference_pointwise_le
          F G hR ξ
      have hNonneg :
          0 ≤
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier F ξ -
                h3SpectralScalarRawFourier G ξ‖ :=
        mul_nonneg
          (pow_nonneg (norm_nonneg ξ) 3)
          (norm_nonneg _)
      simpa only [
        Real.norm_eq_abs,
        abs_of_nonneg hNonneg
      ] using hPoint)

  have hInt :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, major ξ := by
    apply integral_mono_ae hLeft hMajor
    exact hRawSubAE.mono (fun ξ hξ => by
      dsimp only [major]
      rw [hξ]
      exact
        h3RawFourier_cubicDifference_pointwise_le
          F G hR ξ)

  have hLowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          R ^ 3 * ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRawSubNorm.const_mul (R ^ 3)

  have hTailSumInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier F ξ‖ +
            ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hF4'.add hG4'

  have hTailInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          R⁻¹ *
            (‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier F ξ‖ +
              ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hTailSumInt.const_mul R⁻¹

  have hSplit :
      (∫ ξ : H3FourierPoint3,
          R ^ 3 * ‖h3SpectralScalarRawFourier (F - G) ξ‖ +
            R⁻¹ *
              (‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier F ξ‖ +
                ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier G ξ‖))
        =
      (∫ ξ : H3FourierPoint3,
          R ^ 3 * ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        +
      ∫ ξ : H3FourierPoint3,
        R⁻¹ *
          (‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier F ξ‖ +
            ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier G ξ‖) := by
    exact integral_add hLowInt hTailInt

  have hMajorIntegral :
      (∫ ξ : H3FourierPoint3, major ξ)
        =
      R ^ 3 *
          h3SpectralScalarRawFourierL1Mass (F - G)
        +
      R⁻¹ *
        (h3SpectralScalarRawFourierMomentMass (4 : ℝ) F +
          h3SpectralScalarRawFourierMomentMass (4 : ℝ) G) := by
    calc
      (∫ ξ : H3FourierPoint3, major ξ)
          =
        (∫ ξ : H3FourierPoint3,
            R ^ 3 *
              ‖h3SpectralScalarRawFourier (F - G) ξ‖)
          +
        ∫ ξ : H3FourierPoint3,
          R⁻¹ *
            (‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier F ξ‖ +
              ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier G ξ‖) := by
        dsimp only [major]
        exact hSplit
      _ =
        R ^ 3 *
            (∫ ξ : H3FourierPoint3,
              ‖h3SpectralScalarRawFourier (F - G) ξ‖)
          +
        R⁻¹ *
          (∫ ξ : H3FourierPoint3,
            (‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier F ξ‖ +
              ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier G ξ‖)) := by
        rw [integral_const_mul, integral_const_mul]
      _ =
        R ^ 3 *
            (∫ ξ : H3FourierPoint3,
              ‖h3SpectralScalarRawFourier (F - G) ξ‖)
          +
        R⁻¹ *
          ((∫ ξ : H3FourierPoint3,
              ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier F ξ‖) +
            ∫ ξ : H3FourierPoint3,
              ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier G ξ‖) := by
        rw [integral_add hF4' hG4']
      _ =
        R ^ 3 *
            h3SpectralScalarRawFourierL1Mass (F - G)
          +
        R⁻¹ *
          (h3SpectralScalarRawFourierMomentMass (4 : ℝ) F +
            h3SpectralScalarRawFourierMomentMass (4 : ℝ) G) := by
        rw [hMass0Sub, hMass4F, hMass4G]

  rw [hMass3Sub]
  rw [hMajorIntegral] at hInt
  exact hInt

/-- Final topology-ready form: the low-frequency part is bounded directly by
the H³ norm difference. -/
theorem h3SpectralScalarRawFourierMomentMass_three_sub_le_norm
    (F G : H3SpectralScalarState)
    {R : ℝ}
    (hR : 0 < R)
    (hF4 : H3RawFourierMomentIntegrable (4 : ℝ) F)
    (hG4 : H3RawFourierMomentIntegrable (4 : ℝ) G) :
    h3SpectralScalarRawFourierMomentMass (3 : ℝ) (F - G)
      ≤
    (R ^ 3 * h3RawFourierL1DeweightingCoefficient) * ‖F - G‖
      +
    R⁻¹ *
      (h3SpectralScalarRawFourierMomentMass (4 : ℝ) F +
        h3SpectralScalarRawFourierMomentMass (4 : ℝ) G) := by
  have hInterp :=
    h3SpectralScalarRawFourierMomentMass_three_sub_le
      F G hR hF4 hG4

  have hLow :=
    h3SpectralScalarRawFourierL1Mass_le_norm (F - G)

  have hR3 :
      0 ≤ R ^ 3 :=
    pow_nonneg hR.le 3

  have hLow' :
      R ^ 3 * h3SpectralScalarRawFourierL1Mass (F - G)
        ≤
      R ^ 3 *
        (h3RawFourierL1DeweightingCoefficient * ‖F - G‖) :=
    mul_le_mul_of_nonneg_left hLow hR3

  calc
    h3SpectralScalarRawFourierMomentMass (3 : ℝ) (F - G)
        ≤
      R ^ 3 * h3SpectralScalarRawFourierL1Mass (F - G)
        +
      R⁻¹ *
        (h3SpectralScalarRawFourierMomentMass (4 : ℝ) F +
          h3SpectralScalarRawFourierMomentMass (4 : ℝ) G) :=
      hInterp
    _ ≤
      R ^ 3 *
          (h3RawFourierL1DeweightingCoefficient * ‖F - G‖)
        +
      R⁻¹ *
        (h3SpectralScalarRawFourierMomentMass (4 : ℝ) F +
          h3SpectralScalarRawFourierMomentMass (4 : ℝ) G) := by
      exact add_le_add hLow' (le_refl _)
    _ =
      (R ^ 3 * h3RawFourierL1DeweightingCoefficient) * ‖F - G‖
        +
      R⁻¹ *
        (h3SpectralScalarRawFourierMomentMass (4 : ℝ) F +
          h3SpectralScalarRawFourierMomentMass (4 : ℝ) G) := by
      ring

end
end Euclidean
end Bridge
end PrimeTensor
