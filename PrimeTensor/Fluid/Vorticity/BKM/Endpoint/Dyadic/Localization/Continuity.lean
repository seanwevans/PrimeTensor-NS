import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Fourier.Localization

/-!
# BKM endpoint: continuity of dyadic Fourier localization on L²

The localized BKM multiplier has pointwise norm at most one.  The preceding
endpoint files package multiplication by that symbol as an `L²` state and
identify its action on the Fourier transforms of the three physical vorticity
components.

For the endpoint convolution theorem we next need a closure argument from a
dense Schwartz class.  This file isolates the continuity of the Fourier-side
operator used in that argument.

For fixed dyadic scale and coordinate indices, the localization map

    F ↦ Mᵢₖ,R F

* is contractive on Fourier `L²`;
* commutes exactly with subtraction;
* is `1`-Lipschitz;
* remains `1`-Lipschitz after composition with Mathlib's unitary `L²`
  Fourier transform.

No convolution identity is asserted here.  The purpose is to make the
Fourier-side target a closed, quantitatively continuous operator before the
Young-convolution side is extended from Schwartz data.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter FourierTransform
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicLocalizationContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Localized multiplier application is contractive on Fourier `L²`. -/
theorem norm_h3BKMLocalizedCoordinateMultiplierApplyL2_le
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (F : H3FourierComplexL2) :
    ‖h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k F‖
      ≤
    ‖F‖ := by

  unfold h3BKMLocalizedCoordinateMultiplierApplyL2

  rw [
    MeasureTheory.Lp.norm_toLp,
    MeasureTheory.Lp.norm_def
  ]

  refine
    ENNReal.toReal_mono
      (MeasureTheory.Lp.eLpNorm_ne_top F)
      ?_

  apply eLpNorm_mono_ae

  filter_upwards with ξ

  rw [norm_mul]

  calc
    ‖h3BKMLocalizedCoordinateMultiplier
        R hR i k ξ‖ * ‖F ξ‖
        ≤
      1 * ‖F ξ‖ := by
        exact
          mul_le_mul_of_nonneg_right
            (norm_h3BKMLocalizedCoordinateMultiplier_le_one
              hR i k ξ)
            (norm_nonneg _)

    _ = ‖F ξ‖ := by
      rw [one_mul]

/-- Localized multiplier application commutes exactly with subtraction. -/
theorem h3BKMLocalizedCoordinateMultiplierApplyL2_sub
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (F G : H3FourierComplexL2) :
    h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k (F - G)
      =
    h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k F
      -
    h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k G := by

  apply MeasureTheory.Lp.ext

  filter_upwards [
    h3BKMLocalizedCoordinateMultiplierApplyL2_ae
      hR i k (F - G),
    h3BKMLocalizedCoordinateMultiplierApplyL2_ae
      hR i k F,
    h3BKMLocalizedCoordinateMultiplierApplyL2_ae
      hR i k G,
    MeasureTheory.Lp.coeFn_sub F G,
    MeasureTheory.Lp.coeFn_sub
      (h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k F)
      (h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k G)
  ] with ξ hOut hF hG hIn hSub

  rw [hOut, hSub]

  simp only [Pi.sub_apply] at hIn ⊢

  rw [hIn, hF, hG]

  ring

/-- Difference form of the localization contraction. -/
theorem norm_h3BKMLocalizedCoordinateMultiplierApplyL2_sub_le
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (F G : H3FourierComplexL2) :
    ‖h3BKMLocalizedCoordinateMultiplierApplyL2 R hR i k F
        -
      h3BKMLocalizedCoordinateMultiplierApplyL2 R hR i k G‖
      ≤
    ‖F - G‖ := by

  rw [
    ← h3BKMLocalizedCoordinateMultiplierApplyL2_sub
      hR i k F G
  ]

  exact
    norm_h3BKMLocalizedCoordinateMultiplierApplyL2_le
      hR i k (F - G)

/-- Fixed dyadic localization is `1`-Lipschitz on Fourier `L²`. -/
theorem lipschitzWith_h3BKMLocalizedCoordinateMultiplierApplyL2
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    LipschitzWith 1
      (h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k :
        H3FourierComplexL2 →
          H3FourierComplexL2) := by

  apply LipschitzWith.of_dist_le_mul

  intro F G

  rw [dist_eq_norm, dist_eq_norm]

  simpa only [NNReal.coe_one, one_mul] using
    norm_h3BKMLocalizedCoordinateMultiplierApplyL2_sub_le
      hR i k F G

/-- Fixed dyadic localization is continuous on Fourier `L²`. -/
theorem continuous_h3BKMLocalizedCoordinateMultiplierApplyL2
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    Continuous
      (h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k :
        H3FourierComplexL2 →
          H3FourierComplexL2) :=
  (lipschitzWith_h3BKMLocalizedCoordinateMultiplierApplyL2
    hR i k).continuous

/--
Fourier transform followed by fixed dyadic localization is still
`1`-Lipschitz on `L²`.
-/
theorem lipschitzWith_h3BKMFourierLocalizedCoordinateMultiplierApplyL2
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    LipschitzWith 1
      (fun F : H3FourierComplexL2 =>
        h3BKMLocalizedCoordinateMultiplierApplyL2
          R hR i k
          ((MeasureTheory.Lp.fourierTransformₗᵢ
              H3FourierPoint3 ℂ) F)) := by

  apply LipschitzWith.of_dist_le_mul

  intro F G

  rw [dist_eq_norm, dist_eq_norm]

  have hFourierSub :
      (MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ) (F - G)
        =
      (MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ) F
        -
      (MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ) G := by
    exact
      (MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ).map_sub F G

  rw [
    ← h3BKMLocalizedCoordinateMultiplierApplyL2_sub
      hR i k
      ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ) F)
      ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ) G),
    ← hFourierSub
  ]

  calc
    ‖h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k
        ((MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ) (F - G))‖
        ≤
      ‖(MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ) (F - G)‖ := by
        exact
          norm_h3BKMLocalizedCoordinateMultiplierApplyL2_le
            hR i k
            ((MeasureTheory.Lp.fourierTransformₗᵢ
              H3FourierPoint3 ℂ) (F - G))

    _ = ‖F - G‖ := by
      exact
        (MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ).norm_map (F - G)

    _ = 1 * ‖F - G‖ := by
      rw [one_mul]

/--
Fourier transform followed by fixed dyadic localization is continuous on
`L²`.
-/
theorem continuous_h3BKMFourierLocalizedCoordinateMultiplierApplyL2
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    Continuous
      (fun F : H3FourierComplexL2 =>
        h3BKMLocalizedCoordinateMultiplierApplyL2
          R hR i k
          ((MeasureTheory.Lp.fourierTransformₗᵢ
              H3FourierPoint3 ℂ) F)) :=
  (lipschitzWith_h3BKMFourierLocalizedCoordinateMultiplierApplyL2
    hR i k).continuous

end

end Euclidean
end Bridge
end PrimeTensor
