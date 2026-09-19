import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.HighFrequencyGradientQuarterWeight

/-!
# BKM endpoint: explicit dyadic quarter-decay of the high gradient

The previous checkpoint proved that the fixed fractional H³ deweighting weight

    q(ξ) = ‖ξ‖^(5/4) W₃(ξ)⁻¹

belongs to Fourier `L²`.

On the support of the high-frequency factor at upper index `hi` we have

    R_(hi+1) ≤ ‖ξ‖,

so

    R_(hi+1)^(1/4) ≤ ‖ξ‖^(1/4).

Therefore

    ‖ξ‖ W₃(ξ)⁻¹
      ≤ R_(hi+1)^(-1/4)
          ‖ξ‖^(5/4) W₃(ξ)⁻¹.

Combining this with the derivative-symbol bound gives the explicit multiplier
estimate

    ‖m_hi,i‖₂
      ≤ (2π) R_(hi+1)^(-1/4) C_q,

where `C_q` is the fixed quarter-tail `L²` constant.

Finally the already-packaged inverse-Fourier high-gradient estimate inherits
the same coefficient.  This is the quantitative high-frequency input needed
for the logarithmic BKM cutoff selection.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeBKMEndpointHighFrequencyGradientDyadicDecay
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Quarter-tail package representative -/

theorem h3BKMQuarterTailMomentWeightL2_ae :
    (h3BKMQuarterTailMomentWeightL2 :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3BKMQuarterTailMomentWeightComplex := by
  exact
    MemLp.coeFn_toLp
      h3BKMQuarterTailMomentWeightComplex_memLp2

/-! ## Pointwise extraction of the dyadic radius -/

/--
On the high-frequency support, the first H³ Fourier moment is bounded by the
quarter-tail weight with one inverse quarter power of the upper dyadic radius.
-/
theorem h3SobolevFrequencyFirstMomentInv_le_dyadicQuarterTail
    (hi : ℕ)
    (ξ : H3FourierPoint3)
    (hHigh :
      h3BKMDyadicHighFrequencyFactor hi ξ ≠ 0) :
    h3SobolevFrequencyFirstMomentInv ξ
      ≤
    (h3BKMDyadicRadius (hi + 1) ^ ((1 : ℝ) / 4))⁻¹
      *
    h3BKMQuarterTailMomentWeight ξ := by

  let R : ℝ :=
    h3BKMDyadicRadius (hi + 1)
  let r : ℝ :=
    ‖ξ‖

  have hR :
      0 < R := by
    dsimp only [R]
    exact
      h3BKMDyadicRadius_pos (hi + 1)

  have hr :
      0 ≤ r := by
    dsimp only [r]
    exact norm_nonneg _

  have hRle :
      R ≤ r := by
    by_contra hnot
    have hrR :
        r ≤ R := le_of_not_ge hnot
    have hZero :=
      h3BKMDyadicHighFrequencyFactor_eq_zero_of_norm_le
        hi
        (ξ := ξ)
        (by
          simpa only [R, r] using hrR)
    exact hHigh hZero

  have hQuarter :
      R ^ ((1 : ℝ) / 4)
        ≤
      r ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow
      hR.le
      hRle
      (by norm_num)

  have hRQuarterPos :
      0 < R ^ ((1 : ℝ) / 4) :=
    Real.rpow_pos_of_pos
      hR
      ((1 : ℝ) / 4)

  have hFirstNonneg :
      0 ≤ h3SobolevFrequencyFirstMomentInv ξ := by
    unfold
      h3SobolevFrequencyFirstMomentInv
      h3SobolevFrequencyWeightInv
    exact
      mul_nonneg
        (norm_nonneg ξ)
        (inv_nonneg.mpr
          (h3SobolevFrequencyWeight_pos ξ).le)

  have hFiveSplit :
      r ^ ((5 : ℝ) / 4)
        =
      r ^ ((1 : ℝ) / 4) * r := by
    calc
      r ^ ((5 : ℝ) / 4)
          =
        r ^ (((1 : ℝ) / 4) + 1) := by
          congr 1
          ring
      _ =
        r ^ ((1 : ℝ) / 4) * r ^ (1 : ℝ) := by
          rw [
            Real.rpow_add_of_nonneg
              hr
              (by norm_num : 0 ≤ (1 : ℝ) / 4)
              (by norm_num : 0 ≤ (1 : ℝ))
          ]
      _ =
        r ^ ((1 : ℝ) / 4) * r := by
          rw [Real.rpow_one]

  rw [inv_mul_eq_div]

  apply (le_div_iff₀ hRQuarterPos).2

  calc
    h3SobolevFrequencyFirstMomentInv ξ
          *
        R ^ ((1 : ℝ) / 4)
        =
      R ^ ((1 : ℝ) / 4)
          *
        h3SobolevFrequencyFirstMomentInv ξ := by
          ring

    _ ≤
      r ^ ((1 : ℝ) / 4)
          *
        h3SobolevFrequencyFirstMomentInv ξ :=
      mul_le_mul_of_nonneg_right
        hQuarter
        hFirstNonneg

    _ =
      h3BKMQuarterTailMomentWeight ξ := by
        unfold
          h3SobolevFrequencyFirstMomentInv
          h3BKMQuarterTailMomentWeight
        dsimp only [r]
        rw [hFiveSplit]
        ring

/--
Pointwise high-gradient multiplier bound with explicit inverse quarter power of
the upper dyadic radius.
-/
theorem norm_h3BKMHighGradientDeweightingMultiplier_le_dyadicQuarter
    (hi : ℕ)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3BKMHighGradientDeweightingMultiplier hi i ξ‖
      ≤
    ((2 * Real.pi)
      *
    (h3BKMDyadicRadius (hi + 1) ^ ((1 : ℝ) / 4))⁻¹)
      *
    h3BKMQuarterTailMomentWeight ξ := by

  have hQuarterNonneg :
      0 ≤ h3BKMQuarterTailMomentWeight ξ := by
    unfold
      h3BKMQuarterTailMomentWeight
      h3SobolevFrequencyWeightInv
    exact
      mul_nonneg
        (Real.rpow_nonneg (norm_nonneg ξ) _)
        (inv_nonneg.mpr
          (h3SobolevFrequencyWeight_pos ξ).le)

  by_cases hHigh :
      h3BKMDyadicHighFrequencyFactor hi ξ = 0

  · unfold h3BKMHighGradientDeweightingMultiplier
    rw [hHigh]
    simp only [
      Complex.ofReal_zero,
      zero_mul,
      norm_zero
    ]

    exact
      mul_nonneg
        (mul_nonneg
          (by positivity)
          (inv_nonneg.mpr
            (Real.rpow_nonneg
              (h3BKMDyadicRadius_pos (hi + 1)).le
              _)))
        hQuarterNonneg

  · have hFirst :=
      h3SobolevFrequencyFirstMomentInv_le_dyadicQuarterTail
        hi ξ hHigh

    have hTwoPi :
        0 ≤ 2 * Real.pi := by
      positivity

    calc
      ‖h3BKMHighGradientDeweightingMultiplier hi i ξ‖
          ≤
        (2 * Real.pi)
          *
        h3SobolevFrequencyFirstMomentInv ξ :=
        norm_h3BKMHighGradientDeweightingMultiplier_le
          hi i ξ

      _ ≤
        (2 * Real.pi)
          *
        ((h3BKMDyadicRadius (hi + 1) ^ ((1 : ℝ) / 4))⁻¹
          *
        h3BKMQuarterTailMomentWeight ξ) :=
        mul_le_mul_of_nonneg_left
          hFirst
          hTwoPi

      _ =
        ((2 * Real.pi)
          *
        (h3BKMDyadicRadius (hi + 1) ^ ((1 : ℝ) / 4))⁻¹)
          *
        h3BKMQuarterTailMomentWeight ξ := by
          ring

/-! ## Bundled L² dyadic decay -/

/--
The `L²` norm of the high-gradient deweighting multiplier decays by an explicit
inverse quarter power of the upper dyadic radius.
-/
theorem norm_h3BKMHighGradientDeweightingMultiplierL2_le_dyadicQuarter
    (hi : ℕ)
    (i : Fin 3) :
    ‖h3BKMHighGradientDeweightingMultiplierL2 hi i‖
      ≤
    ((2 * Real.pi)
      *
    (h3BKMDyadicRadius (hi + 1) ^ ((1 : ℝ) / 4))⁻¹)
      *
    h3BKMQuarterTailMomentConstant := by

  apply
    MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul

  filter_upwards [
    h3BKMHighGradientDeweightingMultiplierL2_ae hi i,
    h3BKMQuarterTailMomentWeightL2_ae
  ] with ξ hHigh hQuarter

  rw [hHigh, hQuarter]

  have hQuarterNonneg :
      0 ≤ h3BKMQuarterTailMomentWeight ξ := by
    unfold
      h3BKMQuarterTailMomentWeight
      h3SobolevFrequencyWeightInv
    exact
      mul_nonneg
        (Real.rpow_nonneg (norm_nonneg ξ) _)
        (inv_nonneg.mpr
          (h3SobolevFrequencyWeight_pos ξ).le)

  have hPoint :=
    norm_h3BKMHighGradientDeweightingMultiplier_le_dyadicQuarter
      hi i ξ

  simpa [
    h3BKMQuarterTailMomentWeightComplex,
    h3BKMQuarterTailMomentConstant,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hQuarterNonneg
  ] using hPoint

/-! ## Quantitative inverse-Fourier high-gradient estimate -/

/--
The high-frequency inverse-Fourier gradient contribution has the same explicit
dyadic quarter decay against the weighted H³ norm.
-/
theorem norm_fourierInv_h3BKMHighGradientAmplitude_le_dyadicQuarter
    (hi : ℕ)
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖FourierTransformInv.fourierInv
        (h3BKMHighGradientAmplitude hi G i)
        x‖
      ≤
    (((2 * Real.pi)
        *
      (h3BKMDyadicRadius (hi + 1) ^ ((1 : ℝ) / 4))⁻¹)
        *
      h3BKMQuarterTailMomentConstant)
      *
    ‖G‖ := by

  have hBase :=
    norm_fourierInv_h3BKMHighGradientAmplitude_le_multiplierL2
      hi G i x

  have hMultiplier :=
    norm_h3BKMHighGradientDeweightingMultiplierL2_le_dyadicQuarter
      hi i

  calc
    ‖FourierTransformInv.fourierInv
        (h3BKMHighGradientAmplitude hi G i)
        x‖
        ≤
      ‖h3BKMHighGradientDeweightingMultiplierL2 hi i‖
        *
      ‖G‖ :=
      hBase

    _ ≤
      (((2 * Real.pi)
          *
        (h3BKMDyadicRadius (hi + 1) ^ ((1 : ℝ) / 4))⁻¹)
          *
        h3BKMQuarterTailMomentConstant)
        *
      ‖G‖ :=
      mul_le_mul_of_nonneg_right
        hMultiplier
        (norm_nonneg G)

end

end Euclidean
end Bridge
end PrimeTensor
