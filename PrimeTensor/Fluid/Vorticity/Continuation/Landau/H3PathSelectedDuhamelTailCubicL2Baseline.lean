import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedHighRadialDuhamelTailL2Frontier

/-!
# Automatic cubic radial L² baseline for selected Duhamel tails

The remaining terminal-tail frontier asks for fourth and fifth radial Fourier
weights in `L²`.  Before bootstrapping those two extra levels, record the exact
baseline already present in every H³ spectral state.

The exact solver weight is

    W₃(ξ)² = 1 + q + q² + q³,
    q = (2π)² ‖ξ‖².

Hence `W₃(ξ)` dominates `‖ξ‖³`.  Since the canonical raw representative is

    raw(G)(ξ) = W₃(ξ)⁻¹ G(ξ),

every H³ spectral scalar state automatically satisfies

    ‖ξ‖³ raw(G)(ξ) ∈ L².

Applying this to the selected terminal Duhamel tail shows that the unresolved
high-frequency problem starts exactly one derivative above the native H³
topology:

    cubic tail L²       automatic,
    fourth tail L²      first gain,
    fifth tail L²       second gain.

This is the base input for the weighted `L¹ * L² → L²` convolution bootstrap.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedDuhamelTailCubicL2Baseline
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## The exact H³ weight dominates the cubic radial weight -/

/--
The exact H³ Sobolev frequency weight dominates the unnormalized cubic radial
weight.  The Fourier derivative normalization `(2π)` only makes the H³ weight
larger.
-/
theorem h3FourierNorm_cubed_le_h3SobolevFrequencyWeight
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 3 ≤ h3SobolevFrequencyWeight ξ := by

  let r : ℝ := ‖ξ‖
  let c : ℝ := 2 * Real.pi
  let q : ℝ := h3FourierGradientSquare ξ
  let W : ℝ := h3SobolevFrequencyWeight ξ
  let S : ℝ := h3SobolevFrequencyWeightSq ξ

  have hr0 : 0 ≤ r := by
    dsimp only [r]
    exact norm_nonneg ξ

  have hc1 : 1 ≤ c := by
    dsimp only [c]
    nlinarith [Real.pi_gt_three]

  have hc0 : 0 ≤ c := le_trans zero_le_one hc1

  have hc3 : 1 ≤ c ^ 3 := by
    exact one_le_pow₀ hc1

  have hq0 : 0 ≤ q := by
    dsimp only [q]
    exact h3FourierGradientSquare_nonneg ξ

  have hS0 : 0 ≤ S := by
    dsimp only [S]
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (one_le_h3SobolevFrequencyWeightSq ξ)

  have hW0 : 0 ≤ W := by
    dsimp only [W, h3SobolevFrequencyWeight]
    exact Real.sqrt_nonneg _

  have hWsq : W ^ 2 = S := by
    dsimp only [W, S, h3SobolevFrequencyWeight]
    exact Real.sq_sqrt hS0

  have hqdef :
      q = c ^ 2 * r ^ 2 := by
    dsimp only [q, c, r, h3FourierGradientSquare]

  have hq3_le : q ^ 3 ≤ S := by
    dsimp only [S, h3SobolevFrequencyWeightSq]
    nlinarith [
      hq0,
      sq_nonneg q
    ]

  have hscaled_sq :
      (c ^ 3 * r ^ 3) ^ 2 = q ^ 3 := by
    rw [hqdef]
    ring

  have hscaled0 :
      0 ≤ c ^ 3 * r ^ 3 := by
    positivity

  have hscaled_le :
      c ^ 3 * r ^ 3 ≤ W := by
    have hsq :
        (c ^ 3 * r ^ 3) ^ 2 ≤ W ^ 2 := by
      rw [hscaled_sq, hWsq]
      exact hq3_le
    nlinarith

  have hr3_le_scaled :
      r ^ 3 ≤ c ^ 3 * r ^ 3 := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right
        hc3
        (pow_nonneg hr0 3))

  exact
    hr3_le_scaled.trans hscaled_le

/--
The cubic radial factor times the inverse exact H³ weight is bounded by one.
-/
theorem h3FourierNorm_cubed_mul_h3SobolevFrequencyWeightInv_le_one
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 3 * h3SobolevFrequencyWeightInv ξ ≤ 1 := by

  have hWeight :
      ‖ξ‖ ^ 3 ≤ h3SobolevFrequencyWeight ξ :=
    h3FourierNorm_cubed_le_h3SobolevFrequencyWeight ξ

  have hInv0 :
      0 ≤ h3SobolevFrequencyWeightInv ξ := by
    unfold h3SobolevFrequencyWeightInv
    exact
      inv_nonneg.mpr
        (h3SobolevFrequencyWeight_pos ξ).le

  have hMul :=
    mul_le_mul_of_nonneg_right
      hWeight
      hInv0

  calc
    ‖ξ‖ ^ 3 * h3SobolevFrequencyWeightInv ξ
        ≤
      h3SobolevFrequencyWeight ξ *
        h3SobolevFrequencyWeightInv ξ :=
      hMul
    _ = 1 := by
      unfold h3SobolevFrequencyWeightInv
      exact
        mul_inv_cancel₀
          (ne_of_gt
            (h3SobolevFrequencyWeight_pos ξ))

/-! ## Every H³ spectral state has cubic raw Fourier L² -/

/--
The canonical raw Fourier representative of every H³ spectral scalar state has
cubic radial weight in `L²`.
-/
theorem h3SpectralScalarRawFourier_cubicWeight_memLp2
    (G : H3SpectralScalarState) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 3 : ℝ) : ℂ) *
          h3SpectralScalarRawFourier G ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 3 : ℝ) : ℂ) *
            h3SpectralScalarRawFourier G ξ)
        (volume : Measure H3FourierPoint3) := by
    exact
      (Complex.continuous_ofReal.comp
        (continuous_norm.pow 3)).aestronglyMeasurable.mul
        (h3SpectralScalarRawFourier_memLp2 G).1

  refine
    (MeasureTheory.Lp.memLp G).of_le
      hMeas
      ?_

  filter_upwards with ξ

  have hr3 :
      0 ≤ ‖ξ‖ ^ 3 :=
    pow_nonneg (norm_nonneg ξ) 3

  have hInv0 :
      0 ≤ h3SobolevFrequencyWeightInv ξ := by
    unfold h3SobolevFrequencyWeightInv
    exact
      inv_nonneg.mpr
        (h3SobolevFrequencyWeight_pos ξ).le

  have hMultiplier :
      ‖ξ‖ ^ 3 *
          h3SobolevFrequencyWeightInv ξ
        ≤
      1 :=
    h3FourierNorm_cubed_mul_h3SobolevFrequencyWeightInv_le_one ξ

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hr3,
    h3SpectralScalarRawFourier,
    h3SobolevFrequencyWeightInvComplex,
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hInv0
  ]

  calc
    ‖ξ‖ ^ 3 *
        (h3SobolevFrequencyWeightInv ξ * ‖G ξ‖)
        =
      (‖ξ‖ ^ 3 *
        h3SobolevFrequencyWeightInv ξ) *
        ‖G ξ‖ := by
          ring
    _ ≤ 1 * ‖G ξ‖ :=
      mul_le_mul_of_nonneg_right
        hMultiplier
        (norm_nonneg _)
    _ = ‖G ξ‖ := by
      rw [one_mul]

/-! ## Selected terminal tails inherit the cubic baseline -/

/--
Every selected terminal Duhamel tail has cubic radial raw Fourier `L²`
automatically.  No positive-lag estimate beyond the fact that the tail is an
H³ spectral state is needed.
-/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_cubicWeight_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 3 : ℝ) : ℂ) *
          (((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
              (t := t) hν U₀ hA hU₀ i :
            H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ))
      2
      (volume : Measure H3FourierPoint3) := by

  let G : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamelSelectedTail
      (t := t) hν U₀ hA hU₀ i

  have hBase :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 3 : ℝ) : ℂ) *
            h3SpectralScalarRawFourier G ξ)
        2
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarRawFourier_cubicWeight_memLp2 G

  have hRep :
      ((h3SpectralScalarRawFourierL2 G :
          H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourier G :=
    h3SpectralScalarRawFourierL2_ae G

  have hWeighted :
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 3 : ℝ) : ℂ) *
          (((h3SpectralScalarRawFourierL2 G :
              H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ))
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 3 : ℝ) : ℂ) *
          h3SpectralScalarRawFourier G ξ) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  change
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 3 : ℝ) : ℂ) *
          (((h3SpectralScalarRawFourierL2 G :
              H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ))
      2
      (volume : Measure H3FourierPoint3)

  exact
    (memLp_congr_ae hWeighted).2 hBase

/-!
The active frontier in
`H3PathSelectedHighRadialDuhamelTailL2Frontier` therefore begins immediately
above this theorem: order four is the first non-native `L²` gain, and order
five is the second.
-/

end

end Euclidean
end Bridge
end PrimeTensor
