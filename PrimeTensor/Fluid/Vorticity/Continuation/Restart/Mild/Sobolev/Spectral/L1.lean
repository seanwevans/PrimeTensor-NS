import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Heat.Smoothing
import PrimeTensor.Fluid.Vorticity.H3.Axis.Sum
import Mathlib.Analysis.Distribution.Sobolev

/-!
# Weighted H³ spectral states deweight to Fourier `L¹`

The nonlinear Sobolev algebra estimate will be proved in Fourier variables.

A scalar solver state stores

    G(ξ) = W₃(ξ) * f̂(ξ)

in complex `L²`, where

    W₃(ξ)² = 1 + q + q² + q³,
    q = (2π)² ‖ξ‖².

To use Young convolution estimates we first need the raw Fourier amplitude
`f̂ = W₃⁻¹ G` in `L¹`.

The analytic input is the standard Japanese-bracket fact that

    (1 + ‖ξ‖²)⁻¹ ∈ L²(R³).

Our custom exact H³ weight is stronger:

    1 + ‖ξ‖² ≤ W₃(ξ).

Hence `W₃⁻¹ ∈ L²`, and Hölder (`L² * L² → L¹`) gives

    W₃⁻¹ G ∈ L¹.

This is the Sobolev-embedding kernel needed for the subsequent weighted
convolution / H³ algebra theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SpectralL1
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## The exact H³ weight dominates a standard Japanese bracket -/

/--
The Fourier gradient square dominates twice the unscaled Euclidean
frequency square.
-/
theorem two_mul_norm_sq_le_h3FourierGradientSquare
    (ξ : H3FourierPoint3) :
    2 * ‖ξ‖ ^ 2
      ≤
    h3FourierGradientSquare ξ := by
  have hpi : (3 : ℝ) < Real.pi :=
    Real.pi_gt_three
  have hc :
      (2 : ℝ) ≤ (2 * Real.pi) ^ 2 := by
    nlinarith [sq_nonneg (Real.pi - 3)]
  unfold h3FourierGradientSquare
  exact
    mul_le_mul_of_nonneg_right
      hc
      (sq_nonneg ‖ξ‖)

/--
The exact polynomial H³ weight-square dominates the square of
`1 + ‖ξ‖²`.
-/
theorem one_add_norm_sq_sq_le_h3SobolevFrequencyWeightSq
    (ξ : H3FourierPoint3) :
    (1 + ‖ξ‖ ^ 2) ^ 2
      ≤
    h3SobolevFrequencyWeightSq ξ := by
  let r : ℝ := ‖ξ‖ ^ 2
  let q : ℝ := h3FourierGradientSquare ξ

  have hr : 0 ≤ r := by
    dsimp [r]
    positivity

  have hq : 0 ≤ q := by
    dsimp [q]
    exact h3FourierGradientSquare_nonneg ξ

  have h2r_le_q : 2 * r ≤ q := by
    dsimp [r, q]
    exact two_mul_norm_sq_le_h3FourierGradientSquare ξ

  have hr_le_q : r ≤ q := by
    linarith

  have hr2_le_q2 : r ^ 2 ≤ q ^ 2 := by
    rw [sq_le_sq]
    simpa [
      abs_of_nonneg hr,
      abs_of_nonneg hq
    ] using hr_le_q

  have hq3 : 0 ≤ q ^ 3 := by
    positivity

  change
    (1 + r) ^ 2
      ≤
    1 + q + q ^ 2 + q ^ 3

  nlinarith

/--
The exact H³ frequency weight dominates `1 + ‖ξ‖²`.
-/
theorem one_add_norm_sq_le_h3SobolevFrequencyWeight
    (ξ : H3FourierPoint3) :
    1 + ‖ξ‖ ^ 2
      ≤
    h3SobolevFrequencyWeight ξ := by
  have hSq :
      (1 + ‖ξ‖ ^ 2) ^ 2
        ≤
      (h3SobolevFrequencyWeight ξ) ^ 2 := by
    rw [h3SobolevFrequencyWeight_sq]
    exact
      one_add_norm_sq_sq_le_h3SobolevFrequencyWeightSq ξ

  have hAbs :=
    (sq_le_sq).mp hSq

  have hLeft :
      0 ≤ 1 + ‖ξ‖ ^ 2 := by
    positivity

  have hRight :
      0 ≤ h3SobolevFrequencyWeight ξ :=
    (h3SobolevFrequencyWeight_pos ξ).le

  simpa [
    abs_of_nonneg hLeft,
    abs_of_nonneg hRight
  ] using hAbs

/-! ## Standard inverse Japanese bracket in `L²(R³)` -/

/-- The standard order-two inverse Bessel weight. -/
def h3StandardInverseBesselWeight
    (ξ : H3FourierPoint3) : ℝ :=
  (1 + ‖ξ‖ ^ 2)⁻¹

/-- The standard inverse weight is continuous. -/
theorem continuous_h3StandardInverseBesselWeight :
    Continuous h3StandardInverseBesselWeight := by
  unfold h3StandardInverseBesselWeight
  exact
    (continuous_const.add (continuous_norm.pow 2)).inv₀
      (fun ξ => by
        have hPos :
            0 < 1 + ‖ξ‖ ^ 2 := by
          nlinarith [sq_nonneg ‖ξ‖]
        exact ne_of_gt hPos)

/--
The Fourier carrier really has dimension three.

This is kept as a named lemma because the generic Mathlib Japanese-bracket
integrability theorem is dimension-parametric.
-/
theorem h3FourierPoint3_finrank :
    Module.finrank ℝ H3FourierPoint3 = 3 := by
  change
    Module.finrank ℝ
      (EuclideanSpace ℝ (PrimeTensor.Axis Depth.three))
      =
    3

  rw [finrank_euclideanSpace]

  simpa using
    (axis_sum_three
      (fun _ : PrimeTensor.Axis Depth.three => (1 : ℕ)))

/--
`(1 + ‖ξ‖²)⁻¹` belongs to `L²` in three spatial dimensions.
-/
theorem h3StandardInverseBesselWeight_memLp2 :
    MemLp
      h3StandardInverseBesselWeight
      2
      (volume : Measure H3FourierPoint3) := by
  have hs :
      (Module.finrank ℝ H3FourierPoint3 : ℝ)
        <
      (4 : ℝ) := by
    rw [h3FourierPoint3_finrank]
    norm_num

  have hInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(4 : ℝ) / 2))
        volume :=
    integrable_rpow_neg_one_add_norm_sq hs

  have hMeas :
      AEStronglyMeasurable
        h3StandardInverseBesselWeight
        volume :=
    continuous_h3StandardInverseBesselWeight.aestronglyMeasurable

  rw [memLp_two_iff_integrable_sq_norm hMeas]

  refine hInt.congr ?_

  filter_upwards with ξ

  have hb :
      0 < (1 : ℝ) + ‖ξ‖ ^ 2 := by
    positivity

  unfold h3StandardInverseBesselWeight
  rw [
    Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hb)
  ]

  rw [show
    ((1 + ‖ξ‖ ^ 2)⁻¹) ^ 2
      =
    ((1 + ‖ξ‖ ^ 2) ^ (-(4 : ℝ) / 2)) by
      rw [show (-(4 : ℝ) / 2) = (-2 : ℝ) by norm_num]
      rw [Real.rpow_neg (le_of_lt hb)]
      norm_num]

/-! ## The exact inverse weight is also `L²` -/

/-- Reciprocal of the exact H³ spectral frequency weight. -/
def h3SobolevFrequencyWeightInv
    (ξ : H3FourierPoint3) : ℝ :=
  (h3SobolevFrequencyWeight ξ)⁻¹

/-- The exact inverse H³ weight is continuous. -/
theorem continuous_h3SobolevFrequencyWeightInv :
    Continuous h3SobolevFrequencyWeightInv := by
  unfold h3SobolevFrequencyWeightInv
  exact
    continuous_h3SobolevFrequencyWeight.inv₀
      (fun ξ =>
        ne_of_gt (h3SobolevFrequencyWeight_pos ξ))

/-- Pointwise comparison of the exact inverse weight with the standard one. -/
theorem h3SobolevFrequencyWeightInv_le_standard
    (ξ : H3FourierPoint3) :
    h3SobolevFrequencyWeightInv ξ
      ≤
    h3StandardInverseBesselWeight ξ := by
  unfold
    h3SobolevFrequencyWeightInv
    h3StandardInverseBesselWeight

  have hBase :
      0 < 1 + ‖ξ‖ ^ 2 := by
    positivity

  simpa [one_div] using
    one_div_le_one_div_of_le
      hBase
      (one_add_norm_sq_le_h3SobolevFrequencyWeight ξ)

/-- The exact reciprocal H³ weight belongs to real `L²`. -/
theorem h3SobolevFrequencyWeightInv_memLp2 :
    MemLp
      h3SobolevFrequencyWeightInv
      2
      (volume : Measure H3FourierPoint3) := by
  apply
    h3StandardInverseBesselWeight_memLp2.of_le
      continuous_h3SobolevFrequencyWeightInv.aestronglyMeasurable

  filter_upwards with ξ

  have hInvNonneg :
      0 ≤ h3SobolevFrequencyWeightInv ξ := by
    unfold h3SobolevFrequencyWeightInv
    exact inv_nonneg.mpr
      (h3SobolevFrequencyWeight_pos ξ).le

  have hStdNonneg :
      0 ≤ h3StandardInverseBesselWeight ξ := by
    unfold h3StandardInverseBesselWeight
    positivity

  simpa [
    Real.norm_eq_abs,
    abs_of_nonneg hInvNonneg,
    abs_of_nonneg hStdNonneg
  ] using
    h3SobolevFrequencyWeightInv_le_standard ξ

/-- Complex-valued copy of the exact reciprocal H³ weight. -/
def h3SobolevFrequencyWeightInvComplex
    (ξ : H3FourierPoint3) : ℂ :=
  h3SobolevFrequencyWeightInv ξ

/-- The complex reciprocal weight is in `L²`. -/
theorem h3SobolevFrequencyWeightInvComplex_memLp2 :
    MemLp
      h3SobolevFrequencyWeightInvComplex
      2
      (volume : Measure H3FourierPoint3) := by
  exact
    h3SobolevFrequencyWeightInv_memLp2.ofReal

/-! ## Deweighting a spectral H³ state produces Fourier `L¹` -/

/--
Raw Fourier amplitude represented by a weighted spectral scalar state.

If `G = W₃ f̂`, this is exactly `f̂`.
-/
def h3SpectralScalarRawFourier
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℂ :=
  h3SobolevFrequencyWeightInvComplex ξ * G ξ

/--
The deweighted raw Fourier amplitude is `L¹`.

This is precisely Hölder `L² * L² → L¹`.
-/
theorem h3SpectralScalarRawFourier_memLp1
    (G : H3SpectralScalarState) :
    MemLp
      (h3SpectralScalarRawFourier G)
      1
      (volume : Measure H3FourierPoint3) := by
  change
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3SobolevFrequencyWeightInvComplex ξ * G ξ)
      1
      volume

  exact
    (MeasureTheory.Lp.memLp G).mul'
      h3SobolevFrequencyWeightInvComplex_memLp2

/-- Canonical `L¹` package of the raw Fourier amplitude. -/
noncomputable def h3SpectralScalarRawFourierL1
    (G : H3SpectralScalarState) :
    MeasureTheory.Lp
      ℂ
      1
      (volume : Measure H3FourierPoint3) :=
  (h3SpectralScalarRawFourier_memLp1 G).toLp
    (h3SpectralScalarRawFourier G)

/-- The packaged `L¹` function represents the expected deweighted amplitude. -/
theorem h3SpectralScalarRawFourierL1_ae
    (G : H3SpectralScalarState) :
    (h3SpectralScalarRawFourierL1 G :
        H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    h3SpectralScalarRawFourier G := by
  exact
    MemLp.coeFn_toLp
      (h3SpectralScalarRawFourier_memLp1 G)

/--
Deweighting and immediately reweighting recovers the original spectral state
almost everywhere.
-/
theorem h3SpectralScalarRawFourier_reweight_ae
    (G : H3SpectralScalarState) :
    (fun ξ : H3FourierPoint3 =>
      (h3SobolevFrequencyWeight ξ : ℂ) *
        h3SpectralScalarRawFourier G ξ)
      =ᵐ[volume]
    (G : H3FourierPoint3 → ℂ) := by
  filter_upwards with ξ

  unfold
    h3SpectralScalarRawFourier
    h3SobolevFrequencyWeightInvComplex

  have hW :
      h3SobolevFrequencyWeight ξ ≠ 0 :=
    ne_of_gt (h3SobolevFrequencyWeight_pos ξ)

  have hReal :
      h3SobolevFrequencyWeight ξ *
          h3SobolevFrequencyWeightInv ξ
        =
      (1 : ℝ) := by
    unfold h3SobolevFrequencyWeightInv
    exact mul_inv_cancel₀ hW

  have hComplex :
      (h3SobolevFrequencyWeight ξ : ℂ) *
          (h3SobolevFrequencyWeightInv ξ : ℂ)
        =
      (1 : ℂ) := by
    exact_mod_cast hReal

  rw [← mul_assoc, hComplex, one_mul]

end

end Euclidean
end Bridge
end PrimeTensor
