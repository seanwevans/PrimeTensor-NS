import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.FrequencyTrichotomySupport

/-!
# BKM endpoint: quantitative bounds for the exact frequency trichotomy

The exact low / middle / high decomposition is now available together with its
support geometry.  This file records the uniform multiplier bounds needed by
the next analytic step.

Each real-valued factor lies in `[0,1]`.  Consequently multiplication by any
of the three factors is pointwise contractive on complex Fourier amplitudes:

    ‖m(ξ) z‖ ≤ ‖z‖.

These simple facts are the reusable domination input for the low- and
high-frequency `L¹` / inverse-Fourier estimates.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointFrequencyTrichotomyBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Real multiplier bounds -/

theorem h3BKMDyadicLowFrequencyFactor_nonneg
    (lo : ℕ)
    (ξ : H3FourierPoint3) :
    0 ≤ h3BKMDyadicLowFrequencyFactor lo ξ := by

  unfold h3BKMDyadicLowFrequencyFactor

  exact
    h3BKMFrequencyCutoffBump_nonneg
      (h3BKMDyadicRadius_pos lo)
      ξ

theorem h3BKMDyadicLowFrequencyFactor_le_one
    (lo : ℕ)
    (ξ : H3FourierPoint3) :
    h3BKMDyadicLowFrequencyFactor lo ξ ≤ 1 := by

  unfold h3BKMDyadicLowFrequencyFactor

  exact
    h3BKMFrequencyCutoffBump_le_one
      (h3BKMDyadicRadius_pos lo)
      ξ

theorem h3BKMDyadicHighFrequencyFactor_nonneg
    (hi : ℕ)
    (ξ : H3FourierPoint3) :
    0 ≤ h3BKMDyadicHighFrequencyFactor hi ξ := by

  unfold h3BKMDyadicHighFrequencyFactor

  exact
    sub_nonneg.mpr
      (
        h3BKMFrequencyCutoffBump_le_one
          (h3BKMDyadicRadius_pos (hi + 1))
          ξ
      )

theorem h3BKMDyadicHighFrequencyFactor_le_one
    (hi : ℕ)
    (ξ : H3FourierPoint3) :
    h3BKMDyadicHighFrequencyFactor hi ξ ≤ 1 := by

  unfold h3BKMDyadicHighFrequencyFactor

  have hCutoff :
      0
        ≤
      h3BKMFrequencyCutoffBump
        (h3BKMDyadicRadius (hi + 1))
        (h3BKMDyadicRadius_pos (hi + 1))
        ξ :=
    h3BKMFrequencyCutoffBump_nonneg
      (h3BKMDyadicRadius_pos (hi + 1))
      ξ

  linarith

theorem h3BKMDyadicMiddleFrequencyFactor_nonneg
    (lo hi : ℕ)
    (ξ : H3FourierPoint3) :
    0 ≤ h3BKMDyadicMiddleFrequencyFactor lo hi ξ := by

  unfold h3BKMDyadicMiddleFrequencyFactor

  apply Finset.sum_nonneg
  intro n hn

  exact
    h3BKMFrequencyShell_nonneg
      (h3BKMDyadicRadius_pos n)
      ξ

theorem h3BKMDyadicMiddleFrequencyFactor_le_one
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (ξ : H3FourierPoint3) :
    h3BKMDyadicMiddleFrequencyFactor lo hi ξ ≤ 1 := by

  have hPart :=
    h3BKMDyadicFrequencyTrichotomy_named_eq_one
      hlohi ξ

  have hLow :
      0 ≤ h3BKMDyadicLowFrequencyFactor lo ξ :=
    h3BKMDyadicLowFrequencyFactor_nonneg
      lo ξ

  have hHigh :
      0 ≤ h3BKMDyadicHighFrequencyFactor hi ξ :=
    h3BKMDyadicHighFrequencyFactor_nonneg
      hi ξ

  linarith

/-! ## Complex norm bounds -/

theorem norm_coe_h3BKMDyadicLowFrequencyFactor_le_one
    (lo : ℕ)
    (ξ : H3FourierPoint3) :
    ‖(h3BKMDyadicLowFrequencyFactor lo ξ : ℂ)‖ ≤ 1 := by

  rw [
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg
      (h3BKMDyadicLowFrequencyFactor_nonneg lo ξ)
  ]

  exact
    h3BKMDyadicLowFrequencyFactor_le_one
      lo ξ

theorem norm_coe_h3BKMDyadicMiddleFrequencyFactor_le_one
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (ξ : H3FourierPoint3) :
    ‖(h3BKMDyadicMiddleFrequencyFactor lo hi ξ : ℂ)‖ ≤ 1 := by

  rw [
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg
      (h3BKMDyadicMiddleFrequencyFactor_nonneg lo hi ξ)
  ]

  exact
    h3BKMDyadicMiddleFrequencyFactor_le_one
      hlohi ξ

theorem norm_coe_h3BKMDyadicHighFrequencyFactor_le_one
    (hi : ℕ)
    (ξ : H3FourierPoint3) :
    ‖(h3BKMDyadicHighFrequencyFactor hi ξ : ℂ)‖ ≤ 1 := by

  rw [
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg
      (h3BKMDyadicHighFrequencyFactor_nonneg hi ξ)
  ]

  exact
    h3BKMDyadicHighFrequencyFactor_le_one
      hi ξ

/-! ## Pointwise contraction bounds -/

theorem norm_h3BKMDyadicLowFrequencyFactor_mul_le
    (lo : ℕ)
    (ξ : H3FourierPoint3)
    (z : ℂ) :
    ‖(h3BKMDyadicLowFrequencyFactor lo ξ : ℂ) * z‖
      ≤
    ‖z‖ := by

  rw [norm_mul]

  calc
    ‖(h3BKMDyadicLowFrequencyFactor lo ξ : ℂ)‖ * ‖z‖
        ≤
      1 * ‖z‖ := by
        exact
          mul_le_mul_of_nonneg_right
            (norm_coe_h3BKMDyadicLowFrequencyFactor_le_one
              lo ξ)
            (norm_nonneg z)

    _ = ‖z‖ := by
      ring

theorem norm_h3BKMDyadicMiddleFrequencyFactor_mul_le
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (ξ : H3FourierPoint3)
    (z : ℂ) :
    ‖(h3BKMDyadicMiddleFrequencyFactor lo hi ξ : ℂ) * z‖
      ≤
    ‖z‖ := by

  rw [norm_mul]

  calc
    ‖(h3BKMDyadicMiddleFrequencyFactor lo hi ξ : ℂ)‖ * ‖z‖
        ≤
      1 * ‖z‖ := by
        exact
          mul_le_mul_of_nonneg_right
            (norm_coe_h3BKMDyadicMiddleFrequencyFactor_le_one
              hlohi ξ)
            (norm_nonneg z)

    _ = ‖z‖ := by
      ring

theorem norm_h3BKMDyadicHighFrequencyFactor_mul_le
    (hi : ℕ)
    (ξ : H3FourierPoint3)
    (z : ℂ) :
    ‖(h3BKMDyadicHighFrequencyFactor hi ξ : ℂ) * z‖
      ≤
    ‖z‖ := by

  rw [norm_mul]

  calc
    ‖(h3BKMDyadicHighFrequencyFactor hi ξ : ℂ)‖ * ‖z‖
        ≤
      1 * ‖z‖ := by
        exact
          mul_le_mul_of_nonneg_right
            (norm_coe_h3BKMDyadicHighFrequencyFactor_le_one
              hi ξ)
            (norm_nonneg z)

    _ = ‖z‖ := by
      ring

end

end Euclidean
end Bridge
end PrimeTensor
