import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Frequency.Trichotomy

/-!
# BKM endpoint: support geometry of the exact frequency trichotomy

`FrequencyTrichotomy` decomposes every canonical Fourier gradient mode into

    low + middle + high.

This file records the exact geometric behavior of those three multipliers.

For the lower dyadic endpoint `R_lo`:

* the low factor is exactly one on `‖ξ‖ ≤ R_lo`;
* the low factor is exactly zero once `2 R_lo ≤ ‖ξ‖`.

For the upper dyadic endpoint `R_(hi+1)`:

* the high factor is exactly zero on `‖ξ‖ ≤ R_(hi+1)`;
* the high factor is exactly one once `2 R_(hi+1) ≤ ‖ξ‖`.

The middle factor is named explicitly as the finite shell sum.  By telescoping,

    middle = χ_(R_(hi+1)) - χ_(R_lo),

and it is exactly one throughout the interior annulus

    R_(lo+1) ≤ ‖ξ‖ ≤ R_(hi+1).

These are the support facts needed for the subsequent low- and high-frequency
pointwise estimates.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointFrequencyTrichotomySupport
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The finite middle-frequency multiplier in the exact BKM trichotomy. -/
noncomputable def h3BKMDyadicMiddleFrequencyFactor
    (lo hi : ℕ)
    (ξ : H3FourierPoint3) :
    ℝ :=
  ∑ n ∈ Finset.Icc lo hi,
    h3BKMFrequencyShell
      (h3BKMDyadicRadius n)
      (h3BKMDyadicRadius_pos n)
      ξ

/-- The low factor is one on its inner dyadic ball. -/
theorem h3BKMDyadicLowFrequencyFactor_eq_one_of_norm_le
    (lo : ℕ)
    {ξ : H3FourierPoint3}
    (hξ :
      ‖ξ‖ ≤ h3BKMDyadicRadius lo) :
    h3BKMDyadicLowFrequencyFactor lo ξ
      =
    1 := by

  unfold h3BKMDyadicLowFrequencyFactor

  exact
    h3BKMFrequencyCutoffBump_eq_one_of_norm_le
      (h3BKMDyadicRadius_pos lo)
      hξ

/-- The low factor vanishes outside twice its dyadic radius. -/
theorem h3BKMDyadicLowFrequencyFactor_eq_zero_of_two_mul_le_norm
    (lo : ℕ)
    {ξ : H3FourierPoint3}
    (hξ :
      2 * h3BKMDyadicRadius lo ≤ ‖ξ‖) :
    h3BKMDyadicLowFrequencyFactor lo ξ
      =
    0 := by

  unfold h3BKMDyadicLowFrequencyFactor

  exact
    h3BKMFrequencyCutoffBump_eq_zero_of_two_mul_le_norm
      (h3BKMDyadicRadius_pos lo)
      hξ

/-- The high factor vanishes on the upper inner dyadic ball. -/
theorem h3BKMDyadicHighFrequencyFactor_eq_zero_of_norm_le
    (hi : ℕ)
    {ξ : H3FourierPoint3}
    (hξ :
      ‖ξ‖ ≤ h3BKMDyadicRadius (hi + 1)) :
    h3BKMDyadicHighFrequencyFactor hi ξ
      =
    0 := by

  unfold h3BKMDyadicHighFrequencyFactor

  rw [
    h3BKMFrequencyCutoffBump_eq_one_of_norm_le
      (h3BKMDyadicRadius_pos (hi + 1))
      hξ
  ]

  ring

/-- The high factor is one beyond twice the upper dyadic radius. -/
theorem h3BKMDyadicHighFrequencyFactor_eq_one_of_two_mul_le_norm
    (hi : ℕ)
    {ξ : H3FourierPoint3}
    (hξ :
      2 * h3BKMDyadicRadius (hi + 1) ≤ ‖ξ‖) :
    h3BKMDyadicHighFrequencyFactor hi ξ
      =
    1 := by

  unfold h3BKMDyadicHighFrequencyFactor

  rw [
    h3BKMFrequencyCutoffBump_eq_zero_of_two_mul_le_norm
      (h3BKMDyadicRadius_pos (hi + 1))
      hξ
  ]

  ring

/-- The named middle factor is exactly the telescoping cutoff difference. -/
theorem h3BKMDyadicMiddleFrequencyFactor_eq_cutoff_sub
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (ξ : H3FourierPoint3) :
    h3BKMDyadicMiddleFrequencyFactor lo hi ξ
      =
    h3BKMFrequencyCutoffBump
        (h3BKMDyadicRadius (hi + 1))
        (h3BKMDyadicRadius_pos (hi + 1))
        ξ
      -
    h3BKMFrequencyCutoffBump
        (h3BKMDyadicRadius lo)
        (h3BKMDyadicRadius_pos lo)
        ξ := by

  unfold h3BKMDyadicMiddleFrequencyFactor

  exact
    h3BKMDyadicFrequencyShell_sum_Icc_eq_cutoff_sub
      hlohi ξ

/-- The named middle factor is exactly one on the interior dyadic annulus. -/
theorem h3BKMDyadicMiddleFrequencyFactor_eq_one
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    {ξ : H3FourierPoint3}
    (hLower :
      h3BKMDyadicRadius (lo + 1) ≤ ‖ξ‖)
    (hUpper :
      ‖ξ‖ ≤ h3BKMDyadicRadius (hi + 1)) :
    h3BKMDyadicMiddleFrequencyFactor lo hi ξ
      =
    1 := by

  unfold h3BKMDyadicMiddleFrequencyFactor

  exact
    h3BKMDyadicFrequencyShell_sum_Icc_eq_one
      hlohi
      hLower
      hUpper

/--
The exact low/middle/high partition may be stated directly using the named
middle multiplier.
-/
theorem h3BKMDyadicFrequencyTrichotomy_named_eq_one
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (ξ : H3FourierPoint3) :
    h3BKMDyadicLowFrequencyFactor lo ξ
      +
    h3BKMDyadicMiddleFrequencyFactor lo hi ξ
      +
    h3BKMDyadicHighFrequencyFactor hi ξ
      =
    1 := by

  unfold h3BKMDyadicMiddleFrequencyFactor

  exact
    h3BKMDyadicFrequencyTrichotomy_eq_one
      hlohi ξ

/--
Complex-valued version of the named low/middle/high partition.
-/
theorem h3BKMDyadicFrequencyTrichotomy_named_complex_eq_one
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (ξ : H3FourierPoint3) :
    (h3BKMDyadicLowFrequencyFactor lo ξ : ℂ)
      +
    (h3BKMDyadicMiddleFrequencyFactor lo hi ξ : ℂ)
      +
    (h3BKMDyadicHighFrequencyFactor hi ξ : ℂ)
      =
    1 := by

  exact_mod_cast
    h3BKMDyadicFrequencyTrichotomy_named_eq_one
      hlohi ξ

end

end Euclidean
end Bridge
end PrimeTensor
