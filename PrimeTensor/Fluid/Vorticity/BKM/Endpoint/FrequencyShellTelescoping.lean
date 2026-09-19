import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicShellPartition

/-!
# BKM endpoint: the product shell is a telescoping cutoff difference

The BKM shell was introduced in the product form

    ψ_R = χ_{2R} (1 - χ_R),

where `χ_R` is one on `‖ξ‖ ≤ R` and vanishes once `2R ≤ ‖ξ‖`.

The nesting of these particular cutoffs gives a stronger identity.  Wherever
`χ_R` can be nonzero we have `‖ξ‖ ≤ 2R`, hence `χ_{2R} = 1`; outside that
region `χ_R = 0`.  Therefore

    χ_{2R} χ_R = χ_R

pointwise, and consequently

    ψ_R = χ_{2R} - χ_R.

At the standard dyadic radii `R_n = 2^n` this becomes

    ψ_{R_n} = χ_{R_{n+1}} - χ_{R_n}.

Thus a finite consecutive shell sum telescopes exactly:

    ∑_{n=lo}^{hi} ψ_{R_n}
      = χ_{R_{hi+1}} - χ_{R_lo}.

In particular the sum is exactly one throughout the interior annulus

    R_{lo+1} ≤ ‖ξ‖ ≤ R_{hi+1}.

This is the global middle-window partition identity needed to turn the
already-bounded middle localized gradient state into the genuine smooth
middle-frequency gradient piece.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointFrequencyShellTelescoping
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
The product-form BKM shell is exactly the difference of the nested outer and
inner cutoffs.
-/
theorem h3BKMFrequencyShell_eq_cutoff_sub
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3) :
    h3BKMFrequencyShell R hR ξ
      =
    h3BKMFrequencyCutoffBump
        (2 * R)
        (mul_pos (by norm_num) hR)
        ξ
      -
    h3BKMFrequencyCutoffBump
        R hR ξ := by

  by_cases hξ : ‖ξ‖ ≤ 2 * R

  · have hOuterOne :
        h3BKMFrequencyCutoffBump
            (2 * R)
            (mul_pos (by norm_num) hR)
            ξ
          =
        1 :=
      h3BKMFrequencyCutoffBump_eq_one_of_norm_le
        (mul_pos (by norm_num) hR)
        hξ

    unfold h3BKMFrequencyShell

    rw [hOuterOne]

    ring

  · have hLower :
        2 * R ≤ ‖ξ‖ := by
      exact
        le_of_lt
          (lt_of_not_ge hξ)

    have hInnerZero :
        h3BKMFrequencyCutoffBump
            R hR ξ
          =
        0 :=
      h3BKMFrequencyCutoffBump_eq_zero_of_two_mul_le_norm
        hR hLower

    unfold h3BKMFrequencyShell

    rw [hInnerZero]

    ring

/--
At a standard dyadic radius, one shell is exactly the difference between the
successor cutoff and the current cutoff.
-/
theorem h3BKMDyadicFrequencyShell_eq_cutoff_succ_sub
    (n : ℕ)
    (ξ : H3FourierPoint3) :
    h3BKMFrequencyShell
        (h3BKMDyadicRadius n)
        (h3BKMDyadicRadius_pos n)
        ξ
      =
    h3BKMFrequencyCutoffBump
        (h3BKMDyadicRadius (n + 1))
        (h3BKMDyadicRadius_pos (n + 1))
        ξ
      -
    h3BKMFrequencyCutoffBump
        (h3BKMDyadicRadius n)
        (h3BKMDyadicRadius_pos n)
        ξ := by

  have h :=
    h3BKMFrequencyShell_eq_cutoff_sub
      (h3BKMDyadicRadius_pos n)
      ξ

  simpa only [
    ← h3BKMDyadicRadius_succ n
  ] using h

/--
A consecutive finite dyadic shell sum telescopes to the difference of its
endpoint cutoffs.
-/
theorem h3BKMDyadicFrequencyShell_sum_Icc_eq_cutoff_sub
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    (ξ : H3FourierPoint3) :
    (∑ n ∈ Finset.Icc lo hi,
      h3BKMFrequencyShell
        (h3BKMDyadicRadius n)
        (h3BKMDyadicRadius_pos n)
        ξ)
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

  let χ : ℕ → ℝ :=
    fun n =>
      h3BKMFrequencyCutoffBump
        (h3BKMDyadicRadius n)
        (h3BKMDyadicRadius_pos n)
        ξ

  have hIcc :
      Finset.Icc lo hi
        =
      Finset.Ico lo (hi + 1) := by
    ext n
    simp

  rw [hIcc]

  have hTerm :
      ∀ n : ℕ,
        h3BKMFrequencyShell
            (h3BKMDyadicRadius n)
            (h3BKMDyadicRadius_pos n)
            ξ
          =
        χ (n + 1) - χ n := by
    intro n
    exact
      h3BKMDyadicFrequencyShell_eq_cutoff_succ_sub
        n ξ

  simp_rw [hTerm]

  rw [
    Finset.sum_Ico_eq_sub
      (fun n => χ (n + 1) - χ n)
      (show lo ≤ hi + 1 by omega),
    Finset.sum_range_sub,
    Finset.sum_range_sub
  ]

  dsimp only [χ]

  ring

/--
The consecutive dyadic shell sum is exactly one on the annulus between the
successor of the lower radius and the successor of the upper radius.
-/
theorem h3BKMDyadicFrequencyShell_sum_Icc_eq_one
    {lo hi : ℕ}
    (hlohi : lo ≤ hi)
    {ξ : H3FourierPoint3}
    (hLower :
      h3BKMDyadicRadius (lo + 1) ≤ ‖ξ‖)
    (hUpper :
      ‖ξ‖ ≤ h3BKMDyadicRadius (hi + 1)) :
    (∑ n ∈ Finset.Icc lo hi,
      h3BKMFrequencyShell
        (h3BKMDyadicRadius n)
        (h3BKMDyadicRadius_pos n)
        ξ)
      =
    1 := by

  rw [
    h3BKMDyadicFrequencyShell_sum_Icc_eq_cutoff_sub
      hlohi ξ
  ]

  have hLower' :
      2 * h3BKMDyadicRadius lo ≤ ‖ξ‖ := by
    simpa only [
      h3BKMDyadicRadius_succ
    ] using hLower

  have hInnerZero :
      h3BKMFrequencyCutoffBump
          (h3BKMDyadicRadius lo)
          (h3BKMDyadicRadius_pos lo)
          ξ
        =
      0 :=
    h3BKMFrequencyCutoffBump_eq_zero_of_two_mul_le_norm
      (h3BKMDyadicRadius_pos lo)
      hLower'

  have hOuterOne :
      h3BKMFrequencyCutoffBump
          (h3BKMDyadicRadius (hi + 1))
          (h3BKMDyadicRadius_pos (hi + 1))
          ξ
        =
      1 :=
    h3BKMFrequencyCutoffBump_eq_one_of_norm_le
      (h3BKMDyadicRadius_pos (hi + 1))
      hUpper

  rw [hInnerZero, hOuterOne]

  ring

end

end Euclidean
end Bridge
end PrimeTensor
