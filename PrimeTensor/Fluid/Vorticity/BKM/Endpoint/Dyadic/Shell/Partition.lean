import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.Middle.Kernel.Bound

/-!
# BKM endpoint: adjacent dyadic shells form an exact local partition

The smooth BKM shell was deliberately defined as

    ψ_R = χ_{2R} (1 - χ_R),

rather than as a raw difference of cutoffs.  Although these shells do not
telescope algebraically, two adjacent dyadic shells form an exact partition
on the annulus between their central radii.

If

    2R ≤ ‖ξ‖ ≤ 4R,

then the radius-`R` cutoff has already vanished while the radius-`4R` cutoff
is still identically one.  Hence

    ψ_R(ξ) + ψ_{2R}(ξ)
      = χ_{2R}(ξ) + (1 - χ_{2R}(ξ))
      = 1.

For the standard radii `Rₙ = 2ⁿ`, this says

    ψ_{Rₙ}(ξ) + ψ_{Rₙ₊₁}(ξ) = 1

whenever `Rₙ₊₁ ≤ ‖ξ‖ ≤ Rₙ₊₂`.

This is the exact local reconstruction mechanism needed to turn the finite
middle-shell Fourier identity into the genuine middle-frequency gradient
piece; no artificial division by the shell sum is required.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicShellPartition
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The standard dyadic radius doubles at every successor index. -/
theorem h3BKMDyadicRadius_succ
    (n : ℕ) :
    h3BKMDyadicRadius (n + 1)
      =
    2 * h3BKMDyadicRadius n := by

  unfold h3BKMDyadicRadius
  rw [pow_succ]
  ring

/--
The radius-`R` low-pass cutoff has vanished once the frequency norm reaches
`2R`, its outer support radius.
-/
theorem h3BKMFrequencyCutoffBump_eq_zero_of_two_mul_le_norm
    {R : ℝ}
    (hR : 0 < R)
    {ξ : H3FourierPoint3}
    (hξ : 2 * R ≤ ‖ξ‖) :
    h3BKMFrequencyCutoffBump R hR ξ = 0 := by

  apply
    (h3BKMFrequencyCutoffBump R hR).zero_of_le_dist

  simpa only [
    h3BKMFrequencyCutoffBump_rOut,
    dist_zero_right
  ] using hξ

/--
Two adjacent smooth BKM shells add exactly to one on the annulus
`2R ≤ ‖ξ‖ ≤ 4R`.
-/
theorem h3BKMFrequencyShell_add_double_eq_one
    {R : ℝ}
    (hR : 0 < R)
    {ξ : H3FourierPoint3}
    (hLower : 2 * R ≤ ‖ξ‖)
    (hUpper : ‖ξ‖ ≤ 4 * R) :
    h3BKMFrequencyShell R hR ξ
      +
    h3BKMFrequencyShell
      (2 * R)
      (mul_pos (by norm_num) hR)
      ξ
      =
    1 := by

  have hInnerZero :
      h3BKMFrequencyCutoffBump R hR ξ = 0 :=
    h3BKMFrequencyCutoffBump_eq_zero_of_two_mul_le_norm
      hR hLower

  have hTwoRPos :
      0 < 2 * R :=
    mul_pos (by norm_num) hR

  have hFourRPos :
      0 < 2 * (2 * R) :=
    mul_pos (by norm_num) hTwoRPos

  have hOuterOne :
      h3BKMFrequencyCutoffBump
          (2 * (2 * R))
          hFourRPos
          ξ
        =
      1 := by

    apply
      h3BKMFrequencyCutoffBump_eq_one_of_norm_le
        hFourRPos

    nlinarith

  unfold h3BKMFrequencyShell

  rw [
    hInnerZero,
    hOuterOne
  ]

  ring

/--
At adjacent dyadic scales, the two BKM shells reconstruct one exactly on the
annulus between the next two dyadic radii.
-/
theorem h3BKMDyadicFrequencyShell_adjacent_eq_one
    (n : ℕ)
    {ξ : H3FourierPoint3}
    (hLower :
      h3BKMDyadicRadius (n + 1) ≤ ‖ξ‖)
    (hUpper :
      ‖ξ‖ ≤ h3BKMDyadicRadius (n + 2)) :
    h3BKMFrequencyShell
        (h3BKMDyadicRadius n)
        (h3BKMDyadicRadius_pos n)
        ξ
      +
    h3BKMFrequencyShell
        (h3BKMDyadicRadius (n + 1))
        (h3BKMDyadicRadius_pos (n + 1))
        ξ
      =
    1 := by

  have hLower' :
      2 * h3BKMDyadicRadius n ≤ ‖ξ‖ := by

    rw [
      h3BKMDyadicRadius_succ
        n
    ] at hLower

    exact hLower

  have hUpper' :
      ‖ξ‖ ≤ 4 * h3BKMDyadicRadius n := by

    have h := hUpper

    rw [
      show n + 2 = (n + 1) + 1 by omega,
      h3BKMDyadicRadius_succ
        (n + 1),
      h3BKMDyadicRadius_succ
        n
    ] at h

    nlinarith

  have h :=
    h3BKMFrequencyShell_add_double_eq_one
      (h3BKMDyadicRadius_pos n)
      hLower'
      hUpper'

  simpa only [
    h3BKMDyadicRadius_succ
  ] using h

end

end Euclidean
end Bridge
end PrimeTensor
