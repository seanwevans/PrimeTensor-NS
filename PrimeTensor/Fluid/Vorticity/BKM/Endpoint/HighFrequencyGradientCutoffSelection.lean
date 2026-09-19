import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.HighFrequencyGradientDyadicDecay
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicMiddleGradient
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# BKM endpoint: logarithmic upper dyadic cutoff selection

The high-frequency estimate now has the form

    high_hi(G)
      ≤ (2π) R_(hi+1)^(-1/4) C_q ‖G‖.

To make the high term uniformly bounded, choose the upper dyadic index at the
ceiling of the base-two logarithm of the fourth power of the H³ size.

For a scalar `A`, set

    M(A)  = max 1 A,
    N(A)  = ceil (log₂ (M(A)^4)).

Then

    M(A)^4 ≤ 2^N(A) ≤ R_(N(A)+1),

so in particular

    A ≤ R_(N(A)+1)^(1/4).

Consequently, whenever `‖G‖ ≤ A`,

    R_(N(A)+1)^(-1/4) ‖G‖ ≤ 1,

and the high-frequency inverse-Fourier gradient is bounded solely by the fixed
quarter-tail constant.

At the same time the middle-window shell count with lower index zero satisfies

    width(0,N(A))
      ≤ 4 log₂(max 1 A) + 2.

This is the precise cutoff algebra needed to convert the low/middle/high
trichotomy into a logarithmic gradient estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeBKMEndpointHighFrequencyGradientCutoffSelection
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Canonical upper cutoff -/

/-- Safe positive scalar used in the logarithmic dyadic cutoff. -/
noncomputable def h3BKMUpperCutoffScale
    (A : ℝ) : ℝ :=
  max 1 A

/--
Canonical upper dyadic index: the natural ceiling of the base-two logarithm of
the fourth power of the safe H³ scale.
-/
noncomputable def h3BKMUpperCutoffIndex
    (A : ℝ) : ℕ :=
  ⌈Real.logb 2 ((h3BKMUpperCutoffScale A) ^ 4)⌉₊

theorem one_le_h3BKMUpperCutoffScale
    (A : ℝ) :
    1 ≤ h3BKMUpperCutoffScale A := by
  unfold h3BKMUpperCutoffScale
  exact le_max_left _ _

theorem h3BKMUpperCutoffScale_pos
    (A : ℝ) :
    0 < h3BKMUpperCutoffScale A :=
  lt_of_lt_of_le zero_lt_one
    (one_le_h3BKMUpperCutoffScale A)

theorem le_h3BKMUpperCutoffScale
    (A : ℝ) :
    A ≤ h3BKMUpperCutoffScale A := by
  unfold h3BKMUpperCutoffScale
  exact le_max_right _ _

/-! ## Radius captured by the selected index -/

/--
The selected dyadic radius already dominates the fourth power of the safe
scale.
-/
theorem h3BKMUpperCutoffScale_pow_four_le_radius
    (A : ℝ) :
    (h3BKMUpperCutoffScale A) ^ 4
      ≤
    h3BKMDyadicRadius
      (h3BKMUpperCutoffIndex A) := by

  let M : ℝ :=
    h3BKMUpperCutoffScale A

  let L : ℝ :=
    Real.logb 2 (M ^ 4)

  let N : ℕ :=
    h3BKMUpperCutoffIndex A

  have hM :
      0 < M := by
    dsimp only [M]
    exact h3BKMUpperCutoffScale_pos A

  have hM4 :
      0 < M ^ 4 := by
    positivity

  have hCeil :
      L ≤ (N : ℝ) := by
    dsimp only [L, N, h3BKMUpperCutoffIndex]
    exact Nat.le_ceil _

  have hPow :
      (2 : ℝ) ^ L
        ≤
      (2 : ℝ) ^ (N : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2)
      hCeil

  calc
    M ^ 4
        =
      (2 : ℝ) ^ L := by
        dsimp only [L]
        symm
        exact
          Real.rpow_logb
            (by norm_num : (0 : ℝ) < 2)
            (by norm_num : (2 : ℝ) ≠ 1)
            hM4

    _ ≤
      (2 : ℝ) ^ (N : ℝ) :=
      hPow

    _ =
      h3BKMDyadicRadius N := by
        unfold h3BKMDyadicRadius
        exact
          Real.rpow_natCast
            (2 : ℝ)
            N

    _ =
      h3BKMDyadicRadius
        (h3BKMUpperCutoffIndex A) := by
        rfl

/--
The successor radius used by the high-frequency factor also dominates the
fourth power of the safe scale.
-/
theorem h3BKMUpperCutoffScale_pow_four_le_successor_radius
    (A : ℝ) :
    (h3BKMUpperCutoffScale A) ^ 4
      ≤
    h3BKMDyadicRadius
      (h3BKMUpperCutoffIndex A + 1) := by

  calc
    (h3BKMUpperCutoffScale A) ^ 4
        ≤
      h3BKMDyadicRadius
        (h3BKMUpperCutoffIndex A) :=
      h3BKMUpperCutoffScale_pow_four_le_radius A

    _ ≤
      h3BKMDyadicRadius
        (h3BKMUpperCutoffIndex A + 1) := by
      rw [
        h3BKMDyadicRadius_succ
          (h3BKMUpperCutoffIndex A)
      ]
      have hR :
          0 ≤
            h3BKMDyadicRadius
              (h3BKMUpperCutoffIndex A) :=
        (h3BKMDyadicRadius_pos
          (h3BKMUpperCutoffIndex A)).le
      nlinarith

/--
Taking a quarter power shows that the selected successor radius dominates the
safe scale itself.
-/
theorem h3BKMUpperCutoffScale_le_successor_radius_quarter
    (A : ℝ) :
    h3BKMUpperCutoffScale A
      ≤
    (h3BKMDyadicRadius
      (h3BKMUpperCutoffIndex A + 1)) ^ ((1 : ℝ) / 4) := by

  let M : ℝ :=
    h3BKMUpperCutoffScale A

  let R : ℝ :=
    h3BKMDyadicRadius
      (h3BKMUpperCutoffIndex A + 1)

  have hM :
      0 ≤ M := by
    exact
      (h3BKMUpperCutoffScale_pos A).le

  have hR :
      0 ≤ R := by
    dsimp only [R]
    exact
      (h3BKMDyadicRadius_pos
        (h3BKMUpperCutoffIndex A + 1)).le

  have hM4R :
      M ^ 4 ≤ R := by
    dsimp only [M, R]
    exact
      h3BKMUpperCutoffScale_pow_four_le_successor_radius A

  have hQuarter :=
    Real.rpow_le_rpow
      (pow_nonneg hM 4)
      hM4R
      (by norm_num : 0 ≤ (1 : ℝ) / 4)

  have hCollapse :
      (M ^ 4) ^ ((1 : ℝ) / 4)
        =
      M := by
    calc
      (M ^ 4) ^ ((1 : ℝ) / 4)
          =
        (M ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) := by
          congr 1
          exact
            (Real.rpow_natCast M 4).symm

      _ =
        M ^ ((4 : ℝ) * ((1 : ℝ) / 4)) := by
          rw [← Real.rpow_mul hM]

      _ =
        M := by
          convert Real.rpow_one M using 1 <;> ring

  rw [hCollapse] at hQuarter

  exact hQuarter

theorem le_successor_radius_quarter_h3BKMUpperCutoff
    (A : ℝ) :
    A
      ≤
    (h3BKMDyadicRadius
      (h3BKMUpperCutoffIndex A + 1)) ^ ((1 : ℝ) / 4) :=
  le_trans
    (le_h3BKMUpperCutoffScale A)
    (h3BKMUpperCutoffScale_le_successor_radius_quarter A)

/-! ## High tail becomes uniformly bounded -/

/--
The inverse quarter-radius factor times any scalar below the selected H³ scale
is at most one.
-/
theorem successor_radius_quarter_inv_mul_le_one
    {A B : ℝ}
    (hB : 0 ≤ B)
    (hBA : B ≤ A) :
    (h3BKMDyadicRadius
        (h3BKMUpperCutoffIndex A + 1) ^ ((1 : ℝ) / 4))⁻¹
        *
      B
      ≤
    1 := by

  let Rq : ℝ :=
    (h3BKMDyadicRadius
      (h3BKMUpperCutoffIndex A + 1)) ^ ((1 : ℝ) / 4)

  have hRq :
      0 < Rq := by
    dsimp only [Rq]
    exact
      Real.rpow_pos_of_pos
        (h3BKMDyadicRadius_pos
          (h3BKMUpperCutoffIndex A + 1))
        ((1 : ℝ) / 4)

  have hBRq :
      B ≤ Rq := by
    exact
      le_trans
        hBA
        (le_successor_radius_quarter_h3BKMUpperCutoff A)

  rw [inv_mul_eq_div]

  exact
    (div_le_iff₀ hRq).2
      (by
        simpa only [one_mul] using hBRq)

/--
At the canonical cutoff, the high-frequency inverse-Fourier contribution is
uniformly bounded by the fixed quarter-tail constant whenever the weighted H³
state norm is at most `A`.
-/
theorem norm_fourierInv_h3BKMHighGradientAmplitude_selected_le_constant
    (A : ℝ)
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (hGA : ‖G‖ ≤ A) :
    ‖FourierTransformInv.fourierInv
        (h3BKMHighGradientAmplitude
          (h3BKMUpperCutoffIndex A)
          G i)
        x‖
      ≤
    (2 * Real.pi)
      *
    h3BKMQuarterTailMomentConstant := by

  have hBase :=
    norm_fourierInv_h3BKMHighGradientAmplitude_le_dyadicQuarter
      (h3BKMUpperCutoffIndex A)
      G i x

  have hTail :
      (h3BKMDyadicRadius
          (h3BKMUpperCutoffIndex A + 1) ^ ((1 : ℝ) / 4))⁻¹
          *
        ‖G‖
        ≤
      1 :=
    successor_radius_quarter_inv_mul_le_one
      (A := A)
      (B := ‖G‖)
      (norm_nonneg G)
      hGA

  have hC :
      0 ≤
        (2 * Real.pi)
          *
        h3BKMQuarterTailMomentConstant := by
    exact
      mul_nonneg
        (by positivity)
        h3BKMQuarterTailMomentConstant_nonneg

  calc
    ‖FourierTransformInv.fourierInv
        (h3BKMHighGradientAmplitude
          (h3BKMUpperCutoffIndex A)
          G i)
        x‖
        ≤
      (((2 * Real.pi)
          *
        (h3BKMDyadicRadius
          (h3BKMUpperCutoffIndex A + 1) ^ ((1 : ℝ) / 4))⁻¹)
          *
        h3BKMQuarterTailMomentConstant)
        *
      ‖G‖ :=
      hBase

    _ =
      ((2 * Real.pi)
        *
      h3BKMQuarterTailMomentConstant)
        *
      ((h3BKMDyadicRadius
          (h3BKMUpperCutoffIndex A + 1) ^ ((1 : ℝ) / 4))⁻¹
          *
        ‖G‖) := by
      ring

    _ ≤
      ((2 * Real.pi)
        *
      h3BKMQuarterTailMomentConstant)
        *
      1 :=
      mul_le_mul_of_nonneg_left
        hTail
        hC

    _ =
      (2 * Real.pi)
        *
      h3BKMQuarterTailMomentConstant := by
      ring

/-! ## Logarithmic middle-window width -/

/--
The selected middle window from the unit dyadic scale has logarithmic width at
most `4 log₂(max 1 A) + 2`.
-/
theorem h3BKMMiddleDyadicLogWidth_zero_selected_le
    (A : ℝ) :
    h3BKMMiddleDyadicLogWidth
        0
        (h3BKMUpperCutoffIndex A)
      ≤
    4 * Real.logb 2 (h3BKMUpperCutoffScale A)
      + 2 := by

  let M : ℝ :=
    h3BKMUpperCutoffScale A

  let L : ℝ :=
    Real.logb 2 (M ^ 4)

  have hM1 :
      1 ≤ M := by
    dsimp only [M]
    exact one_le_h3BKMUpperCutoffScale A

  have hM4one :
      1 ≤ M ^ 4 := by
    simpa using
      (pow_le_pow_left₀
        (by norm_num : 0 ≤ (1 : ℝ))
        hM1
        4)

  have hL :
      0 ≤ L := by
    dsimp only [L]
    exact
      Real.logb_nonneg
        (by norm_num : (1 : ℝ) < 2)
        hM4one

  have hCeil :
      ((h3BKMUpperCutoffIndex A : ℕ) : ℝ)
        <
      L + 1 := by
    unfold h3BKMUpperCutoffIndex
    dsimp only [L, M]
    exact
      Nat.ceil_lt_add_one hL

  rw [
    h3BKMMiddleDyadicLogWidth_eq_shellCount
      (Nat.zero_le (h3BKMUpperCutoffIndex A))
  ]

  simp only [
    Nat.sub_zero,
    Nat.cast_add,
    Nat.cast_one
  ]

  have hLogPow :
      Real.logb 2 (M ^ 4)
        =
      (4 : ℝ) * Real.logb 2 M :=
    Real.logb_pow 2 M 4

  dsimp only [L] at hCeil
  rw [hLogPow] at hCeil

  dsimp only [M] at hCeil

  linarith

end

end Euclidean
end Bridge
end PrimeTensor
