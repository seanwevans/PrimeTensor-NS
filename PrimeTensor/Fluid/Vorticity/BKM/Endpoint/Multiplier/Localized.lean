import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Frequency.Shell

/-!
# BKM endpoint: dyadically localized Biot--Savart multiplier

The smooth shell from `FrequencyShell` is now multiplied by the homogeneous
degree-zero Biot--Savart coefficient

    mᵢₖ(ξ) = ξᵢ ξₖ / |ξ|².

We define

    Mᵢₖ,R(ξ) = ψ_R(ξ) mᵢₖ(ξ).

Because `ψ_R` has compact support, the localized symbol has compact support.
Because `0 ≤ ψ_R ≤ 1` and `‖mᵢₖ‖ ≤ 1`, the localized symbol satisfies the
uniform pointwise bound

    ‖Mᵢₖ,R(ξ)‖ ≤ 1.

The shell also kills the entire inner ball `‖ξ‖ ≤ R`, so the localized symbol
vanishes in a neighborhood of the only singular frequency.

The next checkpoint will use that vanishing neighborhood to prove global
smoothness of the localized symbol and package it as a complex Schwartz
function.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function
open scoped Topology ContDiff SchwartzMap

noncomputable section

noncomputable local instance axisFintypeBKMEndpointLocalizedMultiplier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The smooth shell is bounded above by one. -/
theorem h3BKMFrequencyShell_le_one
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3) :
    h3BKMFrequencyShell R hR ξ ≤ 1 := by

  have hOuterLe :
      h3BKMFrequencyCutoffBump
          (2 * R)
          (mul_pos (by norm_num) hR)
          ξ
        ≤
      1 :=
    h3BKMFrequencyCutoffBump_le_one
      (mul_pos (by norm_num) hR)
      ξ

  have hOuterNonneg :
      0 ≤
      h3BKMFrequencyCutoffBump
        (2 * R)
        (mul_pos (by norm_num) hR)
        ξ :=
    h3BKMFrequencyCutoffBump_nonneg
      (mul_pos (by norm_num) hR)
      ξ

  have hInnerNonneg :
      0 ≤
      h3BKMFrequencyCutoffBump
        R hR ξ :=
    h3BKMFrequencyCutoffBump_nonneg
      hR ξ

  have hInnerLe :
      h3BKMFrequencyCutoffBump
          R hR ξ
        ≤
      1 :=
    h3BKMFrequencyCutoffBump_le_one
      hR ξ

  have hComplementNonneg :
      0 ≤
      1 -
        h3BKMFrequencyCutoffBump
          R hR ξ :=
    sub_nonneg.mpr hInnerLe

  unfold h3BKMFrequencyShell

  calc
    h3BKMFrequencyCutoffBump
          (2 * R)
          (mul_pos (by norm_num) hR)
          ξ
        *
      (
        1 -
        h3BKMFrequencyCutoffBump
          R hR ξ
      )
        ≤
      1 *
      (
        1 -
        h3BKMFrequencyCutoffBump
          R hR ξ
      ) := by
        exact
          mul_le_mul_of_nonneg_right
            hOuterLe
            hComplementNonneg

    _ =
      1 -
        h3BKMFrequencyCutoffBump
          R hR ξ := by
      ring

    _ ≤ 1 := by
      linarith

/--
Dyadically localized degree-zero Biot--Savart coordinate multiplier.
-/
noncomputable def h3BKMLocalizedCoordinateMultiplier
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  (h3BKMFrequencyShell R hR ξ : ℂ)
    *
  h3BKMCoordinateCoefficient ξ i k

/-- The localized multiplier vanishes on the entire inner ball. -/
theorem h3BKMLocalizedCoordinateMultiplier_eq_zero_of_norm_le
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    {ξ : H3FourierPoint3}
    (hξ : ‖ξ‖ ≤ R) :
    h3BKMLocalizedCoordinateMultiplier
      R hR i k ξ
      =
    0 := by

  unfold h3BKMLocalizedCoordinateMultiplier

  rw [
    h3BKMFrequencyShell_eq_zero_of_norm_le
      hR hξ
  ]

  norm_num

/-- The complexification of the real frequency shell has compact support. -/
theorem h3BKMFrequencyShell_complex_hasCompactSupport
    {R : ℝ}
    (hR : 0 < R) :
    HasCompactSupport
      (fun ξ : H3FourierPoint3 =>
        (h3BKMFrequencyShell R hR ξ : ℂ)) := by

  exact
    (h3BKMFrequencyShell_hasCompactSupport hR).comp_left
      (g := Complex.ofReal)
      rfl

/-- Every localized Biot--Savart coordinate symbol has compact support. -/
theorem h3BKMLocalizedCoordinateMultiplier_hasCompactSupport
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    HasCompactSupport
      (h3BKMLocalizedCoordinateMultiplier
        R hR i k) := by

  unfold h3BKMLocalizedCoordinateMultiplier

  exact
    (h3BKMFrequencyShell_complex_hasCompactSupport hR).mul_right

/-- Uniform degree-zero bound for every localized coordinate multiplier. -/
theorem norm_h3BKMLocalizedCoordinateMultiplier_le_one
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3BKMLocalizedCoordinateMultiplier
        R hR i k ξ‖
      ≤
    1 := by

  unfold h3BKMLocalizedCoordinateMultiplier

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg
      (h3BKMFrequencyShell_nonneg hR ξ)
  ]

  have hShell :
      h3BKMFrequencyShell R hR ξ ≤ 1 :=
    h3BKMFrequencyShell_le_one
      hR ξ

  have hCoeff :
      ‖h3BKMCoordinateCoefficient ξ i k‖ ≤ 1 :=
    norm_h3BKMCoordinateCoefficient_le_one
      ξ i k

  exact
    (mul_le_mul
      hShell
      hCoeff
      (norm_nonneg _)
      (by norm_num)).trans_eq
        (by ring)

/-- The localized multiplier itself is pointwise norm-nonnegative. -/
theorem norm_h3BKMLocalizedCoordinateMultiplier_nonneg
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (ξ : H3FourierPoint3) :
    0 ≤
    ‖h3BKMLocalizedCoordinateMultiplier
        R hR i k ξ‖ := by
  exact norm_nonneg _

end

end Euclidean
end Bridge
end PrimeTensor
