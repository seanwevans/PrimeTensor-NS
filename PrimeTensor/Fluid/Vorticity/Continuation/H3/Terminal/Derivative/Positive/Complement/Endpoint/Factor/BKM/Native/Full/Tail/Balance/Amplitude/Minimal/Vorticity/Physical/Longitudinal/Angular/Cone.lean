import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Divergence.Free.Obstruction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Heat.Divergence

/-!
# Angular-cone recovery of the longitudinal spectral component

The surviving one-component obstruction lies inside a divergence-free weighted
H³ spectral path.  Solving the Fourier divergence relation for one coordinate
is not uniformly bounded on all of frequency space: division by the
longitudinal derivative symbol degenerates near the coordinate plane.

The correct bounded region is angular rather than an absolute frequency slab.

For `κ > 0`, define the good cone for coordinate `i` by

    κ * |D(ξ)| ≤ |dᵢ(ξ)|,

where `|D(ξ)| = 2π ‖ξ‖` is the radial derivative magnitude and `dᵢ` is the
`i`-th coordinate derivative symbol.  On this cone every transverse
coordinate symbol satisfies

    |dⱼ(ξ)| ≤ |D(ξ)| ≤ κ⁻¹ |dᵢ(ξ)|.

Therefore Fourier incompressibility gives the pointwise degree-zero estimate

    κ ‖gᵢ‖ ≤ sum of the two transverse component norms.

The same estimate applies to the difference of two divergence-free spectral
vectors.  This is the exact pointwise input needed for the next L²
localization step: any surviving longitudinal non-Cauchy mass must concentrate
in the complementary equatorial cone.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalAngularCone
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Angular good and bad cones -/

/--
Angular good cone for recovering velocity coordinate `i` from the Fourier
divergence identity.
-/
def h3TerminalLongitudinalAngularGoodCone
    (i : Fin 3)
    (κ : ℝ) :
    Set H3FourierPoint3 :=
  {
    ξ |
      κ * h3FourierGradientMagnitude ξ
        ≤
      ‖h3FourierDerivativeSymbol i ξ‖
  }

/--
Complementary equatorial cone where the longitudinal derivative symbol is
small compared with the full radial derivative magnitude.
-/
def h3TerminalLongitudinalAngularBadCone
    (i : Fin 3)
    (κ : ℝ) :
    Set H3FourierPoint3 :=
  {
    ξ |
      ‖h3FourierDerivativeSymbol i ξ‖
        <
      κ * h3FourierGradientMagnitude ξ
  }

/--
Every frequency belongs to the angular good cone or the complementary bad
cone.
-/
theorem mem_longitudinalAngularGoodCone_or_badCone
    (i : Fin 3)
    (κ : ℝ)
    (ξ : H3FourierPoint3) :
    ξ ∈ h3TerminalLongitudinalAngularGoodCone i κ
      ∨
    ξ ∈ h3TerminalLongitudinalAngularBadCone i κ := by

  exact
    le_or_gt
      (κ * h3FourierGradientMagnitude ξ)
      ‖h3FourierDerivativeSymbol i ξ‖

/-! ## Transverse magnitude -/

/--
Sum of the norms of the two spectral coordinates transverse to `i`.
-/
def h3TerminalTransverseSpectralMagnitude
    (i : Fin 3)
    (g : Fin 3 → ℂ) : ℝ :=
  if i = 0 then
    ‖g 1‖ + ‖g 2‖
  else if i = 1 then
    ‖g 0‖ + ‖g 2‖
  else
    ‖g 0‖ + ‖g 1‖

/-! ## Pointwise recovery on the good cone -/

/--
On the angular good cone, Fourier incompressibility controls the longitudinal
spectral coordinate by the two transverse coordinates.

The factor is written without division:

    κ ‖gᵢ‖ ≤ transverse magnitude.

This form is stable at the Lean level and is exactly equivalent to the usual
`κ⁻¹` multiplier bound when `κ > 0`.
-/
theorem mul_norm_longitudinal_le_transverse_of_divergenceFree_of_mem_goodCone
    {i : Fin 3}
    {κ : ℝ}
    (hκ : 0 < κ)
    {ξ : H3FourierPoint3}
    (hξ : ξ ≠ 0)
    {g : Fin 3 → ℂ}
    (hDiv :
      (∑ j : Fin 3,
        h3FourierDerivativeSymbol j ξ * g j)
        =
      0)
    (hGood :
      ξ ∈ h3TerminalLongitudinalAngularGoodCone i κ) :
    κ * ‖g i‖
      ≤
    h3TerminalTransverseSpectralMagnitude i g := by

  have hGradPos :
      0 < h3FourierGradientMagnitude ξ := by
    unfold h3FourierGradientMagnitude
    have hNormPos :
        0 < ‖ξ‖ :=
      norm_pos_iff.mpr hξ
    positivity

  change
    κ * h3FourierGradientMagnitude ξ
      ≤
    ‖h3FourierDerivativeSymbol i ξ‖
    at hGood

  fin_cases i

  · have hD1 :
        ‖h3FourierDerivativeSymbol (1 : Fin 3) ξ‖
          ≤
        h3FourierGradientMagnitude ξ :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude
        (1 : Fin 3) ξ

    have hD2 :
        ‖h3FourierDerivativeSymbol (2 : Fin 3) ξ‖
          ≤
        h3FourierGradientMagnitude ξ :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude
        (2 : Fin 3) ξ

    have hDiv' :
        h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
          +
        (
          h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
            +
          h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2
        )
          =
        0 := by
      simpa only [Fin.sum_univ_three, add_assoc] using hDiv

    have hEq :
        h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
          =
        -
        (
          h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
            +
          h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2
        ) := by
      calc
        h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
            =
          (
            h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
              +
            (
              h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
                +
              h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2
            )
          )
            -
          (
            h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
              +
            h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2
          ) := by
            ring
        _ =
          -
          (
            h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
              +
            h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2
          ) := by
            rw [hDiv']
            ring

    have hLower :
        κ * h3FourierGradientMagnitude ξ * ‖g 0‖
          ≤
        ‖h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0‖ := by
      calc
        κ * h3FourierGradientMagnitude ξ * ‖g 0‖
            ≤
          ‖h3FourierDerivativeSymbol (0 : Fin 3) ξ‖ * ‖g 0‖ :=
            mul_le_mul_of_nonneg_right
              hGood
              (norm_nonneg _)
        _ =
          ‖h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0‖ := by
            rw [norm_mul]

    have hUpper :
        ‖h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0‖
          ≤
        h3FourierGradientMagnitude ξ * (‖g 1‖ + ‖g 2‖) := by
      rw [hEq, norm_neg]
      calc
        ‖h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
            +
          h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2‖
            ≤
          ‖h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1‖
            +
          ‖h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2‖ :=
            norm_add_le _ _
        _ =
          ‖h3FourierDerivativeSymbol (1 : Fin 3) ξ‖ * ‖g 1‖
            +
          ‖h3FourierDerivativeSymbol (2 : Fin 3) ξ‖ * ‖g 2‖ := by
            rw [norm_mul, norm_mul]
        _ ≤
          h3FourierGradientMagnitude ξ * ‖g 1‖
            +
          h3FourierGradientMagnitude ξ * ‖g 2‖ := by
            exact
              add_le_add
                (mul_le_mul_of_nonneg_right hD1 (norm_nonneg _))
                (mul_le_mul_of_nonneg_right hD2 (norm_nonneg _))
        _ =
          h3FourierGradientMagnitude ξ * (‖g 1‖ + ‖g 2‖) := by
            ring

    have hScaled :
        h3FourierGradientMagnitude ξ * (κ * ‖g 0‖)
          ≤
        h3FourierGradientMagnitude ξ * (‖g 1‖ + ‖g 2‖) := by
      calc
        h3FourierGradientMagnitude ξ * (κ * ‖g 0‖)
            =
          κ * h3FourierGradientMagnitude ξ * ‖g 0‖ := by
            ring
        _ ≤
          ‖h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0‖ :=
            hLower
        _ ≤
          h3FourierGradientMagnitude ξ * (‖g 1‖ + ‖g 2‖) :=
            hUpper

    have hCancel :
        κ * ‖g 0‖
          ≤
        ‖g 1‖ + ‖g 2‖ := by

      by_contra hNot

      have hStrict :
          ‖g 1‖ + ‖g 2‖
            <
          κ * ‖g 0‖ :=
        lt_of_not_ge hNot

      have hStrictScaled :
          h3FourierGradientMagnitude ξ * (‖g 1‖ + ‖g 2‖)
            <
          h3FourierGradientMagnitude ξ * (κ * ‖g 0‖) :=
        mul_lt_mul_of_pos_left
          hStrict
          hGradPos

      exact
        (not_lt_of_ge hScaled)
          hStrictScaled

    simpa [h3TerminalTransverseSpectralMagnitude] using hCancel

  · have hD0 :
        ‖h3FourierDerivativeSymbol (0 : Fin 3) ξ‖
          ≤
        h3FourierGradientMagnitude ξ :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude
        (0 : Fin 3) ξ

    have hD2 :
        ‖h3FourierDerivativeSymbol (2 : Fin 3) ξ‖
          ≤
        h3FourierGradientMagnitude ξ :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude
        (2 : Fin 3) ξ

    have hDiv' :
        h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
          +
        (
          h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
            +
          h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2
        )
          =
        0 := by
      have h := hDiv
      simp only [Fin.sum_univ_three] at h
      calc
        h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
            +
          (
            h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
              +
            h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2
          )
            =
          h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
            +
          h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
            +
          h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2 := by
            ring
        _ = 0 := h

    have hEq :
        h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
          =
        -
        (
          h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
            +
          h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2
        ) := by
      calc
        h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
            =
          (
            h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
              +
            (
              h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
                +
              h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2
            )
          )
            -
          (
            h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
              +
            h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2
          ) := by
            ring
        _ =
          -
          (
            h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
              +
            h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2
          ) := by
            rw [hDiv']
            ring

    have hLower :
        κ * h3FourierGradientMagnitude ξ * ‖g 1‖
          ≤
        ‖h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1‖ := by
      calc
        κ * h3FourierGradientMagnitude ξ * ‖g 1‖
            ≤
          ‖h3FourierDerivativeSymbol (1 : Fin 3) ξ‖ * ‖g 1‖ :=
            mul_le_mul_of_nonneg_right
              hGood
              (norm_nonneg _)
        _ =
          ‖h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1‖ := by
            rw [norm_mul]

    have hUpper :
        ‖h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1‖
          ≤
        h3FourierGradientMagnitude ξ * (‖g 0‖ + ‖g 2‖) := by
      rw [hEq, norm_neg]
      calc
        ‖h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
            +
          h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2‖
            ≤
          ‖h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0‖
            +
          ‖h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2‖ :=
            norm_add_le _ _
        _ =
          ‖h3FourierDerivativeSymbol (0 : Fin 3) ξ‖ * ‖g 0‖
            +
          ‖h3FourierDerivativeSymbol (2 : Fin 3) ξ‖ * ‖g 2‖ := by
            rw [norm_mul, norm_mul]
        _ ≤
          h3FourierGradientMagnitude ξ * ‖g 0‖
            +
          h3FourierGradientMagnitude ξ * ‖g 2‖ := by
            exact
              add_le_add
                (mul_le_mul_of_nonneg_right hD0 (norm_nonneg _))
                (mul_le_mul_of_nonneg_right hD2 (norm_nonneg _))
        _ =
          h3FourierGradientMagnitude ξ * (‖g 0‖ + ‖g 2‖) := by
            ring

    have hScaled :
        h3FourierGradientMagnitude ξ * (κ * ‖g 1‖)
          ≤
        h3FourierGradientMagnitude ξ * (‖g 0‖ + ‖g 2‖) := by
      calc
        h3FourierGradientMagnitude ξ * (κ * ‖g 1‖)
            =
          κ * h3FourierGradientMagnitude ξ * ‖g 1‖ := by
            ring
        _ ≤
          ‖h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1‖ :=
            hLower
        _ ≤
          h3FourierGradientMagnitude ξ * (‖g 0‖ + ‖g 2‖) :=
            hUpper

    have hCancel :
        κ * ‖g 1‖
          ≤
        ‖g 0‖ + ‖g 2‖ := by

      by_contra hNot

      have hStrict :
          ‖g 0‖ + ‖g 2‖
            <
          κ * ‖g 1‖ :=
        lt_of_not_ge hNot

      have hStrictScaled :
          h3FourierGradientMagnitude ξ * (‖g 0‖ + ‖g 2‖)
            <
          h3FourierGradientMagnitude ξ * (κ * ‖g 1‖) :=
        mul_lt_mul_of_pos_left
          hStrict
          hGradPos

      exact
        (not_lt_of_ge hScaled)
          hStrictScaled

    simpa [h3TerminalTransverseSpectralMagnitude] using hCancel

  · have hD0 :
        ‖h3FourierDerivativeSymbol (0 : Fin 3) ξ‖
          ≤
        h3FourierGradientMagnitude ξ :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude
        (0 : Fin 3) ξ

    have hD1 :
        ‖h3FourierDerivativeSymbol (1 : Fin 3) ξ‖
          ≤
        h3FourierGradientMagnitude ξ :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude
        (1 : Fin 3) ξ

    have hDiv' :
        h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2
          +
        (
          h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
            +
          h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
        )
          =
        0 := by
      have h := hDiv
      simp only [Fin.sum_univ_three] at h
      calc
        h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2
            +
          (
            h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
              +
            h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
          )
            =
          h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
            +
          h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
            +
          h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2 := by
            ring
        _ = 0 := h

    have hEq :
        h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2
          =
        -
        (
          h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
            +
          h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
        ) := by
      calc
        h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2
            =
          (
            h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2
              +
            (
              h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
                +
              h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
            )
          )
            -
          (
            h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
              +
            h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
          ) := by
            ring
        _ =
          -
          (
            h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
              +
            h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1
          ) := by
            rw [hDiv']
            ring

    have hLower :
        κ * h3FourierGradientMagnitude ξ * ‖g 2‖
          ≤
        ‖h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2‖ := by
      calc
        κ * h3FourierGradientMagnitude ξ * ‖g 2‖
            ≤
          ‖h3FourierDerivativeSymbol (2 : Fin 3) ξ‖ * ‖g 2‖ :=
            mul_le_mul_of_nonneg_right
              hGood
              (norm_nonneg _)
        _ =
          ‖h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2‖ := by
            rw [norm_mul]

    have hUpper :
        ‖h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2‖
          ≤
        h3FourierGradientMagnitude ξ * (‖g 0‖ + ‖g 1‖) := by
      rw [hEq, norm_neg]
      calc
        ‖h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0
            +
          h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1‖
            ≤
          ‖h3FourierDerivativeSymbol (0 : Fin 3) ξ * g 0‖
            +
          ‖h3FourierDerivativeSymbol (1 : Fin 3) ξ * g 1‖ :=
            norm_add_le _ _
        _ =
          ‖h3FourierDerivativeSymbol (0 : Fin 3) ξ‖ * ‖g 0‖
            +
          ‖h3FourierDerivativeSymbol (1 : Fin 3) ξ‖ * ‖g 1‖ := by
            rw [norm_mul, norm_mul]
        _ ≤
          h3FourierGradientMagnitude ξ * ‖g 0‖
            +
          h3FourierGradientMagnitude ξ * ‖g 1‖ := by
            exact
              add_le_add
                (mul_le_mul_of_nonneg_right hD0 (norm_nonneg _))
                (mul_le_mul_of_nonneg_right hD1 (norm_nonneg _))
        _ =
          h3FourierGradientMagnitude ξ * (‖g 0‖ + ‖g 1‖) := by
            ring

    have hScaled :
        h3FourierGradientMagnitude ξ * (κ * ‖g 2‖)
          ≤
        h3FourierGradientMagnitude ξ * (‖g 0‖ + ‖g 1‖) := by
      calc
        h3FourierGradientMagnitude ξ * (κ * ‖g 2‖)
            =
          κ * h3FourierGradientMagnitude ξ * ‖g 2‖ := by
            ring
        _ ≤
          ‖h3FourierDerivativeSymbol (2 : Fin 3) ξ * g 2‖ :=
            hLower
        _ ≤
          h3FourierGradientMagnitude ξ * (‖g 0‖ + ‖g 1‖) :=
            hUpper

    have hCancel :
        κ * ‖g 2‖
          ≤
        ‖g 0‖ + ‖g 1‖ := by

      by_contra hNot

      have hStrict :
          ‖g 0‖ + ‖g 1‖
            <
          κ * ‖g 2‖ :=
        lt_of_not_ge hNot

      have hStrictScaled :
          h3FourierGradientMagnitude ξ * (‖g 0‖ + ‖g 1‖)
            <
          h3FourierGradientMagnitude ξ * (κ * ‖g 2‖) :=
        mul_lt_mul_of_pos_left
          hStrict
          hGradPos

      exact
        (not_lt_of_ge hScaled)
          hStrictScaled

    simpa [h3TerminalTransverseSpectralMagnitude] using hCancel

/-! ## Difference form -/

/--
The pointwise good-cone estimate is stable under subtraction of two
divergence-free spectral vectors.

This is the form used for endpoint Cauchy estimates.
-/
theorem mul_norm_longitudinal_sub_le_transverse_of_divergenceFree_of_mem_goodCone
    {i : Fin 3}
    {κ : ℝ}
    (hκ : 0 < κ)
    {ξ : H3FourierPoint3}
    (hξ : ξ ≠ 0)
    {g h : Fin 3 → ℂ}
    (hDivG :
      (∑ j : Fin 3,
        h3FourierDerivativeSymbol j ξ * g j)
        =
      0)
    (hDivH :
      (∑ j : Fin 3,
        h3FourierDerivativeSymbol j ξ * h j)
        =
      0)
    (hGood :
      ξ ∈ h3TerminalLongitudinalAngularGoodCone i κ) :
    κ * ‖g i - h i‖
      ≤
    h3TerminalTransverseSpectralMagnitude
      i
      (fun j => g j - h j) := by

  have hDivSub :
      (∑ j : Fin 3,
        h3FourierDerivativeSymbol j ξ * (g j - h j))
        =
      0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hDivG, hDivH]
    exact sub_self 0

  exact
    mul_norm_longitudinal_le_transverse_of_divergenceFree_of_mem_goodCone
      hκ
      hξ
      hDivSub
      hGood

end

end Euclidean
end Bridge
end PrimeTensor
