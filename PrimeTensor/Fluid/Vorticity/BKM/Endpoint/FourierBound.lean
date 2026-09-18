import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.FourierMultiplier

/-!
# BKM endpoint: uniform bounds for the Fourier Biot--Savart coefficients

`FourierMultiplier` produced the exact off-zero-frequency reconstruction

    ∂ᵢ ûⱼ = homogeneous degree-zero coefficients × curl amplitudes.

This file turns those formulas into estimates.

The scalar coefficient

    mᵢₖ(ξ) = ξᵢ ξₖ / |ξ|²

is defined to be zero at the origin.  Each Euclidean coordinate of `ξ` has
absolute value at most `‖ξ‖`, so

    |ξᵢ ξₖ| ≤ ‖ξ‖² = |ξ|²,

and therefore

    ‖mᵢₖ(ξ)‖ ≤ 1.

Substituting these coefficients into the three Biot--Savart identities gives
the pointwise estimates

    ‖∂ᵢ û₀‖ ≤ ‖C₀₁‖ + ‖C₀₂‖,
    ‖∂ᵢ û₁‖ ≤ ‖C₀₁‖ + ‖C₁₂‖,
    ‖∂ᵢ û₂‖ ≤ ‖C₀₂‖ + ‖C₁₂‖.

These are the degree-zero bounds needed for the middle-frequency logarithmic
piece of the BKM endpoint argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointFourierBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The real BKM radius is exactly the squared Euclidean norm. -/
theorem h3BKMFourierRadiusSqReal_eq_norm_sq
    (ξ : H3FourierPoint3) :
    h3BKMFourierRadiusSqReal ξ = ‖ξ‖ ^ 2 := by
  calc
    h3BKMFourierRadiusSqReal ξ
        =
      ∑ a : PrimeTensor.Axis Depth.three, (ξ a) ^ 2 := by
        unfold h3BKMFourierRadiusSqReal
        rw [axis_sum_three]
        simp only [
          h3AxisOfFin3_zero,
          h3AxisOfFin3_one,
          h3AxisOfFin3_two
        ]
        ring
    _ = ‖ξ‖ ^ 2 :=
      (h3FourierPoint3_norm_sq_eq_sum_coordinates ξ).symm

/-- Every Fourier coordinate is bounded by the Euclidean norm. -/
theorem abs_h3BKMFourierCoordinate_le_norm
    (ξ : H3FourierPoint3)
    (i : Fin 3) :
    |ξ (h3AxisOfFin3 i)| ≤ ‖ξ‖ := by
  simpa only [Real.norm_eq_abs] using
    (PiLp.norm_apply_le
      ξ
      (h3AxisOfFin3 i))

/-- Every product of two Fourier coordinates is bounded by the squared radius. -/
theorem abs_mul_abs_h3BKMFourierCoordinate_le_radiusSq
    (ξ : H3FourierPoint3)
    (i k : Fin 3) :
    |ξ (h3AxisOfFin3 i)|
        *
      |ξ (h3AxisOfFin3 k)|
      ≤
    h3BKMFourierRadiusSqReal ξ := by

  have hi :
      |ξ (h3AxisOfFin3 i)| ≤ ‖ξ‖ :=
    abs_h3BKMFourierCoordinate_le_norm
      ξ i

  have hk :
      |ξ (h3AxisOfFin3 k)| ≤ ‖ξ‖ :=
    abs_h3BKMFourierCoordinate_le_norm
      ξ k

  rw [h3BKMFourierRadiusSqReal_eq_norm_sq]

  calc
    |ξ (h3AxisOfFin3 i)|
          *
        |ξ (h3AxisOfFin3 k)|
        ≤
      ‖ξ‖ * ‖ξ‖ := by
        exact
          mul_le_mul
            hi hk
            (abs_nonneg _)
            (norm_nonneg _)

    _ = ‖ξ‖ ^ 2 := by
      ring

/--
Homogeneous degree-zero coordinate coefficient.

At zero frequency it is defined to be zero.
-/
noncomputable def h3BKMCoordinateCoefficient
    (ξ : H3FourierPoint3)
    (i k : Fin 3) : ℂ :=
  if hR : h3BKMFourierRadiusSqReal ξ = 0 then
    0
  else
    (
      (ξ (h3AxisOfFin3 i) : ℂ)
        *
      (ξ (h3AxisOfFin3 k) : ℂ)
    )
      /
    h3BKMFourierRadiusSq ξ

/-- Every homogeneous BKM coordinate coefficient has norm at most one. -/
theorem norm_h3BKMCoordinateCoefficient_le_one
    (ξ : H3FourierPoint3)
    (i k : Fin 3) :
    ‖h3BKMCoordinateCoefficient ξ i k‖ ≤ 1 := by

  by_cases hR :
      h3BKMFourierRadiusSqReal ξ = 0

  · simp [
      h3BKMCoordinateCoefficient,
      hR
    ]

  · have hRNonneg :
        0 ≤ h3BKMFourierRadiusSqReal ξ :=
      h3BKMFourierRadiusSqReal_nonneg ξ

    have hRPos :
        0 < h3BKMFourierRadiusSqReal ξ :=
      lt_of_le_of_ne
        hRNonneg
        (Ne.symm hR)

    have hNum :
        |ξ (h3AxisOfFin3 i)|
            *
          |ξ (h3AxisOfFin3 k)|
          ≤
        h3BKMFourierRadiusSqReal ξ :=
      abs_mul_abs_h3BKMFourierCoordinate_le_radiusSq
        ξ i k

    rw [
      h3BKMCoordinateCoefficient,
      dif_neg hR,
      norm_div,
      norm_mul,
      Complex.norm_real,
      Complex.norm_real,
      h3BKMFourierRadiusSq_eq_ofReal,
      Complex.norm_real,
      Real.norm_eq_abs,
      Real.norm_eq_abs,
      Real.norm_eq_abs,
      abs_of_pos hRPos
    ]

    rw [div_le_iff₀ hRPos]

    simpa only [one_mul] using hNum

/--
Off zero frequency, the component-`0` Biot--Savart identity is a sum of two
bounded homogeneous coordinate multipliers applied to curl amplitudes.
-/
theorem h3BKM_gradient_component0_eq_coordinateCoefficients
    (ξ : H3FourierPoint3)
    (hξ : ξ ≠ 0)
    (g : Fin 3 → ℂ)
    (
      hDiv :
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * g j)
          =
        0
    )
    (i : Fin 3) :
    h3FourierDerivativeSymbol i ξ * g 0
      =
    h3BKMCoordinateCoefficient ξ i 1
        *
      h3BKMCurl01Amplitude ξ g
      +
    h3BKMCoordinateCoefficient ξ i 2
        *
      h3BKMCurl02Amplitude ξ g := by

  have hR :
      h3BKMFourierRadiusSqReal ξ ≠ 0 :=
    (
      h3BKMFourierRadiusSqReal_pos
        ξ hξ
    ).ne'

  rw [
    h3BKM_gradient_component0_eq_curl_div_radiusSq
      ξ hξ g hDiv i
  ]

  simp only [
    h3BKMCoordinateCoefficient,
    dif_neg hR,
    div_eq_mul_inv
  ]

  ring

/--
Off zero frequency, the component-`1` Biot--Savart identity is a signed sum of
two bounded homogeneous coordinate multipliers applied to curl amplitudes.
-/
theorem h3BKM_gradient_component1_eq_coordinateCoefficients
    (ξ : H3FourierPoint3)
    (hξ : ξ ≠ 0)
    (g : Fin 3 → ℂ)
    (
      hDiv :
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * g j)
          =
        0
    )
    (i : Fin 3) :
    h3FourierDerivativeSymbol i ξ * g 1
      =
    -
      (
        h3BKMCoordinateCoefficient ξ i 0
          *
        h3BKMCurl01Amplitude ξ g
      )
      +
    h3BKMCoordinateCoefficient ξ i 2
        *
      h3BKMCurl12Amplitude ξ g := by

  have hR :
      h3BKMFourierRadiusSqReal ξ ≠ 0 :=
    (
      h3BKMFourierRadiusSqReal_pos
        ξ hξ
    ).ne'

  rw [
    h3BKM_gradient_component1_eq_curl_div_radiusSq
      ξ hξ g hDiv i
  ]

  simp only [
    h3BKMCoordinateCoefficient,
    dif_neg hR,
    div_eq_mul_inv
  ]

  ring

/--
Off zero frequency, the component-`2` Biot--Savart identity is a signed sum of
two bounded homogeneous coordinate multipliers applied to curl amplitudes.
-/
theorem h3BKM_gradient_component2_eq_coordinateCoefficients
    (ξ : H3FourierPoint3)
    (hξ : ξ ≠ 0)
    (g : Fin 3 → ℂ)
    (
      hDiv :
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * g j)
          =
        0
    )
    (i : Fin 3) :
    h3FourierDerivativeSymbol i ξ * g 2
      =
    -
      (
        h3BKMCoordinateCoefficient ξ i 0
          *
        h3BKMCurl02Amplitude ξ g
      )
      -
    h3BKMCoordinateCoefficient ξ i 1
        *
      h3BKMCurl12Amplitude ξ g := by

  have hR :
      h3BKMFourierRadiusSqReal ξ ≠ 0 :=
    (
      h3BKMFourierRadiusSqReal_pos
        ξ hξ
    ).ne'

  rw [
    h3BKM_gradient_component2_eq_curl_div_radiusSq
      ξ hξ g hDiv i
  ]

  simp only [
    h3BKMCoordinateCoefficient,
    dif_neg hR,
    div_eq_mul_inv
  ]

  ring

/-- Pointwise multiplier bound for target velocity component `0`. -/
theorem norm_h3BKM_gradient_component0_le_curl
    (ξ : H3FourierPoint3)
    (hξ : ξ ≠ 0)
    (g : Fin 3 → ℂ)
    (
      hDiv :
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * g j)
          =
        0
    )
    (i : Fin 3) :
    ‖h3FourierDerivativeSymbol i ξ * g 0‖
      ≤
    ‖h3BKMCurl01Amplitude ξ g‖
      +
    ‖h3BKMCurl02Amplitude ξ g‖ := by

  rw [
    h3BKM_gradient_component0_eq_coordinateCoefficients
      ξ hξ g hDiv i
  ]

  calc
    ‖h3BKMCoordinateCoefficient ξ i 1
          * h3BKMCurl01Amplitude ξ g
        +
      h3BKMCoordinateCoefficient ξ i 2
          * h3BKMCurl02Amplitude ξ g‖
        ≤
      ‖h3BKMCoordinateCoefficient ξ i 1
          * h3BKMCurl01Amplitude ξ g‖
        +
      ‖h3BKMCoordinateCoefficient ξ i 2
          * h3BKMCurl02Amplitude ξ g‖ :=
      norm_add_le _ _

    _ =
      ‖h3BKMCoordinateCoefficient ξ i 1‖
          * ‖h3BKMCurl01Amplitude ξ g‖
        +
      ‖h3BKMCoordinateCoefficient ξ i 2‖
          * ‖h3BKMCurl02Amplitude ξ g‖ := by
      rw [norm_mul, norm_mul]

    _ ≤
      1 * ‖h3BKMCurl01Amplitude ξ g‖
        +
      1 * ‖h3BKMCurl02Amplitude ξ g‖ := by
      exact
        add_le_add
          (
            mul_le_mul_of_nonneg_right
              (norm_h3BKMCoordinateCoefficient_le_one ξ i 1)
              (norm_nonneg _)
          )
          (
            mul_le_mul_of_nonneg_right
              (norm_h3BKMCoordinateCoefficient_le_one ξ i 2)
              (norm_nonneg _)
          )

    _ =
      ‖h3BKMCurl01Amplitude ξ g‖
        +
      ‖h3BKMCurl02Amplitude ξ g‖ := by
      ring

/-- Pointwise multiplier bound for target velocity component `1`. -/
theorem norm_h3BKM_gradient_component1_le_curl
    (ξ : H3FourierPoint3)
    (hξ : ξ ≠ 0)
    (g : Fin 3 → ℂ)
    (
      hDiv :
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * g j)
          =
        0
    )
    (i : Fin 3) :
    ‖h3FourierDerivativeSymbol i ξ * g 1‖
      ≤
    ‖h3BKMCurl01Amplitude ξ g‖
      +
    ‖h3BKMCurl12Amplitude ξ g‖ := by

  rw [
    h3BKM_gradient_component1_eq_coordinateCoefficients
      ξ hξ g hDiv i
  ]

  calc
    ‖-
          (
            h3BKMCoordinateCoefficient ξ i 0
              * h3BKMCurl01Amplitude ξ g
          )
        +
      h3BKMCoordinateCoefficient ξ i 2
          * h3BKMCurl12Amplitude ξ g‖
        ≤
      ‖-
          (
            h3BKMCoordinateCoefficient ξ i 0
              * h3BKMCurl01Amplitude ξ g
          )‖
        +
      ‖h3BKMCoordinateCoefficient ξ i 2
          * h3BKMCurl12Amplitude ξ g‖ :=
      norm_add_le _ _

    _ =
      ‖h3BKMCoordinateCoefficient ξ i 0‖
          * ‖h3BKMCurl01Amplitude ξ g‖
        +
      ‖h3BKMCoordinateCoefficient ξ i 2‖
          * ‖h3BKMCurl12Amplitude ξ g‖ := by
      rw [norm_neg, norm_mul, norm_mul]

    _ ≤
      1 * ‖h3BKMCurl01Amplitude ξ g‖
        +
      1 * ‖h3BKMCurl12Amplitude ξ g‖ := by
      exact
        add_le_add
          (
            mul_le_mul_of_nonneg_right
              (norm_h3BKMCoordinateCoefficient_le_one ξ i 0)
              (norm_nonneg _)
          )
          (
            mul_le_mul_of_nonneg_right
              (norm_h3BKMCoordinateCoefficient_le_one ξ i 2)
              (norm_nonneg _)
          )

    _ =
      ‖h3BKMCurl01Amplitude ξ g‖
        +
      ‖h3BKMCurl12Amplitude ξ g‖ := by
      ring

/-- Pointwise multiplier bound for target velocity component `2`. -/
theorem norm_h3BKM_gradient_component2_le_curl
    (ξ : H3FourierPoint3)
    (hξ : ξ ≠ 0)
    (g : Fin 3 → ℂ)
    (
      hDiv :
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * g j)
          =
        0
    )
    (i : Fin 3) :
    ‖h3FourierDerivativeSymbol i ξ * g 2‖
      ≤
    ‖h3BKMCurl02Amplitude ξ g‖
      +
    ‖h3BKMCurl12Amplitude ξ g‖ := by

  rw [
    h3BKM_gradient_component2_eq_coordinateCoefficients
      ξ hξ g hDiv i
  ]

  calc
    ‖-
          (
            h3BKMCoordinateCoefficient ξ i 0
              * h3BKMCurl02Amplitude ξ g
          )
        -
      h3BKMCoordinateCoefficient ξ i 1
          * h3BKMCurl12Amplitude ξ g‖
        ≤
      ‖-
          (
            h3BKMCoordinateCoefficient ξ i 0
              * h3BKMCurl02Amplitude ξ g
          )‖
        +
      ‖h3BKMCoordinateCoefficient ξ i 1
          * h3BKMCurl12Amplitude ξ g‖ :=
      norm_sub_le _ _

    _ =
      ‖h3BKMCoordinateCoefficient ξ i 0‖
          * ‖h3BKMCurl02Amplitude ξ g‖
        +
      ‖h3BKMCoordinateCoefficient ξ i 1‖
          * ‖h3BKMCurl12Amplitude ξ g‖ := by
      rw [norm_neg, norm_mul, norm_mul]

    _ ≤
      1 * ‖h3BKMCurl02Amplitude ξ g‖
        +
      1 * ‖h3BKMCurl12Amplitude ξ g‖ := by
      exact
        add_le_add
          (
            mul_le_mul_of_nonneg_right
              (norm_h3BKMCoordinateCoefficient_le_one ξ i 0)
              (norm_nonneg _)
          )
          (
            mul_le_mul_of_nonneg_right
              (norm_h3BKMCoordinateCoefficient_le_one ξ i 1)
              (norm_nonneg _)
          )

    _ =
      ‖h3BKMCurl02Amplitude ξ g‖
        +
      ‖h3BKMCurl12Amplitude ξ g‖ := by
      ring

end

end Euclidean
end Bridge
end PrimeTensor
