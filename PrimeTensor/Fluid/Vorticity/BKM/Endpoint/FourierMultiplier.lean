import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.FourierAlgebra

/-!
# BKM endpoint: Fourier Biot--Savart multipliers off zero frequency

`FourierAlgebra` proved the polynomial reconstruction identities

    |ξ|² dᵢ ĝⱼ = Nᵢⱼ(curl ĝ)

without dividing by the Fourier radius.

This file discharges the zero-frequency algebra cleanly:

* define the underlying real squared radius;
* prove it is strictly positive when `ξ ≠ 0`;
* identify the complex radius factor with the real one;
* divide the three reconstruction identities by that nonzero factor.

The result is the exact pointwise Fourier Biot--Savart multiplier formula
needed by the forthcoming low / middle / high frequency estimates.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- Ordinary real Euclidean squared radius of one project Fourier point. -/
def h3BKMFourierRadiusSqReal
    (ξ : H3FourierPoint3) : ℝ :=
  (ξ (h3AxisOfFin3 0)) ^ 2
    +
  (ξ (h3AxisOfFin3 1)) ^ 2
    +
  (ξ (h3AxisOfFin3 2)) ^ 2

/-- The real squared Fourier radius is always nonnegative. -/
theorem h3BKMFourierRadiusSqReal_nonneg
    (ξ : H3FourierPoint3) :
    0 ≤ h3BKMFourierRadiusSqReal ξ := by
  unfold h3BKMFourierRadiusSqReal
  positivity

/-- Away from the origin, the real squared Fourier radius is strictly positive. -/
theorem h3BKMFourierRadiusSqReal_pos
    (ξ : H3FourierPoint3)
    (hξ : ξ ≠ 0) :
    0 < h3BKMFourierRadiusSqReal ξ := by

  let a : ℝ :=
    ξ (h3AxisOfFin3 0)

  let b : ℝ :=
    ξ (h3AxisOfFin3 1)

  let c : ℝ :=
    ξ (h3AxisOfFin3 2)

  have hSumSqPos :
      0 < a ^ 2 + b ^ 2 + c ^ 2 := by

    by_contra hNot

    have hSumSqNonpos :
        a ^ 2 + b ^ 2 + c ^ 2 ≤ 0 :=
      le_of_not_gt hNot

    have ha0 :
        a = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]

    have hb0 :
        b = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]

    have hc0 :
        c = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]

    have hξ0 :
        ξ = 0 := by
      ext k
      cases k with
      | first =>
          change ξ xAxis = 0
          simpa [a] using ha0
      | next k =>
          cases k with
          | first =>
              change ξ yAxis = 0
              simpa [b] using hb0
          | next k =>
              cases k with
              | first =>
                  change ξ zAxis = 0
                  simpa [c] using hc0

    exact
      hξ hξ0

  simpa only [
    h3BKMFourierRadiusSqReal,
    a,
    b,
    c
  ] using
    hSumSqPos

/-- The complex radius factor used by the algebra is exactly the complexification
of the ordinary real squared radius. -/
theorem h3BKMFourierRadiusSq_eq_ofReal
    (ξ : H3FourierPoint3) :
    h3BKMFourierRadiusSq ξ
      =
    (h3BKMFourierRadiusSqReal ξ : ℂ) := by
  unfold
    h3BKMFourierRadiusSq
    h3BKMFourierRadiusSqReal

  simp only [
    Complex.ofReal_add,
    Complex.ofReal_pow
  ]

/-- The complex Fourier radius factor is nonzero away from `ξ = 0`. -/
theorem h3BKMFourierRadiusSq_ne_zero
    (ξ : H3FourierPoint3)
    (hξ : ξ ≠ 0) :
    h3BKMFourierRadiusSq ξ ≠ 0 := by

  rw [
    h3BKMFourierRadiusSq_eq_ofReal
  ]

  exact
    Complex.ofReal_ne_zero.mpr
      (
        h3BKMFourierRadiusSqReal_pos
          ξ hξ
      ).ne'

/--
Actual Biot--Savart multiplier formula for target velocity component `0`.
-/
theorem h3BKM_gradient_component0_eq_curl_div_radiusSq
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
    (
      (ξ (h3AxisOfFin3 i) : ℂ)
        *
      (
        (ξ (h3AxisOfFin3 1) : ℂ)
            *
          h3BKMCurl01Amplitude ξ g
          +
        (ξ (h3AxisOfFin3 2) : ℂ)
            *
          h3BKMCurl02Amplitude ξ g
      )
    )
      /
    h3BKMFourierRadiusSq ξ := by

  have hRadius :
      h3BKMFourierRadiusSq ξ ≠ 0 :=
    h3BKMFourierRadiusSq_ne_zero
      ξ hξ

  apply
    (eq_div_iff hRadius).2

  rw [mul_comm]

  exact
    h3BKM_radiusSq_mul_gradient_component0_eq_curl
      ξ g hDiv i

/--
Actual Biot--Savart multiplier formula for target velocity component `1`.
-/
theorem h3BKM_gradient_component1_eq_curl_div_radiusSq
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
    (
      (ξ (h3AxisOfFin3 i) : ℂ)
        *
      (
        -
          (ξ (h3AxisOfFin3 0) : ℂ)
            *
          h3BKMCurl01Amplitude ξ g
          +
        (ξ (h3AxisOfFin3 2) : ℂ)
            *
          h3BKMCurl12Amplitude ξ g
      )
    )
      /
    h3BKMFourierRadiusSq ξ := by

  have hRadius :
      h3BKMFourierRadiusSq ξ ≠ 0 :=
    h3BKMFourierRadiusSq_ne_zero
      ξ hξ

  apply
    (eq_div_iff hRadius).2

  rw [mul_comm]

  exact
    h3BKM_radiusSq_mul_gradient_component1_eq_curl
      ξ g hDiv i

/--
Actual Biot--Savart multiplier formula for target velocity component `2`.
-/
theorem h3BKM_gradient_component2_eq_curl_div_radiusSq
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
    (
      (ξ (h3AxisOfFin3 i) : ℂ)
        *
      (
        -
          (ξ (h3AxisOfFin3 0) : ℂ)
            *
          h3BKMCurl02Amplitude ξ g
          -
        (ξ (h3AxisOfFin3 1) : ℂ)
            *
          h3BKMCurl12Amplitude ξ g
      )
    )
      /
    h3BKMFourierRadiusSq ξ := by

  have hRadius :
      h3BKMFourierRadiusSq ξ ≠ 0 :=
    h3BKMFourierRadiusSq_ne_zero
      ξ hξ

  apply
    (eq_div_iff hRadius).2

  rw [mul_comm]

  exact
    h3BKM_radiusSq_mul_gradient_component2_eq_curl
      ξ g hDiv i

end

end Euclidean
end Bridge
end PrimeTensor
