import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Fourier.Algebra

/-!
# BKM endpoint: pointwise Fourier Biot--Savart algebra

The remaining Landau/BKM analytic frontier is the logarithmic endpoint estimate
which controls the velocity gradient by vorticity and the H³ energy.

The first step is purely algebraic.

For a three-component Fourier velocity amplitude `g(ξ)`, write

    dᵢ(ξ) = 2π i ξᵢ

for the project derivative symbol and define the three pairwise curl amplitudes

    C₀₁ = d₁ g₀ - d₀ g₁,
    C₀₂ = d₂ g₀ - d₀ g₂,
    C₁₂ = d₂ g₁ - d₁ g₂.

If `g` is divergence free,

    d₀ g₀ + d₁ g₁ + d₂ g₂ = 0,

then each gradient multiplier is reconstructed from those curl amplitudes after
multiplication by `|ξ|²`.

This file proves the exact polynomial identities before dividing by `|ξ|²`.
Keeping the zero frequency in the statement avoids introducing any exceptional
set or measurable-space issue at this stage.  The next endpoint increment can
divide by the positive radius away from `ξ = 0` and begin the frequency split.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- Complexified Euclidean frequency radius squared. -/
def h3BKMFourierRadiusSq
    (ξ : H3FourierPoint3) : ℂ :=
  (ξ (h3AxisOfFin3 0) : ℂ) ^ 2
    +
  (ξ (h3AxisOfFin3 1) : ℂ) ^ 2
    +
  (ξ (h3AxisOfFin3 2) : ℂ) ^ 2

/-- Fourier amplitude of `∂₁u₀ - ∂₀u₁`. -/
def h3BKMCurl01Amplitude
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) : ℂ :=
  h3FourierDerivativeSymbol 1 ξ * g 0
    -
  h3FourierDerivativeSymbol 0 ξ * g 1

/-- Fourier amplitude of `∂₂u₀ - ∂₀u₂`. -/
def h3BKMCurl02Amplitude
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) : ℂ :=
  h3FourierDerivativeSymbol 2 ξ * g 0
    -
  h3FourierDerivativeSymbol 0 ξ * g 2

/-- Fourier amplitude of `∂₂u₁ - ∂₁u₂`. -/
def h3BKMCurl12Amplitude
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ) : ℂ :=
  h3FourierDerivativeSymbol 2 ξ * g 1
    -
  h3FourierDerivativeSymbol 1 ξ * g 2

/--
Cancel the common nonzero Fourier-derivative factor in the divergence relation.
-/
private theorem h3BKM_coordinate_divergence_eq_zero
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ)
    (
      hDiv :
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * g j)
          =
        0
    ) :
    (ξ (h3AxisOfFin3 0) : ℂ) * g 0
        +
      (ξ (h3AxisOfFin3 1) : ℂ) * g 1
        +
      (ξ (h3AxisOfFin3 2) : ℂ) * g 2
      =
    0 := by

  have hCommon :
      (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    Complex.two_pi_I_ne_zero

  have hFactored :
      (2 * Real.pi * Complex.I : ℂ)
          *
        (
          (ξ (h3AxisOfFin3 0) : ℂ) * g 0
            +
          (ξ (h3AxisOfFin3 1) : ℂ) * g 1
            +
          (ξ (h3AxisOfFin3 2) : ℂ) * g 2
        )
        =
      0 := by
    calc
      (2 * Real.pi * Complex.I : ℂ)
            *
          (
            (ξ (h3AxisOfFin3 0) : ℂ) * g 0
              +
            (ξ (h3AxisOfFin3 1) : ℂ) * g 1
              +
            (ξ (h3AxisOfFin3 2) : ℂ) * g 2
          )
          =
        h3FourierDerivativeSymbol 0 ξ * g 0
          +
        h3FourierDerivativeSymbol 1 ξ * g 1
          +
        h3FourierDerivativeSymbol 2 ξ * g 2 := by
            simp only [h3FourierDerivativeSymbol]
            ring

      _ = 0 := by
            simpa only [Fin.sum_univ_three] using hDiv

  exact
    (mul_eq_zero.mp hFactored).resolve_left hCommon

/--
Divergence-free Fourier algebra for the target velocity component `0`.

This is the numerator form of the Biot--Savart reconstruction:

    |ξ|² dᵢ g₀
      =
    ξᵢ (ξ₁ C₀₁ + ξ₂ C₀₂).
-/
theorem h3BKM_radiusSq_mul_gradient_component0_eq_curl
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ)
    (
      hDiv :
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * g j)
          =
        0
    )
    (i : Fin 3) :
    h3BKMFourierRadiusSq ξ
        *
      (h3FourierDerivativeSymbol i ξ * g 0)
      =
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
    ) := by

  have hDiv' :=
    h3BKM_coordinate_divergence_eq_zero
      ξ g hDiv

  unfold
    h3BKMFourierRadiusSq
    h3BKMCurl01Amplitude
    h3BKMCurl02Amplitude

  simp only [h3FourierDerivativeSymbol]

  linear_combination
    (
      (2 * Real.pi * Complex.I : ℂ)
        *
      (ξ (h3AxisOfFin3 i) : ℂ)
        *
      (ξ (h3AxisOfFin3 0) : ℂ)
    ) * hDiv'

/--
Divergence-free Fourier algebra for target velocity component `1`:

    |ξ|² dᵢ g₁
      =
    ξᵢ (-ξ₀ C₀₁ + ξ₂ C₁₂).
-/
theorem h3BKM_radiusSq_mul_gradient_component1_eq_curl
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ)
    (
      hDiv :
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * g j)
          =
        0
    )
    (i : Fin 3) :
    h3BKMFourierRadiusSq ξ
        *
      (h3FourierDerivativeSymbol i ξ * g 1)
      =
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
    ) := by

  have hDiv' :=
    h3BKM_coordinate_divergence_eq_zero
      ξ g hDiv

  unfold
    h3BKMFourierRadiusSq
    h3BKMCurl01Amplitude
    h3BKMCurl12Amplitude

  simp only [h3FourierDerivativeSymbol]

  linear_combination
    (
      (2 * Real.pi * Complex.I : ℂ)
        *
      (ξ (h3AxisOfFin3 i) : ℂ)
        *
      (ξ (h3AxisOfFin3 1) : ℂ)
    ) * hDiv'

/--
Divergence-free Fourier algebra for target velocity component `2`:

    |ξ|² dᵢ g₂
      =
    ξᵢ (-ξ₀ C₀₂ - ξ₁ C₁₂).
-/
theorem h3BKM_radiusSq_mul_gradient_component2_eq_curl
    (ξ : H3FourierPoint3)
    (g : Fin 3 → ℂ)
    (
      hDiv :
        (∑ j : Fin 3,
          h3FourierDerivativeSymbol j ξ * g j)
          =
        0
    )
    (i : Fin 3) :
    h3BKMFourierRadiusSq ξ
        *
      (h3FourierDerivativeSymbol i ξ * g 2)
      =
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
    ) := by

  have hDiv' :=
    h3BKM_coordinate_divergence_eq_zero
      ξ g hDiv

  unfold
    h3BKMFourierRadiusSq
    h3BKMCurl02Amplitude
    h3BKMCurl12Amplitude

  simp only [h3FourierDerivativeSymbol]

  linear_combination
    (
      (2 * Real.pi * Complex.I : ℂ)
        *
      (ξ (h3AxisOfFin3 i) : ℂ)
        *
      (ξ (h3AxisOfFin3 2) : ℂ)
    ) * hDiv'

end

end Euclidean
end Bridge
end PrimeTensor
