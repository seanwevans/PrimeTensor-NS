import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.Encoder

/-!
# Fourth-order Fourier symbol algebra for H³ dissipation interpolation

The H³ terminal argument now forces the physical third-order energy block onto
an inverse-square terminal scale.  The exact viscous dissipation contains one
additional spatial derivative, so the next coercive bridge is the fourth
Fourier moment.

The existing spectral encoder already proves

    Σᵢ ‖mᵢ(ξ)‖² = q(ξ)

and

    Σᵢₖₗ ‖mᵢₖₗ(ξ)‖² = q(ξ)³,

where `q = h3FourierGradientSquare`.

This file adds the ordered fourth derivative symbol

    mᵢₖₗᵣ = mᵢₖₗ mᵣ

and proves the exact identity

    Σᵢₖₗᵣ ‖mᵢₖₗᵣ(ξ)‖² = q(ξ)⁴.

It also packages the corresponding pointwise fourth-moment density identity

    q(ξ)⁴ ‖F‖²
      =
    Σᵢₖₗᵣ ‖mᵢₖₗᵣ(ξ) F‖².

No PDE estimate is used here.  This is finite Fourier-symbol algebra only.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- Product of four coordinate-derivative symbols. -/
def h3FourierDerivativeSymbol4
    (i k l r : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol3 i k l ξ
    *
  h3FourierDerivativeSymbol r ξ

/--
The complete ordered fourth-symbol square sum is exactly the fourth power of
the canonical Fourier gradient square.
-/
theorem sum_norm_h3FourierDerivativeSymbol4_sq
    (ξ : H3FourierPoint3) :
    (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, ∑ r : Fin 3,
      ‖h3FourierDerivativeSymbol4 i k l r ξ‖ ^ 2)
      =
    (h3FourierGradientSquare ξ) ^ 4 := by

  simp_rw [
    h3FourierDerivativeSymbol4,
    norm_mul,
    mul_pow
  ]

  simp_rw [← Finset.mul_sum]

  rw [sum_norm_h3FourierDerivativeSymbol_sq]

  simp_rw [← Finset.sum_mul]

  rw [sum_norm_h3FourierDerivativeSymbol3_sq]

  ring

/--
Multiplying the fourth-symbol identity by one scalar Fourier density gives the
exact fourth moment density.
-/
theorem h3FourierGradientSquare_four_mul_norm_sq_eq_sum_symbol4
    (ξ : H3FourierPoint3)
    (F : ℂ) :
    h3FourierGradientSquare ξ ^ 4 * ‖F‖ ^ 2
      =
    ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, ∑ r : Fin 3,
      ‖h3FourierDerivativeSymbol4 i k l r ξ * F‖ ^ 2 := by

  rw [← sum_norm_h3FourierDerivativeSymbol4_sq ξ]

  simp_rw [
    norm_mul,
    mul_pow
  ]

  simp_rw [← Finset.sum_mul]

end

end Euclidean
end Bridge
end PrimeTensor
