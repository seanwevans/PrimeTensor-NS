import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinLeraySymbol
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SpectralEncoder
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.FinHeatLeraySpectralDerivativeReality

/-!
# Finite Fourier algebra for the Leray-projected Navier--Stokes equation

The preterminal Navier--Stokes equation is normalized with viscosity one.  To
turn its Fourier transform into the velocity heat--Leray mild equation, two
finite-dimensional facts are needed at each frequency:

* the Leray matrix annihilates every Fourier gradient;
* the Leray matrix fixes every divergence-free Fourier vector.

This file proves those identities directly from the already-verified symbol

    Pᵢⱼ(ξ) = δᵢⱼ - dᵢ(ξ) star(dⱼ(ξ)) / q(ξ),

where `dᵢ(ξ) = 2π i ξᵢ` and `q(ξ) = Σᵢ ‖dᵢ(ξ)‖²`.

No PDE, time integration, or new analytic hypothesis enters here.  The next
rung can therefore apply these identities pointwise to the Fourier-transformed
preterminal momentum equation before performing variation of constants.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal ComplexConjugate

noncomputable section

noncomputable local instance axisFintypeH3FinLerayPDEAlgebra
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Elementary symbol identities -/

/-- The finite Kronecker matrix acts as the identity on a three-vector. -/
@[simp]
theorem sum_h3LerayDelta_mul
    (i : Fin 3)
    (z : Fin 3 → ℂ) :
    (∑ j : Fin 3, h3LerayDelta i j * z j) = z i := by
  classical
  simp [h3LerayDelta]

/-- Vanishing total gradient square forces every coordinate derivative symbol
    to vanish. -/
theorem h3FourierDerivativeSymbol_eq_zero_of_gradientSquare_eq_zero
    {ξ : H3FourierPoint3}
    (hξ : h3FourierGradientSquare ξ = 0)
    (i : Fin 3) :
    h3FourierDerivativeSymbol i ξ = 0 := by
  have hsum := sum_norm_h3FourierDerivativeSymbol_sq ξ
  rw [hξ] at hsum

  have hi_le :
      ‖h3FourierDerivativeSymbol i ξ‖ ^ 2
        ≤
      ∑ j : Fin 3, ‖h3FourierDerivativeSymbol j ξ‖ ^ 2 := by
    exact
      Finset.single_le_sum
        (fun j _ => sq_nonneg ‖h3FourierDerivativeSymbol j ξ‖)
        (Finset.mem_univ i)

  rw [hsum] at hi_le

  have hi_norm : ‖h3FourierDerivativeSymbol i ξ‖ = 0 := by
    nlinarith [norm_nonneg (h3FourierDerivativeSymbol i ξ)]

  exact norm_eq_zero.mp hi_norm

/-- Conjugation of the Fourier derivative symbol is just negation. -/
@[simp]
theorem conj_h3FourierDerivativeSymbol_eq_neg
    (j : Fin 3)
    (ξ : H3FourierPoint3) :
    conj (h3FourierDerivativeSymbol j ξ)
      = -h3FourierDerivativeSymbol j ξ := by
  calc
    conj (h3FourierDerivativeSymbol j ξ)
        = h3FourierDerivativeSymbol j (-ξ) :=
          (h3FourierDerivativeSymbol_neg_eq_conj j ξ).symm
    _ = -h3FourierDerivativeSymbol j ξ := by
          unfold h3FourierDerivativeSymbol
          simp

/-- The quadratic denominator of the Leray rank-one term is exactly the finite
    sum `Σ star(dⱼ) dⱼ`, viewed in `ℂ`. -/
theorem sum_star_h3FourierDerivativeSymbol_mul_eq_gradientSquare
    (ξ : H3FourierPoint3) :
    (∑ j : Fin 3,
        star (h3FourierDerivativeSymbol j ξ) *
          h3FourierDerivativeSymbol j ξ)
      =
    (h3FourierGradientSquare ξ : ℂ) := by
  calc
    (∑ j : Fin 3,
        star (h3FourierDerivativeSymbol j ξ) *
          h3FourierDerivativeSymbol j ξ)
        =
      ∑ j : Fin 3,
        (‖h3FourierDerivativeSymbol j ξ‖ ^ 2 : ℂ) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact
            RCLike.conj_mul
              (h3FourierDerivativeSymbol j ξ)
    _ =
      ((∑ j : Fin 3,
          ‖h3FourierDerivativeSymbol j ξ‖ ^ 2 : ℝ) : ℂ) := by
          norm_cast
    _ = (h3FourierGradientSquare ξ : ℂ) := by
          rw [sum_norm_h3FourierDerivativeSymbol_sq]

/-! ## Rank-one and Leray actions on a gradient -/

/-- The rank-one part of the Leray symbol sends the derivative-symbol vector
    to itself.  At zero frequency both sides vanish. -/
theorem sum_h3LerayRankOneCoefficient_mul_derivativeSymbol
    (ξ : H3FourierPoint3)
    (i : Fin 3) :
    (∑ j : Fin 3,
        h3LerayRankOneCoefficient ξ i j *
          h3FourierDerivativeSymbol j ξ)
      =
    h3FourierDerivativeSymbol i ξ := by
  by_cases hq : h3FourierGradientSquare ξ = 0
  · have hi :=
      h3FourierDerivativeSymbol_eq_zero_of_gradientSquare_eq_zero
        hq i
    simp [h3LerayRankOneCoefficient, hq, hi]
  · have hqC : (h3FourierGradientSquare ξ : ℂ) ≠ 0 := by
      exact_mod_cast hq

    calc
      (∑ j : Fin 3,
          h3LerayRankOneCoefficient ξ i j *
            h3FourierDerivativeSymbol j ξ)
          =
        ∑ j : Fin 3,
          (h3FourierDerivativeSymbol i ξ /
              (h3FourierGradientSquare ξ : ℂ)) *
            (star (h3FourierDerivativeSymbol j ξ) *
              h3FourierDerivativeSymbol j ξ) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [h3LerayRankOneCoefficient, dif_neg hq]
            ring
      _ =
        (h3FourierDerivativeSymbol i ξ /
            (h3FourierGradientSquare ξ : ℂ)) *
          (∑ j : Fin 3,
            star (h3FourierDerivativeSymbol j ξ) *
              h3FourierDerivativeSymbol j ξ) := by
            rw [Finset.mul_sum]
      _ =
        (h3FourierDerivativeSymbol i ξ /
            (h3FourierGradientSquare ξ : ℂ)) *
          (h3FourierGradientSquare ξ : ℂ) := by
            rw [sum_star_h3FourierDerivativeSymbol_mul_eq_gradientSquare]
      _ = h3FourierDerivativeSymbol i ξ := by
            field_simp

/-- The full Leray matrix annihilates the Fourier gradient vector. -/
theorem sum_h3LerayCoefficient_mul_derivativeSymbol_eq_zero
    (ξ : H3FourierPoint3)
    (i : Fin 3) :
    (∑ j : Fin 3,
        h3LerayCoefficient ξ i j *
          h3FourierDerivativeSymbol j ξ)
      = 0 := by
  calc
    (∑ j : Fin 3,
        h3LerayCoefficient ξ i j *
          h3FourierDerivativeSymbol j ξ)
        =
      (∑ j : Fin 3,
          h3LerayDelta i j *
            h3FourierDerivativeSymbol j ξ)
        -
      (∑ j : Fin 3,
          h3LerayRankOneCoefficient ξ i j *
            h3FourierDerivativeSymbol j ξ) := by
          simp_rw [h3LerayCoefficient, sub_mul]
          rw [Finset.sum_sub_distrib]
    _ =
      h3FourierDerivativeSymbol i ξ -
        h3FourierDerivativeSymbol i ξ := by
          rw [sum_h3LerayDelta_mul]
          rw [sum_h3LerayRankOneCoefficient_mul_derivativeSymbol]
    _ = 0 := sub_self _

/-- Consequently the Leray symbol kills an arbitrary scalar Fourier gradient. -/
theorem sum_h3LerayCoefficient_mul_gradient_eq_zero
    (ξ : H3FourierPoint3)
    (i : Fin 3)
    (pHat : ℂ) :
    (∑ j : Fin 3,
        h3LerayCoefficient ξ i j *
          (h3FourierDerivativeSymbol j ξ * pHat))
      = 0 := by
  calc
    (∑ j : Fin 3,
        h3LerayCoefficient ξ i j *
          (h3FourierDerivativeSymbol j ξ * pHat))
        =
      (∑ j : Fin 3,
          h3LerayCoefficient ξ i j *
            h3FourierDerivativeSymbol j ξ) * pHat := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = 0 := by
          rw [sum_h3LerayCoefficient_mul_derivativeSymbol_eq_zero]
          simp

/-! ## Leray action on divergence-free vectors -/

/-- A Fourier divergence-free relation can equivalently be written using the
    conjugated derivative symbols. -/
theorem sum_star_derivativeSymbol_mul_eq_zero_of_divergenceFree
    (ξ : H3FourierPoint3)
    (U : Fin 3 → ℂ)
    (hdiv :
      (∑ j : Fin 3,
        h3FourierDerivativeSymbol j ξ * U j) = 0) :
    (∑ j : Fin 3,
        star (h3FourierDerivativeSymbol j ξ) * U j) = 0 := by
  calc
    (∑ j : Fin 3,
        star (h3FourierDerivativeSymbol j ξ) * U j)
        =
      ∑ j : Fin 3,
        -(h3FourierDerivativeSymbol j ξ * U j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [show
            star (h3FourierDerivativeSymbol j ξ) =
              -h3FourierDerivativeSymbol j ξ by
                exact conj_h3FourierDerivativeSymbol_eq_neg j ξ]
          rw [neg_mul]
    _ = -(∑ j : Fin 3,
        h3FourierDerivativeSymbol j ξ * U j) := by
          rw [Finset.sum_neg_distrib]
    _ = 0 := by rw [hdiv, neg_zero]

/-- On a divergence-free Fourier vector, the rank-one correction vanishes. -/
theorem sum_h3LerayRankOneCoefficient_mul_eq_zero_of_divergenceFree
    (ξ : H3FourierPoint3)
    (i : Fin 3)
    (U : Fin 3 → ℂ)
    (hdiv :
      (∑ j : Fin 3,
        h3FourierDerivativeSymbol j ξ * U j) = 0) :
    (∑ j : Fin 3,
        h3LerayRankOneCoefficient ξ i j * U j) = 0 := by
  by_cases hq : h3FourierGradientSquare ξ = 0
  · simp [h3LerayRankOneCoefficient, hq]
  · have hstar :
      (∑ j : Fin 3,
        star (h3FourierDerivativeSymbol j ξ) * U j) = 0 :=
      sum_star_derivativeSymbol_mul_eq_zero_of_divergenceFree
        ξ U hdiv

    calc
      (∑ j : Fin 3,
          h3LerayRankOneCoefficient ξ i j * U j)
          =
        (h3FourierDerivativeSymbol i ξ /
            (h3FourierGradientSquare ξ : ℂ)) *
          (∑ j : Fin 3,
            star (h3FourierDerivativeSymbol j ξ) * U j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            rw [h3LerayRankOneCoefficient, dif_neg hq]
            ring
      _ = 0 := by rw [hstar, mul_zero]

/-- The Fourier Leray matrix fixes every divergence-free three-vector. -/
theorem sum_h3LerayCoefficient_mul_eq_of_divergenceFree
    (ξ : H3FourierPoint3)
    (i : Fin 3)
    (U : Fin 3 → ℂ)
    (hdiv :
      (∑ j : Fin 3,
        h3FourierDerivativeSymbol j ξ * U j) = 0) :
    (∑ j : Fin 3,
        h3LerayCoefficient ξ i j * U j)
      = U i := by
  calc
    (∑ j : Fin 3,
        h3LerayCoefficient ξ i j * U j)
        =
      (∑ j : Fin 3,
          h3LerayDelta i j * U j)
        -
      (∑ j : Fin 3,
          h3LerayRankOneCoefficient ξ i j * U j) := by
          simp_rw [h3LerayCoefficient, sub_mul]
          rw [Finset.sum_sub_distrib]
    _ = U i - 0 := by
          rw [sum_h3LerayDelta_mul]
          rw [sum_h3LerayRankOneCoefficient_mul_eq_zero_of_divergenceFree
            ξ i U hdiv]
    _ = U i := sub_zero _

end

end Euclidean
end Bridge
end PrimeTensor
