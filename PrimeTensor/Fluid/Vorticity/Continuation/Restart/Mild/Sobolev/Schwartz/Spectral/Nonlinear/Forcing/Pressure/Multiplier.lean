import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.L1

/-!
# Fourier pressure multiplier from the Leray complement

The unprojected H³ nonlinear forcing is

    F = div (u ⊗ u),

while the mild equation uses its Leray projection `P F`.

The finite Leray symbol in this project is defined from the exact Fourier
derivative symbols

    dᵢ(ξ) = 2π i ξᵢ

by

    Pᵢₖ(ξ)
      = δᵢₖ
        - dᵢ(ξ) conj(dₖ(ξ)) / Q(ξ),

where `Q` is the total Fourier gradient square.  At `Q = 0` the rank-one term
is defined to be zero.

Consequently the scalar Leray-complement coefficient is

    q(ξ) =
      (Σₖ conj(dₖ(ξ)) Fₖ(ξ)) / Q(ξ)

away from zero gradient frequency, and zero there.  Then

    Fᵢ - (P F)ᵢ = dᵢ q.

The real momentum interface uses the pressure force `-∂ᵢ p`, so the pressure
Fourier multiplier must be

    p̂ = -q.

This file records those identities pointwise in frequency.  No inverse Fourier
regularity is used yet; that is the next analytic layer.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- Scalar coefficient of the rank-one Leray complement applied to the raw
outer-product divergence.  It is set to zero at zero gradient frequency, in
the same convention as `h3LerayRankOneCoefficient`. -/
noncomputable def h3RawFinLerayComplementScalar
    (U V : H3SpectralFinVectorState)
    (ξ : H3FourierPoint3) : ℂ :=
  if _hq : h3FourierGradientSquare ξ = 0 then
    0
  else
    (∑ k : Fin 3,
        star (h3FourierDerivativeSymbol k ξ) *
          h3RawFinOuterProductDivergence U V k ξ) /
      (h3FourierGradientSquare ξ : ℂ)

/-- Fourier pressure chosen with the sign convention of
`RealFluid.pressureForceComponent = -∂p`. -/
noncomputable def h3RawFinPressureFourier
    (U V : H3SpectralFinVectorState)
    (ξ : H3FourierPoint3) : ℂ :=
  - h3RawFinLerayComplementScalar U V ξ

/-- The finite Kronecker delta acts as the identity under the coordinate sum. -/
theorem sum_h3LerayDelta_mul_pressure
    (F : Fin 3 → ℂ)
    (i : Fin 3) :
    (∑ k : Fin 3,
      h3LerayDelta i k * F k)
      =
    F i := by
  simp [h3LerayDelta, eq_comm]

/-- The unprojected forcing minus its Leray projection is exactly the
rank-one gradient-direction part. -/
theorem h3RawFinOuterProductDivergence_sub_leray_eq_derivative_mul_complement
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinOuterProductDivergence U V i ξ
        -
      h3RawFinLerayOuterProductDivergence U V i ξ
      =
    h3FourierDerivativeSymbol i ξ *
      h3RawFinLerayComplementScalar U V ξ := by
  let F : Fin 3 → ℂ :=
    fun k =>
      h3RawFinOuterProductDivergence U V k ξ

  have hDelta :
      (∑ k : Fin 3,
        h3LerayDelta i k * F k)
        =
      F i := by
    exact sum_h3LerayDelta_mul_pressure F i

  by_cases hq : h3FourierGradientSquare ξ = 0
  · have hProjected :
        (∑ k : Fin 3,
          h3LerayCoefficient ξ i k * F k)
          =
        F i := by
      calc
        (∑ k : Fin 3,
          h3LerayCoefficient ξ i k * F k)
            =
          ∑ k : Fin 3,
            h3LerayDelta i k * F k := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [
                h3LerayCoefficient_of_gradientSquare_eq_zero
                  hq i k
              ]
        _ = F i := hDelta

    change
      F i
          -
        (∑ k : Fin 3,
          h3LerayCoefficient ξ i k * F k)
        =
      h3FourierDerivativeSymbol i ξ *
        h3RawFinLerayComplementScalar U V ξ

    rw [hProjected]
    simp [h3RawFinLerayComplementScalar, hq]

  · have hRank :
        (∑ k : Fin 3,
          h3LerayRankOneCoefficient ξ i k * F k)
          =
        h3FourierDerivativeSymbol i ξ *
          (
            (∑ k : Fin 3,
              star (h3FourierDerivativeSymbol k ξ) * F k) /
            (h3FourierGradientSquare ξ : ℂ)
          ) := by
      simp only [
        h3LerayRankOneCoefficient,
        dif_neg hq
      ]
      calc
        (∑ k : Fin 3,
          (
            h3FourierDerivativeSymbol i ξ *
              star (h3FourierDerivativeSymbol k ξ) /
              (h3FourierGradientSquare ξ : ℂ)
          ) * F k)
            =
          ∑ k : Fin 3,
            h3FourierDerivativeSymbol i ξ *
              (
                (
                  star (h3FourierDerivativeSymbol k ξ) *
                    F k
                ) /
                (h3FourierGradientSquare ξ : ℂ)
              ) := by
                apply Finset.sum_congr rfl
                intro k hk
                ring
        _ =
          h3FourierDerivativeSymbol i ξ *
            (∑ k : Fin 3,
              (
                star (h3FourierDerivativeSymbol k ξ) *
                  F k
              ) /
              (h3FourierGradientSquare ξ : ℂ)) := by
                rw [Finset.mul_sum]
        _ =
          h3FourierDerivativeSymbol i ξ *
            (
              (∑ k : Fin 3,
                star (h3FourierDerivativeSymbol k ξ) * F k) /
              (h3FourierGradientSquare ξ : ℂ)
            ) := by
                rw [Finset.sum_div]

    have hProjected :
        (∑ k : Fin 3,
          h3LerayCoefficient ξ i k * F k)
          =
        F i
          -
        (∑ k : Fin 3,
          h3LerayRankOneCoefficient ξ i k * F k) := by
      calc
        (∑ k : Fin 3,
          h3LerayCoefficient ξ i k * F k)
            =
          ∑ k : Fin 3,
            (
              h3LerayDelta i k * F k
                -
              h3LerayRankOneCoefficient ξ i k * F k
            ) := by
              apply Finset.sum_congr rfl
              intro k hk
              unfold h3LerayCoefficient
              ring
        _ =
          (∑ k : Fin 3,
            h3LerayDelta i k * F k)
            -
          (∑ k : Fin 3,
            h3LerayRankOneCoefficient ξ i k * F k) := by
              rw [Finset.sum_sub_distrib]
        _ =
          F i
            -
          (∑ k : Fin 3,
            h3LerayRankOneCoefficient ξ i k * F k) := by
              rw [hDelta]

    change
      F i
          -
        (∑ k : Fin 3,
          h3LerayCoefficient ξ i k * F k)
        =
      h3FourierDerivativeSymbol i ξ *
        h3RawFinLerayComplementScalar U V ξ

    rw [hProjected]
    simp only [
      h3RawFinLerayComplementScalar,
      dif_neg hq
    ]
    rw [hRank]
    ring

/-- With the project's pressure sign convention, the Leray complement is
exactly the negative Fourier gradient of pressure. -/
theorem h3RawFinOuterProductDivergence_sub_leray_eq_neg_derivative_mul_pressure
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinOuterProductDivergence U V i ξ
        -
      h3RawFinLerayOuterProductDivergence U V i ξ
      =
    -(
      h3FourierDerivativeSymbol i ξ *
        h3RawFinPressureFourier U V ξ
    ) := by
  rw [
    h3RawFinOuterProductDivergence_sub_leray_eq_derivative_mul_complement
  ]
  unfold h3RawFinPressureFourier
  ring

/-- Equivalent PDE-oriented form: the Leray-projected forcing is the raw
forcing plus the Fourier pressure gradient. -/
theorem h3RawFinLerayOuterProductDivergence_eq_raw_add_derivative_mul_pressure
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergence U V i ξ
      =
    h3RawFinOuterProductDivergence U V i ξ
      +
    h3FourierDerivativeSymbol i ξ *
      h3RawFinPressureFourier U V ξ := by
  have hComplement :=
    h3RawFinOuterProductDivergence_sub_leray_eq_neg_derivative_mul_pressure
      U V i ξ

  calc
    h3RawFinLerayOuterProductDivergence U V i ξ
        =
      h3RawFinOuterProductDivergence U V i ξ
        -
      (
        h3RawFinOuterProductDivergence U V i ξ
          -
        h3RawFinLerayOuterProductDivergence U V i ξ
      ) := by
        ring
    _ =
      h3RawFinOuterProductDivergence U V i ξ
        -
      (-
        (
          h3FourierDerivativeSymbol i ξ *
            h3RawFinPressureFourier U V ξ
        )
      ) := by
        rw [hComplement]
    _ =
      h3RawFinOuterProductDivergence U V i ξ
        +
      h3FourierDerivativeSymbol i ξ *
        h3RawFinPressureFourier U V ξ := by
        ring

end

end Euclidean
end Bridge
end PrimeTensor
