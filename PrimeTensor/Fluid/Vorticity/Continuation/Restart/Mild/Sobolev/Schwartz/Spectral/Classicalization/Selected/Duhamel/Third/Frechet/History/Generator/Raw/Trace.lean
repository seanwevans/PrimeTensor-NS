import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Fifth.Coordinate.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.History.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Time.Laplacian

/-!
# Classicalization: third-Fréchet old-history generator raw trace

The third-Fréchet old-history quotient converges to the reconstruction of the
three-coordinate-multiplied zero-time heat generator

    d_a(ξ) d_b(ξ) d_c(ξ) G_t(ξ).

At zero elapsed heat time,

    G_t(ξ) = -ν q(ξ) A_t(ξ),

and the coordinate-symbol trace identity gives

    Σ_k d_k(ξ) d_k(ξ) = -q(ξ).

The fifth-coordinate selected-Duhamel multiplier is stored in the generic
Mathlib multilinear form.  We first expose that multiplier as the expected
ordered product of five coordinate symbols, then obtain

    d_a d_b d_c G_t
      =
    ν Σ_k d_a d_b d_c d_k d_k A_t.

No new estimate or inverse-Fourier argument is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelThirdFrechetHistoryGeneratorRawTrace
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The generic order-five Mathlib multiplier used by the selected Duhamel
reconstruction is exactly the ordered product of the five canonical Fourier
coordinate symbols. -/
theorem h3SelectedDuhamelFifthCoordinateRawAmplitude_eq_symbols
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a b c d e : Fin 3)
    (ξ : H3FourierPoint3) :
    h3SelectedDuhamelFifthCoordinateRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a b c d e ξ
      =
    h3FourierDerivativeSymbol a ξ *
      (h3FourierDerivativeSymbol b ξ *
        (h3FourierDerivativeSymbol c ξ *
          (h3FourierDerivativeSymbol d ξ *
            (h3FourierDerivativeSymbol e ξ *
              h3SelectedDuhamelRawFourierAmplitude
                ν A t hν U₀ hA hU₀ ht i ξ)))) := by
  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)
  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)
  let ec : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 c)
  let ed : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 d)
  let ee : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 e)

  have ha :
      h3FourierDerivativeSymbol a ξ
        =
      ((2 * Real.pi * inner ℝ ξ ea : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ea]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  have hb :
      h3FourierDerivativeSymbol b ξ
        =
      ((2 * Real.pi * inner ℝ ξ eb : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [eb]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  have hc :
      h3FourierDerivativeSymbol c ξ
        =
      ((2 * Real.pi * inner ℝ ξ ec : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ec]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  have hd :
      h3FourierDerivativeSymbol d ξ
        =
      ((2 * Real.pi * inner ℝ ξ ed : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ed]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  have he :
      h3FourierDerivativeSymbol e ξ
        =
      ((2 * Real.pi * inner ℝ ξ ee : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ee]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  unfold h3SelectedDuhamelFifthCoordinateRawAmplitude
  dsimp only

  simp only [
    VectorFourier.fourierPowSMulRight_apply,
    Fin.prod_univ_succ,
    Finset.univ_eq_empty,
    Finset.prod_empty,
    Matrix.cons_val_zero,
    Matrix.cons_val_one,
    Matrix.head_cons,
    Matrix.tail_cons,
    neg_apply,
    innerSL_apply_apply ℝ,
    smul_eq_mul
  ]

  rw [ha, hb, hc, hd, he]
  dsimp only [ea, eb, ec, ed, ee]
  simp [Complex.real_smul] <;> push_cast <;> ring

/-- The three-coordinate-multiplied zero-time old-history heat generator is
exactly viscosity times the raw trace of the three selected-Duhamel
fifth-coordinate multipliers. -/
theorem h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRawAmplitude_eq_viscosity_mul_fifthTrace
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a b c : Fin 3)
    (ξ : H3FourierPoint3) :
    h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a b c ξ
      =
    (ν : ℂ) *
      (∑ k : Fin 3,
        h3SelectedDuhamelFifthCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a b c k k ξ) := by
  unfold h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRawAmplitude
  unfold h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
  rw [
    h3SelectedDuhamelHistoryHeatRawAmplitude_zero
      hν U₀ hA hU₀ ht i
  ]

  have hFifth0 :=
    h3SelectedDuhamelFifthCoordinateRawAmplitude_eq_symbols
      ν A t hν U₀ hA hU₀ ht
      i a b c (0 : Fin 3) (0 : Fin 3) ξ

  have hFifth1 :=
    h3SelectedDuhamelFifthCoordinateRawAmplitude_eq_symbols
      ν A t hν U₀ hA hU₀ ht
      i a b c (1 : Fin 3) (1 : Fin 3) ξ

  have hFifth2 :=
    h3SelectedDuhamelFifthCoordinateRawAmplitude_eq_symbols
      ν A t hν U₀ hA hU₀ ht
      i a b c (2 : Fin 3) (2 : Fin 3) ξ

  have hTrace :=
    sum_h3FourierDerivativeSymbol_mul_self_eq_neg_gradientSquare ξ

  have hCoeff :
      (((-ν * h3FourierGradientSquare ξ : ℝ) : ℂ))
        =
      (ν : ℂ) * (-(h3FourierGradientSquare ξ : ℂ)) := by
    push_cast
    ring

  rw [hCoeff]
  rw [← hTrace]
  rw [Fin.sum_univ_three]
  rw [Fin.sum_univ_three]
  rw [hFifth0, hFifth1, hFifth2]
  ring

end

end Euclidean
end Bridge
end PrimeTensor
