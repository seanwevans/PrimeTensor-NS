import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.WeightedConvolutionBilinear

/-!
# Bilinearity of the Fin-indexed H³ heat--Leray operator

`WeightedConvolutionBilinear` closes the genuinely nonlinear algebraic step:
the exact weighted H³ product convolution is additive and subtractive in both
arguments.

Everything above that layer is linear:

* finite tensor assembly,
* one-coordinate heat differentiation,
* finite divergence,
* the Fourier Leray multiplier,
* and the interval integral, once genuine Bochner integrability is available.

This file lifts the scalar convolution identities through those layers.

The instantaneous heat--Leray kernel and the retarded integrand are therefore
unconditionally bilinear.  For the actual interval-integrated Duhamel operator,
the diagonal subtraction identity is stated with exactly the four
`IntervalIntegrable` hypotheses needed by Mathlib's `integral_sub` and
`integral_add`.  This is intentional: Mathlib defines the integral of a
nonintegrable function to be zero, so global additivity would be false without
an integrability theorem.

The next analytic rung is now sharply identified: prove those retarded kernels
interval integrable for the continuous normalized path class.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Interval

noncomputable section

/-! ## Finite outer-product bilinearity -/

theorem h3SpectralFinOuterProduct_add_left
    (U V W : H3SpectralFinVectorState) :
    h3SpectralFinOuterProduct (U + V) W
      =
    h3SpectralFinOuterProduct U W +
      h3SpectralFinOuterProduct V W := by
  funext i j
  exact
    h3WeightedRawProductConvolutionL2_add_left
      (U i) (V i) (W j)

theorem h3SpectralFinOuterProduct_sub_left
    (U V W : H3SpectralFinVectorState) :
    h3SpectralFinOuterProduct (U - V) W
      =
    h3SpectralFinOuterProduct U W -
      h3SpectralFinOuterProduct V W := by
  funext i j
  exact
    h3WeightedRawProductConvolutionL2_sub_left
      (U i) (V i) (W j)

theorem h3SpectralFinOuterProduct_add_right
    (U V W : H3SpectralFinVectorState) :
    h3SpectralFinOuterProduct U (V + W)
      =
    h3SpectralFinOuterProduct U V +
      h3SpectralFinOuterProduct U W := by
  funext i j
  exact
    h3WeightedRawProductConvolutionL2_add_right
      (U i) (V j) (W j)

theorem h3SpectralFinOuterProduct_sub_right
    (U V W : H3SpectralFinVectorState) :
    h3SpectralFinOuterProduct U (V - W)
      =
    h3SpectralFinOuterProduct U V -
      h3SpectralFinOuterProduct U W := by
  funext i j
  exact
    h3WeightedRawProductConvolutionL2_sub_right
      (U i) (V j) (W j)

/-! ## Scalar heat-derivative multiplier linearity -/

theorem h3SpectralScalarHeatDerivativeApply_add
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (j : Fin 3)
    (F G : H3SpectralScalarState) :
    h3SpectralScalarHeatDerivativeApply
        ν t hν ht j (F + G)
      =
    h3SpectralScalarHeatDerivativeApply
        ν t hν ht j F
      +
    h3SpectralScalarHeatDerivativeApply
        ν t hν ht j G := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarHeatDerivativeApply_ae hν ht j (F + G),
    h3SpectralScalarHeatDerivativeApply_ae hν ht j F,
    h3SpectralScalarHeatDerivativeApply_ae hν ht j G,
    MeasureTheory.Lp.coeFn_add F G,
    MeasureTheory.Lp.coeFn_add
      (h3SpectralScalarHeatDerivativeApply ν t hν ht j F)
      (h3SpectralScalarHeatDerivativeApply ν t hν ht j G)
  ] with ξ hLeft hF hG hIn hOut
  rw [hLeft, hOut]
  change
    h3HeatDerivativeSymbol ν t j ξ *
        ((F + G : H3SpectralScalarState) :
          H3FourierPoint3 → ℂ) ξ
      =
    (h3SpectralScalarHeatDerivativeApply
        ν t hν ht j F :
      H3FourierPoint3 → ℂ) ξ
      +
    (h3SpectralScalarHeatDerivativeApply
        ν t hν ht j G :
      H3FourierPoint3 → ℂ) ξ
  rw [hIn, hF, hG]
  simp only [Pi.add_apply]
  ring

theorem h3SpectralScalarHeatDerivativeApply_sub
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (j : Fin 3)
    (F G : H3SpectralScalarState) :
    h3SpectralScalarHeatDerivativeApply
        ν t hν ht j (F - G)
      =
    h3SpectralScalarHeatDerivativeApply
        ν t hν ht j F
      -
    h3SpectralScalarHeatDerivativeApply
        ν t hν ht j G := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarHeatDerivativeApply_ae hν ht j (F - G),
    h3SpectralScalarHeatDerivativeApply_ae hν ht j F,
    h3SpectralScalarHeatDerivativeApply_ae hν ht j G,
    MeasureTheory.Lp.coeFn_sub F G,
    MeasureTheory.Lp.coeFn_sub
      (h3SpectralScalarHeatDerivativeApply ν t hν ht j F)
      (h3SpectralScalarHeatDerivativeApply ν t hν ht j G)
  ] with ξ hLeft hF hG hIn hOut
  rw [hLeft, hOut]
  change
    h3HeatDerivativeSymbol ν t j ξ *
        ((F - G : H3SpectralScalarState) :
          H3FourierPoint3 → ℂ) ξ
      =
    (h3SpectralScalarHeatDerivativeApply
        ν t hν ht j F :
      H3FourierPoint3 → ℂ) ξ
      -
    (h3SpectralScalarHeatDerivativeApply
        ν t hν ht j G :
      H3FourierPoint3 → ℂ) ξ
  rw [hIn, hF, hG]
  simp only [Pi.sub_apply]
  ring

/-! ## Finite heat-divergence linearity -/

theorem h3SpectralFinTensorHeatDivergenceApply_add
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (T S : H3SpectralFinTensorState) :
    h3SpectralFinTensorHeatDivergenceApply
        ν t hν ht (T + S)
      =
    h3SpectralFinTensorHeatDivergenceApply
        ν t hν ht T
      +
    h3SpectralFinTensorHeatDivergenceApply
        ν t hν ht S := by
  funext i
  unfold h3SpectralFinTensorHeatDivergenceApply
  simp only [Pi.add_apply,
    h3SpectralScalarHeatDerivativeApply_add,
    Finset.sum_add_distrib]

theorem h3SpectralFinTensorHeatDivergenceApply_sub
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (T S : H3SpectralFinTensorState) :
    h3SpectralFinTensorHeatDivergenceApply
        ν t hν ht (T - S)
      =
    h3SpectralFinTensorHeatDivergenceApply
        ν t hν ht T
      -
    h3SpectralFinTensorHeatDivergenceApply
        ν t hν ht S := by
  funext i
  unfold h3SpectralFinTensorHeatDivergenceApply
  simp only [Pi.sub_apply,
    h3SpectralScalarHeatDerivativeApply_sub,
    Finset.sum_sub_distrib]

/-! ## Pre-Leray velocity-kernel bilinearity -/

theorem h3SpectralFinVelocityHeatDivergenceApply_add_left
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V W : H3SpectralFinVectorState) :
    h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht (U + V) W
      =
    h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U W
      +
    h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht V W := by
  unfold h3SpectralFinVelocityHeatDivergenceApply
  rw [h3SpectralFinOuterProduct_add_left]
  exact
    h3SpectralFinTensorHeatDivergenceApply_add
      hν ht
      (h3SpectralFinOuterProduct U W)
      (h3SpectralFinOuterProduct V W)

theorem h3SpectralFinVelocityHeatDivergenceApply_sub_left
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V W : H3SpectralFinVectorState) :
    h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht (U - V) W
      =
    h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U W
      -
    h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht V W := by
  unfold h3SpectralFinVelocityHeatDivergenceApply
  rw [h3SpectralFinOuterProduct_sub_left]
  exact
    h3SpectralFinTensorHeatDivergenceApply_sub
      hν ht
      (h3SpectralFinOuterProduct U W)
      (h3SpectralFinOuterProduct V W)

theorem h3SpectralFinVelocityHeatDivergenceApply_add_right
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V W : H3SpectralFinVectorState) :
    h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U (V + W)
      =
    h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U V
      +
    h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U W := by
  unfold h3SpectralFinVelocityHeatDivergenceApply
  rw [h3SpectralFinOuterProduct_add_right]
  exact
    h3SpectralFinTensorHeatDivergenceApply_add
      hν ht
      (h3SpectralFinOuterProduct U V)
      (h3SpectralFinOuterProduct U W)

theorem h3SpectralFinVelocityHeatDivergenceApply_sub_right
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V W : H3SpectralFinVectorState) :
    h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U (V - W)
      =
    h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U V
      -
    h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U W := by
  unfold h3SpectralFinVelocityHeatDivergenceApply
  rw [h3SpectralFinOuterProduct_sub_right]
  exact
    h3SpectralFinTensorHeatDivergenceApply_sub
      hν ht
      (h3SpectralFinOuterProduct U V)
      (h3SpectralFinOuterProduct U W)

/-! ## Scalar Leray multiplier linearity -/

theorem h3SpectralScalarLerayCoefficientApply_add
    (i j : Fin 3)
    (F G : H3SpectralScalarState) :
    h3SpectralScalarLerayCoefficientApply i j (F + G)
      =
    h3SpectralScalarLerayCoefficientApply i j F +
      h3SpectralScalarLerayCoefficientApply i j G := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarLerayCoefficientApply_ae i j (F + G),
    h3SpectralScalarLerayCoefficientApply_ae i j F,
    h3SpectralScalarLerayCoefficientApply_ae i j G,
    MeasureTheory.Lp.coeFn_add F G,
    MeasureTheory.Lp.coeFn_add
      (h3SpectralScalarLerayCoefficientApply i j F)
      (h3SpectralScalarLerayCoefficientApply i j G)
  ] with ξ hLeft hF hG hIn hOut
  rw [hLeft, hOut]
  change
    h3LerayCoefficient ξ i j *
        ((F + G : H3SpectralScalarState) :
          H3FourierPoint3 → ℂ) ξ
      =
    (h3SpectralScalarLerayCoefficientApply i j F :
      H3FourierPoint3 → ℂ) ξ
      +
    (h3SpectralScalarLerayCoefficientApply i j G :
      H3FourierPoint3 → ℂ) ξ
  rw [hIn, hF, hG]
  simp only [Pi.add_apply]
  ring

theorem h3SpectralScalarLerayCoefficientApply_sub
    (i j : Fin 3)
    (F G : H3SpectralScalarState) :
    h3SpectralScalarLerayCoefficientApply i j (F - G)
      =
    h3SpectralScalarLerayCoefficientApply i j F -
      h3SpectralScalarLerayCoefficientApply i j G := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarLerayCoefficientApply_ae i j (F - G),
    h3SpectralScalarLerayCoefficientApply_ae i j F,
    h3SpectralScalarLerayCoefficientApply_ae i j G,
    MeasureTheory.Lp.coeFn_sub F G,
    MeasureTheory.Lp.coeFn_sub
      (h3SpectralScalarLerayCoefficientApply i j F)
      (h3SpectralScalarLerayCoefficientApply i j G)
  ] with ξ hLeft hF hG hIn hOut
  rw [hLeft, hOut]
  change
    h3LerayCoefficient ξ i j *
        ((F - G : H3SpectralScalarState) :
          H3FourierPoint3 → ℂ) ξ
      =
    (h3SpectralScalarLerayCoefficientApply i j F :
      H3FourierPoint3 → ℂ) ξ
      -
    (h3SpectralScalarLerayCoefficientApply i j G :
      H3FourierPoint3 → ℂ) ξ
  rw [hIn, hF, hG]
  simp only [Pi.sub_apply]
  ring

/-! ## Full Fin-indexed Leray linearity -/

theorem h3SpectralFinLerayApply_add
    (F G : H3SpectralFinVectorState) :
    h3SpectralFinLerayApply (F + G)
      =
    h3SpectralFinLerayApply F +
      h3SpectralFinLerayApply G := by
  funext i
  unfold h3SpectralFinLerayApply
  simp only [Pi.add_apply,
    h3SpectralScalarLerayCoefficientApply_add,
    Finset.sum_add_distrib]

theorem h3SpectralFinLerayApply_sub
    (F G : H3SpectralFinVectorState) :
    h3SpectralFinLerayApply (F - G)
      =
    h3SpectralFinLerayApply F -
      h3SpectralFinLerayApply G := by
  funext i
  unfold h3SpectralFinLerayApply
  simp only [Pi.sub_apply,
    h3SpectralScalarLerayCoefficientApply_sub,
    Finset.sum_sub_distrib]

/-! ## Full instantaneous heat--Leray bilinearity -/

theorem h3SpectralFinHeatLerayVelocityApply_add_left
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V W : H3SpectralFinVectorState) :
    h3SpectralFinHeatLerayVelocityApply
        ν t hν ht (U + V) W
      =
    h3SpectralFinHeatLerayVelocityApply
        ν t hν ht U W
      +
    h3SpectralFinHeatLerayVelocityApply
        ν t hν ht V W := by
  unfold h3SpectralFinHeatLerayVelocityApply
  rw [h3SpectralFinVelocityHeatDivergenceApply_add_left]
  exact
    h3SpectralFinLerayApply_add
      (h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U W)
      (h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht V W)

theorem h3SpectralFinHeatLerayVelocityApply_sub_left
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V W : H3SpectralFinVectorState) :
    h3SpectralFinHeatLerayVelocityApply
        ν t hν ht (U - V) W
      =
    h3SpectralFinHeatLerayVelocityApply
        ν t hν ht U W
      -
    h3SpectralFinHeatLerayVelocityApply
        ν t hν ht V W := by
  unfold h3SpectralFinHeatLerayVelocityApply
  rw [h3SpectralFinVelocityHeatDivergenceApply_sub_left]
  exact
    h3SpectralFinLerayApply_sub
      (h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U W)
      (h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht V W)

theorem h3SpectralFinHeatLerayVelocityApply_add_right
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V W : H3SpectralFinVectorState) :
    h3SpectralFinHeatLerayVelocityApply
        ν t hν ht U (V + W)
      =
    h3SpectralFinHeatLerayVelocityApply
        ν t hν ht U V
      +
    h3SpectralFinHeatLerayVelocityApply
        ν t hν ht U W := by
  unfold h3SpectralFinHeatLerayVelocityApply
  rw [h3SpectralFinVelocityHeatDivergenceApply_add_right]
  exact
    h3SpectralFinLerayApply_add
      (h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U V)
      (h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U W)

theorem h3SpectralFinHeatLerayVelocityApply_sub_right
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V W : H3SpectralFinVectorState) :
    h3SpectralFinHeatLerayVelocityApply
        ν t hν ht U (V - W)
      =
    h3SpectralFinHeatLerayVelocityApply
        ν t hν ht U V
      -
    h3SpectralFinHeatLerayVelocityApply
        ν t hν ht U W := by
  unfold h3SpectralFinHeatLerayVelocityApply
  rw [h3SpectralFinVelocityHeatDivergenceApply_sub_right]
  exact
    h3SpectralFinLerayApply_sub
      (h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U V)
      (h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U W)

/-! ## Retarded integrand bilinearity -/

theorem h3SpectralFinHeatLerayDuhamelIntegrand_sub_left
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V W : ℝ → H3SpectralFinVectorState)
    (s : ℝ) :
    h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν (U - V) W s
      =
    h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν U W s
      -
    h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν V W s := by
  by_cases hs : 0 < t - s
  · simp only [h3SpectralFinHeatLerayDuhamelIntegrand,
      hs, dite_true, Pi.sub_apply]
    exact
      h3SpectralFinHeatLerayVelocityApply_sub_left
        hν hs (U s) (V s) (W s)
  · simp [h3SpectralFinHeatLerayDuhamelIntegrand, hs]

theorem h3SpectralFinHeatLerayDuhamelIntegrand_sub_right
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V W : ℝ → H3SpectralFinVectorState)
    (s : ℝ) :
    h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν U (V - W) s
      =
    h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν U V s
      -
    h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν U W s := by
  by_cases hs : 0 < t - s
  · simp only [h3SpectralFinHeatLerayDuhamelIntegrand,
      hs, dite_true, Pi.sub_apply]
    exact
      h3SpectralFinHeatLerayVelocityApply_sub_right
        hν hs (U s) (V s) (W s)
  · simp [h3SpectralFinHeatLerayDuhamelIntegrand, hs]

/--
Pointwise Picard diagonal subtraction identity for the retarded heat--Leray
integrand.
-/
theorem h3SpectralFinHeatLerayDuhamelIntegrand_diagonal_sub
    {ν t : ℝ}
    (hν : 0 < ν)
    (X Y : ℝ → H3SpectralFinVectorState)
    (s : ℝ) :
    h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν X X s
      -
    h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν Y Y s
      =
    h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν (X - Y) X s
      +
    h3SpectralFinHeatLerayDuhamelIntegrand
        ν t hν Y (X - Y) s := by
  rw [
    h3SpectralFinHeatLerayDuhamelIntegrand_sub_left
      hν X Y X s,
    h3SpectralFinHeatLerayDuhamelIntegrand_sub_right
      hν Y X Y s
  ]
  abel

/-! ## Duhamel diagonal subtraction under genuine integrability -/

/--
Exact Picard diagonal subtraction identity for the actual Bochner interval
integral.

The four integrability hypotheses are precisely what makes interval integration
linear on these terms.  They will be discharged from normalized path
continuity/regularity in the next rung.
-/
theorem h3SpectralFinHeatLerayDuhamel_diagonal_sub
    {ν t : ℝ}
    (hν : 0 < ν)
    (X Y : ℝ → H3SpectralFinVectorState)
    (hXX :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν X X)
        volume 0 t)
    (hYY :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν Y Y)
        volume 0 t)
    (hDX :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν (X - Y) X)
        volume 0 t)
    (hYD :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν Y (X - Y))
        volume 0 t) :
    h3SpectralFinHeatLerayDuhamel
        ν t hν X X
      -
    h3SpectralFinHeatLerayDuhamel
        ν t hν Y Y
      =
    h3SpectralFinHeatLerayDuhamel
        ν t hν (X - Y) X
      +
    h3SpectralFinHeatLerayDuhamel
        ν t hν Y (X - Y) := by
  unfold h3SpectralFinHeatLerayDuhamel
  rw [
    ← intervalIntegral.integral_sub hXX hYY,
    ← intervalIntegral.integral_add hDX hYD
  ]
  apply intervalIntegral.integral_congr
  intro s _hs
  exact
    h3SpectralFinHeatLerayDuhamelIntegrand_diagonal_sub
      hν X Y s

end

end Euclidean
end Bridge
end PrimeTensor
