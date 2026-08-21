import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderThreeInterpolationAtom
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Third-order H³ interpolation: 2-4-4 Hölder core

Pure measure-theoretic Hölder composition.  The space and measure are explicit:
this lemma does not install or require a global `MeasureSpace` instance.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators ENNReal NNReal

/--
For nonnegative measurable functions,

    ‖F (G Q)‖₁ ≤ ‖F‖₂ ‖G‖₄ ‖Q‖₄.

The result is stated at the `lintegral`/`rpow` level used directly by mathlib's
Hölder theorem.
-/
theorem lintegral_three_mul_le_244_raw
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    {F G Q : α → ℝ≥0∞}
    (hF : AEMeasurable F μ)
    (hG : AEMeasurable G μ)
    (hQ : AEMeasurable Q μ) :
    (
      ∫⁻ x : α,
        (F * (G * Q)) x ^ (1 : ℝ) ∂μ
    ) ^ (1 / (1 : ℝ))
      ≤
    (
      (∫⁻ x : α, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
    )
      *
    (
      (
        (∫⁻ x : α, G x ^ (4 : ℝ) ∂μ) ^ (1 / (4 : ℝ))
      )
        *
      (
        (∫⁻ x : α, Q x ^ (4 : ℝ) ∂μ) ^ (1 / (4 : ℝ))
      )
    ) := by

  have h12 :
      (
        ∫⁻ x : α,
          (F * (G * Q)) x ^ (1 : ℝ) ∂μ
      ) ^ (1 / (1 : ℝ))
        ≤
      (
        (∫⁻ x : α, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
      )
        *
      (
        (∫⁻ x : α, (G * Q) x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
      ) := by

    exact
      ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr
        (p := (1 : ℝ))
        (q := (2 : ℝ))
        (r := (2 : ℝ))
        (by norm_num)
        (by norm_num)
        (by norm_num)
        μ
        hF
        (hG.mul hQ)

  have h24 :
      (
        (∫⁻ x : α, (G * Q) x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
      )
        ≤
      (
        (∫⁻ x : α, G x ^ (4 : ℝ) ∂μ) ^ (1 / (4 : ℝ))
      )
        *
      (
        (∫⁻ x : α, Q x ^ (4 : ℝ) ∂μ) ^ (1 / (4 : ℝ))
      ) := by

    exact
      ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr
        (p := (2 : ℝ))
        (q := (4 : ℝ))
        (r := (4 : ℝ))
        (by norm_num)
        (by norm_num)
        (by norm_num)
        μ
        hG
        hQ

  calc
    (
      ∫⁻ x : α,
        (F * (G * Q)) x ^ (1 : ℝ) ∂μ
    ) ^ (1 / (1 : ℝ))
        ≤
      (
        (∫⁻ x : α, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
      )
        *
      (
        (∫⁻ x : α, (G * Q) x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
      ) :=
      h12

    _ ≤
      (
        (∫⁻ x : α, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
      )
        *
      (
        (
          (∫⁻ x : α, G x ^ (4 : ℝ) ∂μ) ^ (1 / (4 : ℝ))
        )
          *
        (
          (∫⁻ x : α, Q x ^ (4 : ℝ) ∂μ) ^ (1 / (4 : ℝ))
        )
      ) := by
        gcongr

/--
The same estimate with the L¹ exponent simplified.
-/
theorem lintegral_three_mul_le_244
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    {F G Q : α → ℝ≥0∞}
    (hF : AEMeasurable F μ)
    (hG : AEMeasurable G μ)
    (hQ : AEMeasurable Q μ) :
    (∫⁻ x : α, F x * (G x * Q x) ∂μ)
      ≤
    (
      (∫⁻ x : α, F x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
    )
      *
    (
      (
        (∫⁻ x : α, G x ^ (4 : ℝ) ∂μ) ^ (1 / (4 : ℝ))
      )
        *
      (
        (∫⁻ x : α, Q x ^ (4 : ℝ) ∂μ) ^ (1 / (4 : ℝ))
      )
    ) := by

  simpa only [
    Pi.mul_apply,
    ENNReal.rpow_one,
    one_div,
    inv_one
  ] using
    lintegral_three_mul_le_244_raw
      μ hF hG hQ

end Euclidean
end Bridge
end PrimeTensor
