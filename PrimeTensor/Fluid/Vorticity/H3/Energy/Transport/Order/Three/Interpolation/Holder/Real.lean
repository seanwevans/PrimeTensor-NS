import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Holder.Core

/-!
# Third-order H³ interpolation: generic real-field Hölder bridge

This file translates the green nonnegative 2-4-4 Hölder theorem to ordinary
real-valued fields over an arbitrary explicit measure.

Keeping the space and measure generic prevents PrimeTensor's `Point3` default
measure elaboration from contaminating the analytic Hölder layer.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators ENNReal NNReal

/--
Raw extended-real Lᵖ seminorm for a real-valued function with an explicit
measure.
-/
noncomputable def realLpEnorm
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (p : ℝ)
    (f : α → ℝ) : ℝ≥0∞ :=
  (
    ∫⁻ x : α,
      ‖f x‖ₑ ^ p
      ∂μ
  ) ^ (1 / p)

/--
For real-valued fields over an arbitrary explicit measure,

    ‖∫ f (g q)‖ₑ ≤ ‖f‖₂ ‖g‖₄ ‖q‖₄.

This is the direct real-field translation of the green nonnegative 2-4-4
Hölder core.
-/
theorem enorm_integral_three_mul_le_244
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    {f g q : α → ℝ}
    (
      hF :
        AEMeasurable
          (fun x : α => ‖f x‖ₑ)
          μ
    )
    (
      hG :
        AEMeasurable
          (fun x : α => ‖g x‖ₑ)
          μ
    )
    (
      hQ :
        AEMeasurable
          (fun x : α => ‖q x‖ₑ)
          μ
    ) :
    ‖
      ∫ x : α,
        f x * (g x * q x)
        ∂μ
    ‖ₑ
      ≤
    realLpEnorm μ 2 f
      *
    (
      realLpEnorm μ 4 g
        *
      realLpEnorm μ 4 q
    ) := by

  have hIntegral :
      ‖
        ∫ x : α,
          f x * (g x * q x)
          ∂μ
      ‖ₑ
        ≤
      ∫⁻ x : α,
        ‖f x * (g x * q x)‖ₑ
        ∂μ := by

    exact
      MeasureTheory.enorm_integral_le_lintegral_enorm
        (μ := μ)
        (fun x : α =>
          f x * (g x * q x))

  have hNormProduct :
      (
        ∫⁻ x : α,
          ‖f x * (g x * q x)‖ₑ
          ∂μ
      )
        =
      (
        ∫⁻ x : α,
          ‖f x‖ₑ
            *
          (‖g x‖ₑ * ‖q x‖ₑ)
          ∂μ
      ) := by

    apply lintegral_congr
    intro x
    rw [enorm_mul, enorm_mul]

  have hHolder :
      (
        ∫⁻ x : α,
          ‖f x‖ₑ
            *
          (‖g x‖ₑ * ‖q x‖ₑ)
          ∂μ
      )
        ≤
      realLpEnorm μ 2 f
        *
      (
        realLpEnorm μ 4 g
          *
        realLpEnorm μ 4 q
      ) := by

    unfold realLpEnorm

    exact
      lintegral_three_mul_le_244
        μ
        hF hG hQ

  calc
    ‖
      ∫ x : α,
        f x * (g x * q x)
        ∂μ
    ‖ₑ
        ≤
      ∫⁻ x : α,
        ‖f x * (g x * q x)‖ₑ
        ∂μ :=
      hIntegral

    _ =
      ∫⁻ x : α,
        ‖f x‖ₑ
          *
        (‖g x‖ₑ * ‖q x‖ₑ)
        ∂μ :=
      hNormProduct

    _ ≤
      realLpEnorm μ 2 f
        *
      (
        realLpEnorm μ 4 g
          *
        realLpEnorm μ 4 q
      ) :=
      hHolder

/--
The same real-field estimate with the factor `2` used by
`spatialEnergyPairing` kept explicit:

    ‖2 ∫ f (g q)‖ₑ
      ≤ ‖2‖ₑ ‖f‖₂ ‖g‖₄ ‖q‖₄.
-/
theorem enorm_two_mul_integral_three_mul_le_244
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    {f g q : α → ℝ}
    (
      hF :
        AEMeasurable
          (fun x : α => ‖f x‖ₑ)
          μ
    )
    (
      hG :
        AEMeasurable
          (fun x : α => ‖g x‖ₑ)
          μ
    )
    (
      hQ :
        AEMeasurable
          (fun x : α => ‖q x‖ₑ)
          μ
    ) :
    ‖
      2
        *
      (
        ∫ x : α,
          f x * (g x * q x)
          ∂μ
      )
    ‖ₑ
      ≤
    ‖(2 : ℝ)‖ₑ
      *
    (
      realLpEnorm μ 2 f
        *
      (
        realLpEnorm μ 4 g
          *
        realLpEnorm μ 4 q
      )
    ) := by

  have hMain :
      ‖
        ∫ x : α,
          f x * (g x * q x)
          ∂μ
      ‖ₑ
        ≤
      realLpEnorm μ 2 f
        *
      (
        realLpEnorm μ 4 g
          *
        realLpEnorm μ 4 q
      ) :=
    enorm_integral_three_mul_le_244
      μ hF hG hQ

  rw [enorm_mul]

  gcongr

end Euclidean
end Bridge
end PrimeTensor
