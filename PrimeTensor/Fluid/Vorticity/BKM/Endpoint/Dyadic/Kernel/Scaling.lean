import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Multiplier.Localized.Scaling
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.L1
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# BKM endpoint: dyadic kernel scaling and `L¹` mass invariance

The localized multiplier now satisfies the exact frequency-side dilation law

    Mᵢₖ,R(ξ) = Mᵢₖ,1(R⁻¹ ξ).

Passing through the inverse Fourier integral gives

    Kᵢₖ,R(x) = R³ Kᵢₖ,1(Rx).

The factor `R³` is exactly the Jacobian from the frequency change of variables.
Since the physical dimension is three, the same factor cancels against the
Jacobian in the `L¹` norm:

    ‖Kᵢₖ,R‖₁ = ‖Kᵢₖ,1‖₁.

This is the scale-independent kernel estimate required by the middle-frequency
BKM shell sum.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicKernelScaling
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Integral formula for the dyadic inverse-Fourier kernel. -/
theorem h3BKMDyadicKernel_eq_integral
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (x : H3FourierPoint3) :
    h3BKMDyadicKernel R hR i k x
      =
    ∫ ξ : H3FourierPoint3,
      Complex.exp
          (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
            Complex.I)
        *
      h3BKMLocalizedCoordinateMultiplierSchwartz
        R hR i k ξ
      ∂(volume : Measure H3FourierPoint3) := by

  unfold
    h3BKMDyadicKernel
    h3BKMDyadicKernelSchwartz

  rw [
    SchwartzMap.fourierInv_coe,
    Real.fourierInv_eq'
  ]

  simp only [smul_eq_mul]

/--
The scaled inverse-Fourier integrand is exactly the unit-scale integrand
composed with `R⁻¹ • ·`.
-/
theorem h3BKMDyadicKernel_scaled_integrand
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (x ξ : H3FourierPoint3) :
    Complex.exp
          (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
            Complex.I)
        *
      h3BKMLocalizedCoordinateMultiplierSchwartz
        R hR i k ξ
      =
    (
      fun η : H3FourierPoint3 =>
        Complex.exp
            (((2 * Real.pi *
                inner ℝ η (R • x) : ℝ) : ℂ) *
              Complex.I)
          *
        h3BKMLocalizedCoordinateMultiplierSchwartz
          (1 : ℝ) zero_lt_one i k η
    ) (R⁻¹ • ξ) := by

  rw [
    h3BKMLocalizedCoordinateMultiplierSchwartz_eq_unit_inv_smul
      hR i k ξ
  ]

  congr 1

  have hInner :
      inner ℝ (R⁻¹ • ξ) (R • x)
        =
      inner ℝ ξ x := by
    rw [
      real_inner_smul_left,
      real_inner_smul_right
    ]
    field_simp [hR.ne']

  rw [hInner]

/-- Exact physical-space scaling law for the Euclidean dyadic BKM kernel. -/
theorem h3BKMDyadicKernel_eq_unit_scale
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (x : H3FourierPoint3) :
    h3BKMDyadicKernel R hR i k x
      =
    (R ^ 3 : ℝ) •
      h3BKMDyadicKernel
        (1 : ℝ) zero_lt_one i k
        (R • x) := by

  rw [
    h3BKMDyadicKernel_eq_integral
      hR i k x
  ]

  have hChange :=
    Measure.integral_comp_inv_smul_of_nonneg
      (volume : Measure H3FourierPoint3)
      (fun η : H3FourierPoint3 =>
        Complex.exp
            (((2 * Real.pi *
                inner ℝ η (R • x) : ℝ) : ℂ) *
              Complex.I)
          *
        h3BKMLocalizedCoordinateMultiplierSchwartz
          (1 : ℝ) zero_lt_one i k η)
      hR.le

  rw [h3FourierPoint3_finrank] at hChange

  have hIntegralUnit :
      (∫ η : H3FourierPoint3,
          Complex.exp
              (((2 * Real.pi *
                  inner ℝ η (R • x) : ℝ) : ℂ) *
                Complex.I)
            *
          h3BKMLocalizedCoordinateMultiplierSchwartz
            (1 : ℝ) zero_lt_one i k η
          ∂(volume : Measure H3FourierPoint3))
        =
      h3BKMDyadicKernel
        (1 : ℝ) zero_lt_one i k
        (R • x) := by

    symm

    exact
      h3BKMDyadicKernel_eq_integral
        zero_lt_one i k (R • x)

  calc
    (∫ ξ : H3FourierPoint3,
        Complex.exp
            (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
              Complex.I)
          *
        h3BKMLocalizedCoordinateMultiplierSchwartz
          R hR i k ξ
        ∂(volume : Measure H3FourierPoint3))
        =
      ∫ ξ : H3FourierPoint3,
        (
          fun η : H3FourierPoint3 =>
            Complex.exp
                (((2 * Real.pi *
                    inner ℝ η (R • x) : ℝ) : ℂ) *
                  Complex.I)
              *
            h3BKMLocalizedCoordinateMultiplierSchwartz
              (1 : ℝ) zero_lt_one i k η
        ) (R⁻¹ • ξ)
        ∂(volume : Measure H3FourierPoint3) := by

      apply integral_congr_ae
      exact
        Filter.Eventually.of_forall
          (fun ξ =>
            h3BKMDyadicKernel_scaled_integrand
              hR i k x ξ)

    _ =
      (R ^ 3 : ℝ) •
        ∫ η : H3FourierPoint3,
          Complex.exp
              (((2 * Real.pi *
                  inner ℝ η (R • x) : ℝ) : ℂ) *
                Complex.I)
            *
          h3BKMLocalizedCoordinateMultiplierSchwartz
            (1 : ℝ) zero_lt_one i k η
          ∂(volume : Measure H3FourierPoint3) :=
      hChange

    _ =
      (R ^ 3 : ℝ) •
        h3BKMDyadicKernel
          (1 : ℝ) zero_lt_one i k
          (R • x) := by
      rw [hIntegralUnit]

/--
The `L¹` mass of every positive-radius dyadic kernel is exactly the unit-scale
mass.
-/
theorem h3BKMDyadicKernelL1Mass_eq_unit
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    h3BKMDyadicKernelL1Mass R hR i k
      =
    h3BKMDyadicKernelL1Mass
      (1 : ℝ) zero_lt_one i k := by

  unfold h3BKMDyadicKernelL1Mass

  have hChange :=
    Measure.integral_comp_smul_of_nonneg
      (volume : Measure H3FourierPoint3)
      (fun x : H3FourierPoint3 =>
        ‖h3BKMDyadicKernel
            (1 : ℝ) zero_lt_one i k x‖)
      R
      (hR := hR.le)

  rw [h3FourierPoint3_finrank] at hChange

  simp_rw [
    h3BKMDyadicKernel_eq_unit_scale
      hR i k,
    norm_smul,
    Real.norm_eq_abs,
    abs_of_pos (pow_pos hR 3)
  ]

  rw [
    integral_const_mul,
    hChange
  ]

  have hR3 : R ^ 3 ≠ 0 :=
    pow_ne_zero 3 hR.ne'

  simp only [smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hR3, one_mul]

/-- The physical transported kernel inherits the same unit-scale `L¹` mass. -/
theorem h3BKMDyadicPhysicalKernel_L1Mass_eq_unit
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (∫ x : Point3,
        ‖h3BKMDyadicPhysicalKernel R hR i k x‖
        ∂(volume : Measure Point3))
      =
    h3BKMDyadicKernelL1Mass
      (1 : ℝ) zero_lt_one i k := by

  rw [
    h3BKMDyadicPhysicalKernel_L1Mass_eq
      hR i k,
    h3BKMDyadicKernelL1Mass_eq_unit
      hR i k
  ]

end

end Euclidean
end Bridge
end PrimeTensor
