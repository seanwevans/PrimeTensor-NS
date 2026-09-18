import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicKernelPhysical

/-!
# BKM endpoint: exact dilation law for the localized multiplier

The dyadic BKM kernel has now been constructed and transported to physical
space.  To prove a scale-independent `L¹` kernel bound, the first step is to
record the exact frequency-side scaling.

For every `R > 0`,

    Mᵢₖ,R(ξ) = Mᵢₖ,1(R⁻¹ ξ).

There are two ingredients:

* the radial shell satisfies the same dilation law;
* the degree-zero Biot--Savart coefficient is homogeneous of degree zero.

This file proves those facts separately and then combines them.  The next
checkpoint can feed the final multiplier identity into the inverse-Fourier
integral and use Mathlib's `integral_comp_smul` change-of-variables theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Function
open scoped Topology ContDiff SchwartzMap

noncomputable section

noncomputable local instance axisFintypeBKMEndpointLocalizedMultiplierScaling
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
A cutoff at radius `a * R` is the radius-`a` cutoff evaluated at the frequency
rescaled by `R⁻¹`.
-/
theorem h3BKMFrequencyCutoffBump_mul_radius
    {a R : ℝ}
    (ha : 0 < a)
    (hR : 0 < R)
    (ξ : H3FourierPoint3) :
    h3BKMFrequencyCutoffBump
        (a * R)
        (mul_pos ha hR)
        ξ
      =
    h3BKMFrequencyCutoffBump
        a ha
        (R⁻¹ • ξ) := by

  rw [
    h3BKMFrequencyCutoffBump_eq_unit_smul
      (mul_pos ha hR)
      ξ,
    h3BKMFrequencyCutoffBump_eq_unit_smul
      ha
      (R⁻¹ • ξ)
  ]

  congr 1

  simp only [smul_smul]

  congr 1

  field_simp [ha.ne', hR.ne']

/-- The dyadic shell at radius `R` is the unit shell evaluated at `R⁻¹ ξ`. -/
theorem h3BKMFrequencyShell_eq_unit_inv_smul
    {R : ℝ}
    (hR : 0 < R)
    (ξ : H3FourierPoint3) :
    h3BKMFrequencyShell R hR ξ
      =
    h3BKMFrequencyShell
      (1 : ℝ)
      zero_lt_one
      (R⁻¹ • ξ) := by

  unfold h3BKMFrequencyShell

  rw [
    h3BKMFrequencyCutoffBump_mul_radius
      (a := 2)
      (R := R)
      (by norm_num)
      hR
      ξ
  ]

  have hInner :
      h3BKMFrequencyCutoffBump
          R hR ξ
        =
      h3BKMFrequencyCutoffBump
          (1 : ℝ)
          zero_lt_one
          (R⁻¹ • ξ) := by
    simpa only [one_mul] using
      h3BKMFrequencyCutoffBump_mul_radius
        (a := 1)
        (R := R)
        zero_lt_one
        hR
        ξ

  rw [hInner]

  simp only [mul_one]

/-- Squared Fourier radius is homogeneous of degree two. -/
theorem h3BKMFourierRadiusSqReal_smul
    (a : ℝ)
    (ξ : H3FourierPoint3) :
    h3BKMFourierRadiusSqReal (a • ξ)
      =
    a ^ 2 * h3BKMFourierRadiusSqReal ξ := by

  unfold h3BKMFourierRadiusSqReal

  simp only [
    PiLp.smul_apply,
    smul_eq_mul
  ]

  ring

/-- The real raw Biot--Savart coordinate multiplier is homogeneous of degree
zero under every nonzero scalar dilation. -/
theorem h3BKMRawCoordinateMultiplierReal_smul
    (a : ℝ)
    (ha : a ≠ 0)
    (i k : Fin 3)
    (ξ : H3FourierPoint3) :
    h3BKMRawCoordinateMultiplierReal
        i k (a • ξ)
      =
    h3BKMRawCoordinateMultiplierReal
      i k ξ := by

  unfold h3BKMRawCoordinateMultiplierReal

  rw [
    h3BKMFourierRadiusSqReal_smul
  ]

  simp only [
    PiLp.smul_apply,
    smul_eq_mul
  ]

  by_cases hRadius :
      h3BKMFourierRadiusSqReal ξ = 0

  · rw [hRadius]

    simp

  · field_simp [ha, hRadius]

/-- Complexified raw coordinate multiplier is likewise degree zero. -/
theorem h3BKMRawCoordinateMultiplier_smul
    (a : ℝ)
    (ha : a ≠ 0)
    (i k : Fin 3)
    (ξ : H3FourierPoint3) :
    h3BKMRawCoordinateMultiplier
        i k (a • ξ)
      =
    h3BKMRawCoordinateMultiplier
      i k ξ := by

  unfold h3BKMRawCoordinateMultiplier

  rw [
    h3BKMRawCoordinateMultiplierReal_smul
      a ha i k ξ
  ]

/-- The totalized coordinate coefficient retains exact degree-zero
homogeneity. -/
theorem h3BKMCoordinateCoefficient_smul
    (a : ℝ)
    (ha : a ≠ 0)
    (i k : Fin 3)
    (ξ : H3FourierPoint3) :
    h3BKMCoordinateCoefficient
        (a • ξ) i k
      =
    h3BKMCoordinateCoefficient
      ξ i k := by

  by_cases hξ : ξ = 0

  · subst ξ

    simp [
      h3BKMCoordinateCoefficient
    ]

  · have haξ :
        a • ξ ≠ 0 :=
      smul_ne_zero ha hξ

    rw [
      h3BKMCoordinateCoefficient_eq_raw
        i k haξ,
      h3BKMCoordinateCoefficient_eq_raw
        i k hξ,
      h3BKMRawCoordinateMultiplier_smul
        a ha i k ξ
    ]

/--
Exact dyadic scaling of the localized BKM coordinate multiplier.
-/
theorem h3BKMLocalizedCoordinateMultiplier_eq_unit_inv_smul
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (ξ : H3FourierPoint3) :
    h3BKMLocalizedCoordinateMultiplier
        R hR i k ξ
      =
    h3BKMLocalizedCoordinateMultiplier
        (1 : ℝ)
        zero_lt_one
        i k
        (R⁻¹ • ξ) := by

  unfold h3BKMLocalizedCoordinateMultiplier

  rw [
    h3BKMFrequencyShell_eq_unit_inv_smul
      hR ξ,
    h3BKMCoordinateCoefficient_smul
      R⁻¹
      (inv_ne_zero hR.ne')
      i k ξ
  ]

/-- Pointwise form for the Schwartz-packaged localized multiplier. -/
theorem h3BKMLocalizedCoordinateMultiplierSchwartz_eq_unit_inv_smul
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (ξ : H3FourierPoint3) :
    h3BKMLocalizedCoordinateMultiplierSchwartz
        R hR i k ξ
      =
    h3BKMLocalizedCoordinateMultiplierSchwartz
        (1 : ℝ)
        zero_lt_one
        i k
        (R⁻¹ • ξ) := by

  rw [
    h3BKMLocalizedCoordinateMultiplierSchwartz_apply,
    h3BKMLocalizedCoordinateMultiplierSchwartz_apply
  ]

  exact
    h3BKMLocalizedCoordinateMultiplier_eq_unit_inv_smul
      hR i k ξ

end

end Euclidean
end Bridge
end PrimeTensor
