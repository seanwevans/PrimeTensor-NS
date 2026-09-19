import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.HighFrequencyGradientCutoffSelection
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.MiddleLocalizedGradientPhysical

/-!
# BKM endpoint: selected middle-gradient logarithmic bound

The upper dyadic cutoff has now been selected canonically from a scalar H³
size `A`.  The generic middle localized-gradient estimate is

    ‖middle_j,[0,hi](x)‖
      ≤ 2 * width(0,hi) * (g(t) * C_BKM)

almost everywhere.

At the selected upper index

    hi = h3BKMUpperCutoffIndex A,

the cutoff-selection theorem gives

    width(0,hi)
      ≤ 4 * log₂(max 1 A) + 2.

This file substitutes that bound into all three physical middle-gradient
components.  The next checkpoint therefore no longer needs any shell-count or
ceiling arithmetic: it can focus purely on identifying the selected middle
physical state with the middle term in the actual derivative trichotomy.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointSelectedMiddleGradientLogBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

private theorem selected_middle_log_scale_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t) :
    0 ≤ 2 * (g t * h3BKMDyadicKernelUnitMassConstant) := by
  exact
    mul_nonneg
      (by norm_num)
      (mul_nonneg
        (h3BKM_vorticityEnvelope_nonneg hEnvelope)
        h3BKMDyadicKernelUnitMassConstant_nonneg)

/-- Selected logarithmic middle bound for target velocity component `0`. -/
theorem ae_norm_h3BKMMiddleLocalizedGradientComponent0InverseL2_selected_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (i : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Point3),
      ‖(h3BKMMiddleLocalizedGradientComponent0InverseL2
          hFourier
          0
          (h3BKMUpperCutoffIndex A)
          i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      2
        * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  have hBase :=
    ae_norm_h3BKMMiddleLocalizedGradientComponent0InverseL2_toLp_le
      hInt hMeas hFourier hEnvelope
      (Nat.zero_le (h3BKMUpperCutoffIndex A))
      i

  have hWidth :=
    h3BKMMiddleDyadicLogWidth_zero_selected_le A

  have hScale :
      0 ≤ 2 * (g t * h3BKMDyadicKernelUnitMassConstant) :=
    selected_middle_log_scale_nonneg hEnvelope

  filter_upwards [hBase] with x hx

  calc
    ‖(h3BKMMiddleLocalizedGradientComponent0InverseL2
          hFourier
          0
          (h3BKMUpperCutoffIndex A)
          i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      2
        * h3BKMMiddleDyadicLogWidth
            0
            (h3BKMUpperCutoffIndex A)
        * (g t * h3BKMDyadicKernelUnitMassConstant) :=
      hx

    _ =
      h3BKMMiddleDyadicLogWidth
          0
          (h3BKMUpperCutoffIndex A)
        * (2 * (g t * h3BKMDyadicKernelUnitMassConstant)) := by
      ring

    _ ≤
      (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (2 * (g t * h3BKMDyadicKernelUnitMassConstant)) :=
      mul_le_mul_of_nonneg_right
        hWidth
        hScale

    _ =
      2
        * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
      ring

/-- Selected logarithmic middle bound for target velocity component `1`. -/
theorem ae_norm_h3BKMMiddleLocalizedGradientComponent1InverseL2_selected_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (i : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Point3),
      ‖(h3BKMMiddleLocalizedGradientComponent1InverseL2
          hFourier
          0
          (h3BKMUpperCutoffIndex A)
          i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      2
        * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  have hBase :=
    ae_norm_h3BKMMiddleLocalizedGradientComponent1InverseL2_toLp_le
      hInt hMeas hFourier hEnvelope
      (Nat.zero_le (h3BKMUpperCutoffIndex A))
      i

  have hWidth :=
    h3BKMMiddleDyadicLogWidth_zero_selected_le A

  have hScale :
      0 ≤ 2 * (g t * h3BKMDyadicKernelUnitMassConstant) :=
    selected_middle_log_scale_nonneg hEnvelope

  filter_upwards [hBase] with x hx

  calc
    ‖(h3BKMMiddleLocalizedGradientComponent1InverseL2
          hFourier
          0
          (h3BKMUpperCutoffIndex A)
          i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      2
        * h3BKMMiddleDyadicLogWidth
            0
            (h3BKMUpperCutoffIndex A)
        * (g t * h3BKMDyadicKernelUnitMassConstant) :=
      hx

    _ =
      h3BKMMiddleDyadicLogWidth
          0
          (h3BKMUpperCutoffIndex A)
        * (2 * (g t * h3BKMDyadicKernelUnitMassConstant)) := by
      ring

    _ ≤
      (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (2 * (g t * h3BKMDyadicKernelUnitMassConstant)) :=
      mul_le_mul_of_nonneg_right
        hWidth
        hScale

    _ =
      2
        * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
      ring

/-- Selected logarithmic middle bound for target velocity component `2`. -/
theorem ae_norm_h3BKMMiddleLocalizedGradientComponent2InverseL2_selected_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (i : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Point3),
      ‖(h3BKMMiddleLocalizedGradientComponent2InverseL2
          hFourier
          0
          (h3BKMUpperCutoffIndex A)
          i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      2
        * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  have hBase :=
    ae_norm_h3BKMMiddleLocalizedGradientComponent2InverseL2_toLp_le
      hInt hMeas hFourier hEnvelope
      (Nat.zero_le (h3BKMUpperCutoffIndex A))
      i

  have hWidth :=
    h3BKMMiddleDyadicLogWidth_zero_selected_le A

  have hScale :
      0 ≤ 2 * (g t * h3BKMDyadicKernelUnitMassConstant) :=
    selected_middle_log_scale_nonneg hEnvelope

  filter_upwards [hBase] with x hx

  calc
    ‖(h3BKMMiddleLocalizedGradientComponent2InverseL2
          hFourier
          0
          (h3BKMUpperCutoffIndex A)
          i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      2
        * h3BKMMiddleDyadicLogWidth
            0
            (h3BKMUpperCutoffIndex A)
        * (g t * h3BKMDyadicKernelUnitMassConstant) :=
      hx

    _ =
      h3BKMMiddleDyadicLogWidth
          0
          (h3BKMUpperCutoffIndex A)
        * (2 * (g t * h3BKMDyadicKernelUnitMassConstant)) := by
      ring

    _ ≤
      (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (2 * (g t * h3BKMDyadicKernelUnitMassConstant)) :=
      mul_le_mul_of_nonneg_right
        hWidth
        hScale

    _ =
      2
        * (4 * Real.logb 2 (h3BKMUpperCutoffScale A) + 2)
        * (g t * h3BKMDyadicKernelUnitMassConstant) := by
      ring

end

end Euclidean
end Bridge
end PrimeTensor
