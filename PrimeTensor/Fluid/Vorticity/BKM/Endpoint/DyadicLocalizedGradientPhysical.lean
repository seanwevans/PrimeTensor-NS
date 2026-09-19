import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicLocalizedCurlPhysical
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicKernelConstant

/-!
# BKM endpoint: physical bounds for one-shell localized gradient states

The localized inverse-curl states now have physical representatives and
scale-uniform vorticity-envelope bounds.  This file assembles them with the
exact Biot--Savart sign pattern into the three one-shell velocity-gradient
states.

For one radius `R` and derivative coordinate `i`, define

    G₀ = C01⁻¹(i,1) + C02⁻¹(i,2),
    G₁ = C12⁻¹(i,2) - C01⁻¹(i,0),
    G₂ = -(C02⁻¹(i,0) + C12⁻¹(i,1)).

These are exactly the inverse-Fourier combinations corresponding to the
one-shell identities in `LocalizedGradientMultiplier`.  Each constituent
localized curl is bounded almost everywhere by the same finite coordinate
kernel constant, so every component costs only a factor of two.

This is the one-shell physical estimate needed before summing over the middle
dyadic window.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicLocalizedGradientPhysical
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointDyadicLocalizedGradientPhysical :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Generic `L²` representative algebra on the physical carrier -/

theorem ae_norm_h3FourierComplexL2_add_toLp_le_two
    (F G : H3FourierComplexL2)
    (C : ℝ)
    (hF :
      ∀ᵐ x ∂(volume : Measure Point3),
        ‖(F : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)‖ ≤ C)
    (hG :
      ∀ᵐ x ∂(volume : Measure Point3),
        ‖(G : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)‖ ≤ C) :
    ∀ᵐ x ∂(volume : Measure Point3),
      ‖((F + G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      2 * C := by

  have hAdd :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (MeasureTheory.Lp.coeFn_add F G)

  filter_upwards [hF, hG, hAdd] with x hFx hGx hAddx

  simp only [Function.comp_apply] at hAddx

  rw [hAddx]
  simp only [Pi.add_apply]

  calc
    ‖(F : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)
        +
      (G : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)‖
        ≤
      ‖(F : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)‖
        +
      ‖(G : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)‖ :=
      norm_add_le _ _

    _ ≤ C + C :=
      add_le_add hFx hGx

    _ = 2 * C := by
      ring

theorem ae_norm_h3FourierComplexL2_sub_toLp_le_two
    (F G : H3FourierComplexL2)
    (C : ℝ)
    (hF :
      ∀ᵐ x ∂(volume : Measure Point3),
        ‖(F : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)‖ ≤ C)
    (hG :
      ∀ᵐ x ∂(volume : Measure Point3),
        ‖(G : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)‖ ≤ C) :
    ∀ᵐ x ∂(volume : Measure Point3),
      ‖((F - G : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      2 * C := by

  have hSub :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (MeasureTheory.Lp.coeFn_sub F G)

  filter_upwards [hF, hG, hSub] with x hFx hGx hSubx

  simp only [Function.comp_apply] at hSubx

  rw [hSubx]
  simp only [Pi.sub_apply]

  calc
    ‖(F : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)
        -
      (G : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)‖
        ≤
      ‖(F : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)‖
        +
      ‖(G : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)‖ :=
      norm_sub_le _ _

    _ ≤ C + C :=
      add_le_add hFx hGx

    _ = 2 * C := by
      ring

theorem ae_norm_h3FourierComplexL2_neg_toLp_le
    (F : H3FourierComplexL2)
    (C : ℝ)
    (hF :
      ∀ᵐ x ∂(volume : Measure Point3),
        ‖(F : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)‖ ≤ C) :
    ∀ᵐ x ∂(volume : Measure Point3),
      ‖((-F : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      C := by

  have hNeg :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (MeasureTheory.Lp.coeFn_neg F)

  filter_upwards [hF, hNeg] with x hFx hNegx

  simp only [Function.comp_apply] at hNegx

  rw [hNegx]
  simp only [Pi.neg_apply, norm_neg]

  exact hFx

/-! ## Upgrade the three localized curls to the universal kernel constant -/

theorem ae_norm_h3BKMLocalizedCanonicalCurl01InverseL2_toLp_le_constant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Point3),
      ‖(h3BKMLocalizedCanonicalCurl01InverseL2
          hFourier R hR i k :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      g t * h3BKMDyadicKernelUnitMassConstant := by

  have h :=
    ae_norm_h3BKMLocalizedCanonicalCurl01InverseL2_toLp_le_unit
      hInt hMeas hFourier hEnvelope hR i k

  filter_upwards [h] with x hx

  exact
    hx.trans
      (mul_le_mul_of_nonneg_left
        (h3BKMDyadicKernelL1Mass_unit_le_constant i k)
        (h3BKM_vorticityEnvelope_nonneg hEnvelope))

theorem ae_norm_h3BKMLocalizedCanonicalCurl02InverseL2_toLp_le_constant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Point3),
      ‖(h3BKMLocalizedCanonicalCurl02InverseL2
          hFourier R hR i k :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      g t * h3BKMDyadicKernelUnitMassConstant := by

  have h :=
    ae_norm_h3BKMLocalizedCanonicalCurl02InverseL2_toLp_le_unit
      hInt hMeas hFourier hEnvelope hR i k

  filter_upwards [h] with x hx

  exact
    hx.trans
      (mul_le_mul_of_nonneg_left
        (h3BKMDyadicKernelL1Mass_unit_le_constant i k)
        (h3BKM_vorticityEnvelope_nonneg hEnvelope))

theorem ae_norm_h3BKMLocalizedCanonicalCurl12InverseL2_toLp_le_constant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Point3),
      ‖(h3BKMLocalizedCanonicalCurl12InverseL2
          hFourier R hR i k :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      g t * h3BKMDyadicKernelUnitMassConstant := by

  have h :=
    ae_norm_h3BKMLocalizedCanonicalCurl12InverseL2_toLp_le_unit
      hInt hMeas hFourier hEnvelope hR i k

  filter_upwards [h] with x hx

  exact
    hx.trans
      (mul_le_mul_of_nonneg_left
        (h3BKMDyadicKernelL1Mass_unit_le_constant i k)
        (h3BKM_vorticityEnvelope_nonneg hEnvelope))

/-! ## Exact one-shell inverse-gradient `L²` states -/

noncomputable def h3BKMDyadicLocalizedGradientComponent0InverseL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (R : ℝ)
    (hR : 0 < R)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  h3BKMLocalizedCanonicalCurl01InverseL2
      hFourier R hR i 1
    +
  h3BKMLocalizedCanonicalCurl02InverseL2
      hFourier R hR i 2

noncomputable def h3BKMDyadicLocalizedGradientComponent1InverseL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (R : ℝ)
    (hR : 0 < R)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  h3BKMLocalizedCanonicalCurl12InverseL2
      hFourier R hR i 2
    -
  h3BKMLocalizedCanonicalCurl01InverseL2
      hFourier R hR i 0

noncomputable def h3BKMDyadicLocalizedGradientComponent2InverseL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (R : ℝ)
    (hR : 0 < R)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  -
    (
      h3BKMLocalizedCanonicalCurl02InverseL2
          hFourier R hR i 0
        +
      h3BKMLocalizedCanonicalCurl12InverseL2
          hFourier R hR i 1
    )

/-! ## One-shell physical bounds -/

theorem ae_norm_h3BKMDyadicLocalizedGradientComponent0InverseL2_toLp_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    {R : ℝ}
    (hR : 0 < R)
    (i : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Point3),
      ‖(h3BKMDyadicLocalizedGradientComponent0InverseL2
          hFourier R hR i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      2 * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  unfold h3BKMDyadicLocalizedGradientComponent0InverseL2

  exact
    ae_norm_h3FourierComplexL2_add_toLp_le_two
      (h3BKMLocalizedCanonicalCurl01InverseL2
        hFourier R hR i 1)
      (h3BKMLocalizedCanonicalCurl02InverseL2
        hFourier R hR i 2)
      (g t * h3BKMDyadicKernelUnitMassConstant)
      (ae_norm_h3BKMLocalizedCanonicalCurl01InverseL2_toLp_le_constant
        hInt hMeas hFourier hEnvelope hR i 1)
      (ae_norm_h3BKMLocalizedCanonicalCurl02InverseL2_toLp_le_constant
        hInt hMeas hFourier hEnvelope hR i 2)

theorem ae_norm_h3BKMDyadicLocalizedGradientComponent1InverseL2_toLp_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    {R : ℝ}
    (hR : 0 < R)
    (i : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Point3),
      ‖(h3BKMDyadicLocalizedGradientComponent1InverseL2
          hFourier R hR i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      2 * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  unfold h3BKMDyadicLocalizedGradientComponent1InverseL2

  exact
    ae_norm_h3FourierComplexL2_sub_toLp_le_two
      (h3BKMLocalizedCanonicalCurl12InverseL2
        hFourier R hR i 2)
      (h3BKMLocalizedCanonicalCurl01InverseL2
        hFourier R hR i 0)
      (g t * h3BKMDyadicKernelUnitMassConstant)
      (ae_norm_h3BKMLocalizedCanonicalCurl12InverseL2_toLp_le_constant
        hInt hMeas hFourier hEnvelope hR i 2)
      (ae_norm_h3BKMLocalizedCanonicalCurl01InverseL2_toLp_le_constant
        hInt hMeas hFourier hEnvelope hR i 0)

theorem ae_norm_h3BKMDyadicLocalizedGradientComponent2InverseL2_toLp_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hInt : VelocityH3IntegrableAt u t)
    (hMeas : VelocityH3MeasurableAt u t)
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (hEnvelope : VorticityEnvelope u g t)
    {R : ℝ}
    (hR : 0 < R)
    (i : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Point3),
      ‖(h3BKMDyadicLocalizedGradientComponent2InverseL2
          hFourier R hR i :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        ≤
      2 * (g t * h3BKMDyadicKernelUnitMassConstant) := by

  unfold h3BKMDyadicLocalizedGradientComponent2InverseL2

  apply
    ae_norm_h3FourierComplexL2_neg_toLp_le
      (
        h3BKMLocalizedCanonicalCurl02InverseL2
            hFourier R hR i 0
          +
        h3BKMLocalizedCanonicalCurl12InverseL2
            hFourier R hR i 1
      )
      (2 * (g t * h3BKMDyadicKernelUnitMassConstant))

  exact
    ae_norm_h3FourierComplexL2_add_toLp_le_two
      (h3BKMLocalizedCanonicalCurl02InverseL2
        hFourier R hR i 0)
      (h3BKMLocalizedCanonicalCurl12InverseL2
        hFourier R hR i 1)
      (g t * h3BKMDyadicKernelUnitMassConstant)
      (ae_norm_h3BKMLocalizedCanonicalCurl02InverseL2_toLp_le_constant
        hInt hMeas hFourier hEnvelope hR i 0)
      (ae_norm_h3BKMLocalizedCanonicalCurl12InverseL2_toLp_le_constant
        hInt hMeas hFourier hEnvelope hR i 1)

end

end Euclidean
end Bridge
end PrimeTensor
