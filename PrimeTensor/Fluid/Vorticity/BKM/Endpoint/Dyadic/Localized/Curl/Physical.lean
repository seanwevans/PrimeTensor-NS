import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Vorticity.Convolution.Physical
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Vorticity.Convolution.Reconstruction
import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Kernel.Bound

/-!
# BKM endpoint: physical representatives of localized inverse-curl states

The two preceding bridges now meet exactly.

`DyadicVorticityConvolutionReconstruction` proves the bundled identities

    K * ωₓ = - F⁻¹(M C12),
    K * ωᵧ =   F⁻¹(M C02),
    K * ω_z = - F⁻¹(M C01),

while `DyadicVorticityConvolutionPhysical` identifies the same bundled
convolution states, after pullback by `WithLp.toLp`, with the literal physical
convolutions already controlled by the BKM `L∞` estimates.

Combining them gives physical representatives for the localized inverse-curl
states with the exact vorticity signs.  We then transfer the scale-uniform
dyadic convolution bounds to the unsigned inverse-curl representatives.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicLocalizedCurlPhysical
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointDyadicLocalizedCurlPhysical :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Signed physical representatives -/

/--
Minus the localized `C12` inverse state is represented physically by the
x-vorticity dyadic convolution.
-/
theorem h3BKMLocalizedCanonicalCurl12InverseL2_neg_toLp_ae_eq_physicalX
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
    (fun x : Point3 =>
      ((-
          h3BKMLocalizedCanonicalCurl12InverseL2
            hFourier R hR i k :
          H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i k)
        (h3BKMPhysicalVorticityX u t)
        x) := by

  have h :=
    h3BKMDyadicVorticityXConvolutionL2_toLp_ae_eq_physical
      hInt hMeas hEnvelope hR i k

  rw [
    h3BKMDyadicVorticityXConvolutionL2_eq_neg_localizedCurl12InverseL2
      hFourier hR i k
  ] at h

  exact h

/--
The localized `C02` inverse state is represented physically by the
y-vorticity dyadic convolution.
-/
theorem h3BKMLocalizedCanonicalCurl02InverseL2_toLp_ae_eq_physicalY
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
    (fun x : Point3 =>
      (h3BKMLocalizedCanonicalCurl02InverseL2
          hFourier R hR i k :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i k)
        (h3BKMPhysicalVorticityY u t)
        x) := by

  have h :=
    h3BKMDyadicVorticityYConvolutionL2_toLp_ae_eq_physical
      hInt hMeas hEnvelope hR i k

  rw [
    h3BKMDyadicVorticityYConvolutionL2_eq_localizedCurl02InverseL2
      hFourier hR i k
  ] at h

  exact h

/--
Minus the localized `C01` inverse state is represented physically by the
z-vorticity dyadic convolution.
-/
theorem h3BKMLocalizedCanonicalCurl01InverseL2_neg_toLp_ae_eq_physicalZ
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
    (fun x : Point3 =>
      ((-
          h3BKMLocalizedCanonicalCurl01InverseL2
            hFourier R hR i k :
          H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    (fun x : Point3 =>
      h3BKMPhysicalConvolution
        (h3BKMDyadicPhysicalKernel R hR i k)
        (h3BKMPhysicalVorticityZ u t)
        x) := by

  have h :=
    h3BKMDyadicVorticityZConvolutionL2_toLp_ae_eq_physical
      hInt hMeas hEnvelope hR i k

  rw [
    h3BKMDyadicVorticityZConvolutionL2_eq_neg_localizedCurl01InverseL2
      hFourier hR i k
  ] at h

  exact h

/-! ## Scale-uniform a.e. bounds for the inverse-curl states -/

/--
The localized `C12` inverse state inherits the scale-uniform x-vorticity
convolution bound.
-/
theorem ae_norm_h3BKMLocalizedCanonicalCurl12InverseL2_toLp_le_unit
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
      g t *
        h3BKMDyadicKernelL1Mass
          (1 : ℝ) zero_lt_one i k := by

  let F : H3FourierComplexL2 :=
    h3BKMLocalizedCanonicalCurl12InverseL2
      hFourier R hR i k

  have hPhysical :=
    h3BKMLocalizedCanonicalCurl12InverseL2_neg_toLp_ae_eq_physicalX
      hInt hMeas hFourier hEnvelope hR i k

  have hNeg :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (MeasureTheory.Lp.coeFn_neg F)

  filter_upwards [hPhysical, hNeg] with x hPhysicalx hNegx

  simp only [Function.comp_apply] at hNegx

  calc
    ‖(F : H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        =
      ‖-
        (F : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)‖ := by
          rw [norm_neg]

    _ =
      ‖((-F : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖ := by
          exact (congrArg norm hNegx).symm

    _ =
      ‖h3BKMPhysicalConvolution
          (h3BKMDyadicPhysicalKernel R hR i k)
          (h3BKMPhysicalVorticityX u t)
          x‖ := by
          exact congrArg norm hPhysicalx

    _ ≤
      g t *
        h3BKMDyadicKernelL1Mass
          (1 : ℝ) zero_lt_one i k := by
          exact
            norm_h3BKMPhysicalConvolution_dyadic_vorticityX_le_unit
              hR hEnvelope i k x

/--
The localized `C02` inverse state inherits the scale-uniform y-vorticity
convolution bound.
-/
theorem ae_norm_h3BKMLocalizedCanonicalCurl02InverseL2_toLp_le_unit
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
      g t *
        h3BKMDyadicKernelL1Mass
          (1 : ℝ) zero_lt_one i k := by

  have hPhysical :=
    h3BKMLocalizedCanonicalCurl02InverseL2_toLp_ae_eq_physicalY
      hInt hMeas hFourier hEnvelope hR i k

  filter_upwards [hPhysical] with x hPhysicalx

  calc
    ‖(h3BKMLocalizedCanonicalCurl02InverseL2
          hFourier R hR i k :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        =
      ‖h3BKMPhysicalConvolution
          (h3BKMDyadicPhysicalKernel R hR i k)
          (h3BKMPhysicalVorticityY u t)
          x‖ := by
          exact congrArg norm hPhysicalx

    _ ≤
      g t *
        h3BKMDyadicKernelL1Mass
          (1 : ℝ) zero_lt_one i k := by
          exact
            norm_h3BKMPhysicalConvolution_dyadic_vorticityY_le_unit
              hR hEnvelope i k x

/--
The localized `C01` inverse state inherits the scale-uniform z-vorticity
convolution bound.
-/
theorem ae_norm_h3BKMLocalizedCanonicalCurl01InverseL2_toLp_le_unit
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
      g t *
        h3BKMDyadicKernelL1Mass
          (1 : ℝ) zero_lt_one i k := by

  let F : H3FourierComplexL2 :=
    h3BKMLocalizedCanonicalCurl01InverseL2
      hFourier R hR i k

  have hPhysical :=
    h3BKMLocalizedCanonicalCurl01InverseL2_neg_toLp_ae_eq_physicalZ
      hInt hMeas hFourier hEnvelope hR i k

  have hNeg :=
    (
      PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)
    ).quasiMeasurePreserving.ae_eq_comp
      (MeasureTheory.Lp.coeFn_neg F)

  filter_upwards [hPhysical, hNeg] with x hPhysicalx hNegx

  simp only [Function.comp_apply] at hNegx

  calc
    ‖(F : H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖
        =
      ‖-
        (F : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x)‖ := by
          rw [norm_neg]

    _ =
      ‖((-F : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)‖ := by
          exact (congrArg norm hNegx).symm

    _ =
      ‖h3BKMPhysicalConvolution
          (h3BKMDyadicPhysicalKernel R hR i k)
          (h3BKMPhysicalVorticityZ u t)
          x‖ := by
          exact congrArg norm hPhysicalx

    _ ≤
      g t *
        h3BKMDyadicKernelL1Mass
          (1 : ℝ) zero_lt_one i k := by
          exact
            norm_h3BKMPhysicalConvolution_dyadic_vorticityZ_le_unit
              hR hEnvelope i k x

end

end Euclidean
end Bridge
end PrimeTensor
