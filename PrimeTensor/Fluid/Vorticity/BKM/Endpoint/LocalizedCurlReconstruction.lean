import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.CanonicalCurlIntegrable
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Reconstruction.Compatibility

/-!
# BKM endpoint: localized canonical curls admit compatible L² reconstructions

The previous endpoint layer proved that each canonical pairwise curl amplitude
belongs to ordinary Fourier `L¹`, and that multiplication by every localized
BKM coordinate multiplier preserves that `L¹` property.

For the physical convolution bridge we also need the corresponding Plancherel
object.  The physical-vorticity identification already shows that every
canonical curl amplitude is, up to the known sign convention, the Fourier
transform of a genuine physical `L²` vorticity package.  Hence every canonical
curl is also in Fourier `L²`.

The localized multiplier has pointwise norm at most one, so localization
preserves this `L²` membership.  We package each localized curl product as an
`H3FourierComplexL2` state and apply the generic `L¹ ∩ L²` inverse-Fourier
compatibility theorem already available in the classicalization stack.

Thus, for every dyadic scale and coordinate multiplier,

    ordinary F⁻¹(Mᵢₖ,R C_ab)

agrees almost everywhere with the unitary `L²` inverse Fourier transform of the
same localized curl state.

This is the final spectral-side reconstruction checkpoint before identifying
that inverse transform with convolution against the physical dyadic kernel.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointLocalizedCurlReconstruction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical `C01` amplitude is also a Fourier `L²` function. -/
theorem h3BKMCanonicalCurl01Amplitude_memLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    MemLp
      (h3BKMCanonicalCurl01Amplitude hInt hMeas)
      2
      (volume : Measure H3FourierPoint3) := by

  let F : H3FourierComplexL2 :=
    h3ScalarFourierL2
      (h3BKMPhysicalVorticityZL2
        u t hInt hMeas)

  have hF :
      MemLp
        ((F : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        2
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.Lp.memLp F

  have hCurlMeas :
      AEStronglyMeasurable
        (h3BKMCanonicalCurl01Amplitude hInt hMeas)
        (volume : Measure H3FourierPoint3) :=
    (h3BKMCanonicalCurl01Amplitude_integrable
      hFourier).aestronglyMeasurable

  have hAE :
      ((F : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      fun ξ : H3FourierPoint3 =>
        - h3BKMCanonicalCurl01Amplitude
            hInt hMeas ξ := by
    dsimp only [F]
    exact
      h3BKMPhysicalVorticityZL2_fourier_ae_eq_neg_curl01
        hFourier

  refine hF.of_le hCurlMeas ?_

  filter_upwards [hAE] with ξ hξ

  have hNorm :
      ‖h3BKMCanonicalCurl01Amplitude hInt hMeas ξ‖
        =
      ‖((F : H3FourierComplexL2) : H3FourierPoint3 → ℂ) ξ‖ := by
    simpa using
      (congrArg norm hξ).symm

  exact hNorm.le

/-- The canonical `C02` amplitude is also a Fourier `L²` function. -/
theorem h3BKMCanonicalCurl02Amplitude_memLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    MemLp
      (h3BKMCanonicalCurl02Amplitude hInt hMeas)
      2
      (volume : Measure H3FourierPoint3) := by

  let F : H3FourierComplexL2 :=
    h3ScalarFourierL2
      (h3BKMPhysicalVorticityYL2
        u t hInt hMeas)

  have hF :
      MemLp
        ((F : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        2
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.Lp.memLp F

  have hCurlMeas :
      AEStronglyMeasurable
        (h3BKMCanonicalCurl02Amplitude hInt hMeas)
        (volume : Measure H3FourierPoint3) :=
    (h3BKMCanonicalCurl02Amplitude_integrable
      hFourier).aestronglyMeasurable

  have hAE :
      ((F : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3BKMCanonicalCurl02Amplitude
        hInt hMeas := by
    dsimp only [F]
    exact
      h3BKMPhysicalVorticityYL2_fourier_ae_eq_curl02
        hFourier

  refine hF.of_le hCurlMeas ?_

  filter_upwards [hAE] with ξ hξ

  have hNorm :
      ‖h3BKMCanonicalCurl02Amplitude hInt hMeas ξ‖
        =
      ‖((F : H3FourierComplexL2) : H3FourierPoint3 → ℂ) ξ‖ := by
    simpa using
      (congrArg norm hξ).symm

  exact hNorm.le

/-- The canonical `C12` amplitude is also a Fourier `L²` function. -/
theorem h3BKMCanonicalCurl12Amplitude_memLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    MemLp
      (h3BKMCanonicalCurl12Amplitude hInt hMeas)
      2
      (volume : Measure H3FourierPoint3) := by

  let F : H3FourierComplexL2 :=
    h3ScalarFourierL2
      (h3BKMPhysicalVorticityXL2
        u t hInt hMeas)

  have hF :
      MemLp
        ((F : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        2
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.Lp.memLp F

  have hCurlMeas :
      AEStronglyMeasurable
        (h3BKMCanonicalCurl12Amplitude hInt hMeas)
        (volume : Measure H3FourierPoint3) :=
    (h3BKMCanonicalCurl12Amplitude_integrable
      hFourier).aestronglyMeasurable

  have hAE :
      ((F : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      fun ξ : H3FourierPoint3 =>
        - h3BKMCanonicalCurl12Amplitude
            hInt hMeas ξ := by
    dsimp only [F]
    exact
      h3BKMPhysicalVorticityXL2_fourier_ae_eq_neg_curl12
        hFourier

  refine hF.of_le hCurlMeas ?_

  filter_upwards [hAE] with ξ hξ

  have hNorm :
      ‖h3BKMCanonicalCurl12Amplitude hInt hMeas ξ‖
        =
      ‖((F : H3FourierComplexL2) : H3FourierPoint3 → ℂ) ξ‖ := by
    simpa using
      (congrArg norm hξ).symm

  exact hNorm.le

/--
A localized BKM coordinate multiplier preserves Fourier `L²` membership.
-/
theorem h3BKMLocalizedCoordinateMultiplier_mul_memLp2
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    {f : H3FourierPoint3 → ℂ}
    (hf :
      MemLp
        f
        2
        (volume : Measure H3FourierPoint3)) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3BKMLocalizedCoordinateMultiplier
            R hR i k ξ
          *
        f ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3BKMLocalizedCoordinateMultiplier
              R hR i k ξ
            *
          f ξ)
        (volume : Measure H3FourierPoint3) := by
    exact
      (h3BKMLocalizedCoordinateMultiplier_contDiff
        hR i k).continuous.aestronglyMeasurable.mul
          hf.aestronglyMeasurable

  refine hf.of_le hMeas ?_

  filter_upwards with ξ

  rw [norm_mul]

  calc
    ‖h3BKMLocalizedCoordinateMultiplier
        R hR i k ξ‖ * ‖f ξ‖
        ≤
      1 * ‖f ξ‖ := by
        exact
          mul_le_mul_of_nonneg_right
            (norm_h3BKMLocalizedCoordinateMultiplier_le_one
              hR i k ξ)
            (norm_nonneg _)

    _ = ‖f ξ‖ := by
      rw [one_mul]

/-- Localized `C01` multiplier products belong to Fourier `L²`. -/
theorem h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl01_memLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3BKMLocalizedCoordinateMultiplier
            R hR i k ξ
          *
        h3BKMCanonicalCurl01Amplitude
          hInt hMeas ξ)
      2
      (volume : Measure H3FourierPoint3) :=
  h3BKMLocalizedCoordinateMultiplier_mul_memLp2
    hR i k
    (h3BKMCanonicalCurl01Amplitude_memLp2 hFourier)

/-- Localized `C02` multiplier products belong to Fourier `L²`. -/
theorem h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl02_memLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3BKMLocalizedCoordinateMultiplier
            R hR i k ξ
          *
        h3BKMCanonicalCurl02Amplitude
          hInt hMeas ξ)
      2
      (volume : Measure H3FourierPoint3) :=
  h3BKMLocalizedCoordinateMultiplier_mul_memLp2
    hR i k
    (h3BKMCanonicalCurl02Amplitude_memLp2 hFourier)

/-- Localized `C12` multiplier products belong to Fourier `L²`. -/
theorem h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl12_memLp2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3BKMLocalizedCoordinateMultiplier
            R hR i k ξ
          *
        h3BKMCanonicalCurl12Amplitude
          hInt hMeas ξ)
      2
      (volume : Measure H3FourierPoint3) :=
  h3BKMLocalizedCoordinateMultiplier_mul_memLp2
    hR i k
    (h3BKMCanonicalCurl12Amplitude_memLp2 hFourier)

/-- `L²` package of one localized `C01` multiplier product. -/
noncomputable def h3BKMLocalizedCanonicalCurl01L2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3) :
    H3FourierComplexL2 :=
  (h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl01_memLp2
    hFourier hR i k).toLp
      (fun ξ : H3FourierPoint3 =>
        h3BKMLocalizedCoordinateMultiplier
            R hR i k ξ
          *
        h3BKMCanonicalCurl01Amplitude hInt hMeas ξ)

/-- `L²` package of one localized `C02` multiplier product. -/
noncomputable def h3BKMLocalizedCanonicalCurl02L2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3) :
    H3FourierComplexL2 :=
  (h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl02_memLp2
    hFourier hR i k).toLp
      (fun ξ : H3FourierPoint3 =>
        h3BKMLocalizedCoordinateMultiplier
            R hR i k ξ
          *
        h3BKMCanonicalCurl02Amplitude hInt hMeas ξ)

/-- `L²` package of one localized `C12` multiplier product. -/
noncomputable def h3BKMLocalizedCanonicalCurl12L2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3) :
    H3FourierComplexL2 :=
  (h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl12_memLp2
    hFourier hR i k).toLp
      (fun ξ : H3FourierPoint3 =>
        h3BKMLocalizedCoordinateMultiplier
            R hR i k ξ
          *
        h3BKMCanonicalCurl12Amplitude hInt hMeas ξ)

/-- Canonical unitary `L²` inverse transform of localized `C01`. -/
noncomputable def h3BKMLocalizedCanonicalCurl01InverseL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3) :
    H3FourierComplexL2 :=
  (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).symm
    (h3BKMLocalizedCanonicalCurl01L2
      hFourier R hR i k)

/-- Canonical unitary `L²` inverse transform of localized `C02`. -/
noncomputable def h3BKMLocalizedCanonicalCurl02InverseL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3) :
    H3FourierComplexL2 :=
  (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).symm
    (h3BKMLocalizedCanonicalCurl02L2
      hFourier R hR i k)

/-- Canonical unitary `L²` inverse transform of localized `C12`. -/
noncomputable def h3BKMLocalizedCanonicalCurl12InverseL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3) :
    H3FourierComplexL2 :=
  (MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ).symm
    (h3BKMLocalizedCanonicalCurl12L2
      hFourier R hR i k)

/--
Ordinary inverse Fourier reconstruction of localized `C01` agrees a.e. with
its unitary `L²` inverse transform.
-/
theorem h3BKMLocalizedCanonicalCurl01_fourierInv_ae_eq_L2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3BKMLocalizedCoordinateMultiplier
              R hR i k ξ
            *
          h3BKMCanonicalCurl01Amplitude
            hInt hMeas ξ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    ((h3BKMLocalizedCanonicalCurl01InverseL2
        hFourier R hR i k :
        H3FourierComplexL2) :
      H3FourierPoint3 → ℂ) := by

  unfold
    h3BKMLocalizedCanonicalCurl01InverseL2
    h3BKMLocalizedCanonicalCurl01L2

  exact
    h3FourierInv_integrable_memLp2_ae_eq_L2
      (h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl01_integrable
        hFourier hR i k)
      (h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl01_memLp2
        hFourier hR i k)

/--
Ordinary inverse Fourier reconstruction of localized `C02` agrees a.e. with
its unitary `L²` inverse transform.
-/
theorem h3BKMLocalizedCanonicalCurl02_fourierInv_ae_eq_L2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3BKMLocalizedCoordinateMultiplier
              R hR i k ξ
            *
          h3BKMCanonicalCurl02Amplitude
            hInt hMeas ξ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    ((h3BKMLocalizedCanonicalCurl02InverseL2
        hFourier R hR i k :
        H3FourierComplexL2) :
      H3FourierPoint3 → ℂ) := by

  unfold
    h3BKMLocalizedCanonicalCurl02InverseL2
    h3BKMLocalizedCanonicalCurl02L2

  exact
    h3FourierInv_integrable_memLp2_ae_eq_L2
      (h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl02_integrable
        hFourier hR i k)
      (h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl02_memLp2
        hFourier hR i k)

/--
Ordinary inverse Fourier reconstruction of localized `C12` agrees a.e. with
its unitary `L²` inverse transform.
-/
theorem h3BKMLocalizedCanonicalCurl12_fourierInv_ae_eq_L2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3BKMLocalizedCoordinateMultiplier
              R hR i k ξ
            *
          h3BKMCanonicalCurl12Amplitude
            hInt hMeas ξ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    ((h3BKMLocalizedCanonicalCurl12InverseL2
        hFourier R hR i k :
        H3FourierComplexL2) :
      H3FourierPoint3 → ℂ) := by

  unfold
    h3BKMLocalizedCanonicalCurl12InverseL2
    h3BKMLocalizedCanonicalCurl12L2

  exact
    h3FourierInv_integrable_memLp2_ae_eq_L2
      (h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl12_integrable
        hFourier hR i k)
      (h3BKMLocalizedCoordinateMultiplier_mul_canonicalCurl12_memLp2
        hFourier hR i k)

end

end Euclidean
end Bridge
end PrimeTensor
