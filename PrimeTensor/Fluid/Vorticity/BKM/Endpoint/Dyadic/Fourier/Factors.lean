import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Vorticity.Physical.Convolution.L2

/-!
# BKM endpoint: exact Fourier identities for the dyadic convolution factors

The previous checkpoint placed the physical dyadic convolution in the endpoint
Young space `L¹ * L² → L²`.  Before proving the convolution theorem itself,
identify the two factors on the Fourier side without any remaining carrier or
sign ambiguity.

This file packages:

* the three canonical curl amplitudes as genuine Fourier `L²` states;
* one dyadic inverse-Fourier kernel as a genuine Fourier-carrier `L²` state;
* the localized coordinate multiplier as a genuine Fourier-carrier `L²` state.

It then proves the exact identities

    𝓕 Kᵢₖ,R = Mᵢₖ,R

and, for the physical vorticity components,

    𝓕 ωₓ = -C12,
    𝓕 ωᵧ =  C02,
    𝓕 ω_z = -C01

as equalities of bundled `L²` states, not merely representative-level a.e.
statements.

These equalities are the factor inputs for the next `L¹ * L²` Fourier
convolution bridge.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicFourierFactors
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Canonical curl amplitudes as L² states -/

/-- Bundled `L²` state of the canonical `C01` amplitude. -/
noncomputable def h3BKMCanonicalCurl01L2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    H3FourierComplexL2 :=
  (h3BKMCanonicalCurl01Amplitude_memLp2 hFourier).toLp
    (h3BKMCanonicalCurl01Amplitude hInt hMeas)

/-- Bundled `L²` state of the canonical `C02` amplitude. -/
noncomputable def h3BKMCanonicalCurl02L2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    H3FourierComplexL2 :=
  (h3BKMCanonicalCurl02Amplitude_memLp2 hFourier).toLp
    (h3BKMCanonicalCurl02Amplitude hInt hMeas)

/-- Bundled `L²` state of the canonical `C12` amplitude. -/
noncomputable def h3BKMCanonicalCurl12L2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    H3FourierComplexL2 :=
  (h3BKMCanonicalCurl12Amplitude_memLp2 hFourier).toLp
    (h3BKMCanonicalCurl12Amplitude hInt hMeas)

theorem h3BKMCanonicalCurl01L2_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    (h3BKMCanonicalCurl01L2 hFourier :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3BKMCanonicalCurl01Amplitude hInt hMeas := by

  unfold h3BKMCanonicalCurl01L2

  exact
    MeasureTheory.MemLp.coeFn_toLp
      (h3BKMCanonicalCurl01Amplitude_memLp2 hFourier)

theorem h3BKMCanonicalCurl02L2_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    (h3BKMCanonicalCurl02L2 hFourier :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3BKMCanonicalCurl02Amplitude hInt hMeas := by

  unfold h3BKMCanonicalCurl02L2

  exact
    MeasureTheory.MemLp.coeFn_toLp
      (h3BKMCanonicalCurl02Amplitude_memLp2 hFourier)

theorem h3BKMCanonicalCurl12L2_ae
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    (h3BKMCanonicalCurl12L2 hFourier :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3BKMCanonicalCurl12Amplitude hInt hMeas := by

  unfold h3BKMCanonicalCurl12L2

  exact
    MeasureTheory.MemLp.coeFn_toLp
      (h3BKMCanonicalCurl12Amplitude_memLp2 hFourier)

/-! ## Exact bundled Fourier identities for physical vorticity -/

theorem h3ScalarFourierL2_h3BKMPhysicalVorticityXL2_eq_neg_curl12L2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    h3ScalarFourierL2
        (h3BKMPhysicalVorticityXL2
          u t hInt hMeas)
      =
    - h3BKMCanonicalCurl12L2 hFourier := by

  apply MeasureTheory.Lp.ext

  filter_upwards [
    h3BKMPhysicalVorticityXL2_fourier_ae_eq_neg_curl12 hFourier,
    h3BKMCanonicalCurl12L2_ae hFourier,
    MeasureTheory.Lp.coeFn_neg
      (h3BKMCanonicalCurl12L2 hFourier)
  ] with ξ hPhysical hCurl hNeg

  rw [hPhysical, hNeg]
  simp only [Pi.neg_apply]
  rw [hCurl]

theorem h3ScalarFourierL2_h3BKMPhysicalVorticityYL2_eq_curl02L2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    h3ScalarFourierL2
        (h3BKMPhysicalVorticityYL2
          u t hInt hMeas)
      =
    h3BKMCanonicalCurl02L2 hFourier := by

  apply MeasureTheory.Lp.ext

  filter_upwards [
    h3BKMPhysicalVorticityYL2_fourier_ae_eq_curl02 hFourier,
    h3BKMCanonicalCurl02L2_ae hFourier
  ] with ξ hPhysical hCurl

  rw [hPhysical, hCurl]

theorem h3ScalarFourierL2_h3BKMPhysicalVorticityZL2_eq_neg_curl01L2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    h3ScalarFourierL2
        (h3BKMPhysicalVorticityZL2
          u t hInt hMeas)
      =
    - h3BKMCanonicalCurl01L2 hFourier := by

  apply MeasureTheory.Lp.ext

  filter_upwards [
    h3BKMPhysicalVorticityZL2_fourier_ae_eq_neg_curl01 hFourier,
    h3BKMCanonicalCurl01L2_ae hFourier,
    MeasureTheory.Lp.coeFn_neg
      (h3BKMCanonicalCurl01L2 hFourier)
  ] with ξ hPhysical hCurl hNeg

  rw [hPhysical, hNeg]
  simp only [Pi.neg_apply]
  rw [hCurl]

/-- Exact Plancherel transform of transported physical x-vorticity. -/
theorem h3BKMPhysicalVorticityXEuclideanComplex_fourier_eq_neg_curl12L2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    (𝓕
      (h3PhysicalScalarL2EuclideanComplex
        (h3BKMPhysicalVorticityXL2
          u t hInt hMeas)) :
      H3FourierComplexL2)
      =
    - h3BKMCanonicalCurl12L2 hFourier := by

  rw [
    ← h3ScalarFourierL2_eq_fourier_physicalScalarL2EuclideanComplex
      (h3BKMPhysicalVorticityXL2 u t hInt hMeas)
  ]

  exact
    h3ScalarFourierL2_h3BKMPhysicalVorticityXL2_eq_neg_curl12L2
      hFourier

/-- Exact Plancherel transform of transported physical y-vorticity. -/
theorem h3BKMPhysicalVorticityYEuclideanComplex_fourier_eq_curl02L2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    (𝓕
      (h3PhysicalScalarL2EuclideanComplex
        (h3BKMPhysicalVorticityYL2
          u t hInt hMeas)) :
      H3FourierComplexL2)
      =
    h3BKMCanonicalCurl02L2 hFourier := by

  rw [
    ← h3ScalarFourierL2_eq_fourier_physicalScalarL2EuclideanComplex
      (h3BKMPhysicalVorticityYL2 u t hInt hMeas)
  ]

  exact
    h3ScalarFourierL2_h3BKMPhysicalVorticityYL2_eq_curl02L2
      hFourier

/-- Exact Plancherel transform of transported physical z-vorticity. -/
theorem h3BKMPhysicalVorticityZEuclideanComplex_fourier_eq_neg_curl01L2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas) :
    (𝓕
      (h3PhysicalScalarL2EuclideanComplex
        (h3BKMPhysicalVorticityZL2
          u t hInt hMeas)) :
      H3FourierComplexL2)
      =
    - h3BKMCanonicalCurl01L2 hFourier := by

  rw [
    ← h3ScalarFourierL2_eq_fourier_physicalScalarL2EuclideanComplex
      (h3BKMPhysicalVorticityZL2 u t hInt hMeas)
  ]

  exact
    h3ScalarFourierL2_h3BKMPhysicalVorticityZL2_eq_neg_curl01L2
      hFourier

/-! ## Dyadic kernel and multiplier as L² states -/

/-- One dyadic inverse-Fourier kernel as an `L²` state. -/
noncomputable def h3BKMDyadicKernelL2
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3) :
    H3FourierComplexL2 :=
  (h3BKMDyadicKernelSchwartz R hR i k).toLp
    2
    (volume : Measure H3FourierPoint3)

/-- The dyadic-kernel `L²` package has the expected representative a.e. -/
theorem h3BKMDyadicKernelL2_ae
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (h3BKMDyadicKernelL2 R hR i k :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3BKMDyadicKernel R hR i k := by

  unfold h3BKMDyadicKernelL2
  unfold h3BKMDyadicKernel

  exact
    SchwartzMap.coeFn_toLp
      (h3BKMDyadicKernelSchwartz R hR i k)
      2
      (volume : Measure H3FourierPoint3)

/-- One localized BKM coordinate multiplier as an `L²` state. -/
noncomputable def h3BKMLocalizedCoordinateMultiplierL2
    (R : ℝ)
    (hR : 0 < R)
    (i k : Fin 3) :
    H3FourierComplexL2 :=
  (h3BKMLocalizedCoordinateMultiplierSchwartz
      R hR i k).toLp
    2
    (volume : Measure H3FourierPoint3)

/-- The localized-multiplier `L²` package has the expected representative. -/
theorem h3BKMLocalizedCoordinateMultiplierL2_ae
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (h3BKMLocalizedCoordinateMultiplierL2
        R hR i k :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3BKMLocalizedCoordinateMultiplier
      R hR i k := by

  unfold h3BKMLocalizedCoordinateMultiplierL2

  have hLp :=
    SchwartzMap.coeFn_toLp
      (h3BKMLocalizedCoordinateMultiplierSchwartz
        R hR i k)
      2
      (volume : Measure H3FourierPoint3)

  filter_upwards [hLp] with ξ hξ

  rw [hξ]

  exact
    h3BKMLocalizedCoordinateMultiplierSchwartz_apply
      hR i k ξ

/--
The `L²` Fourier transform of the dyadic inverse-Fourier kernel is exactly the
localized BKM coordinate multiplier.
-/
theorem h3BKMDyadicKernelL2_fourier_eq_localizedCoordinateMultiplierL2
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (𝓕 (h3BKMDyadicKernelL2 R hR i k) :
        H3FourierComplexL2)
      =
    h3BKMLocalizedCoordinateMultiplierL2
      R hR i k := by

  unfold
    h3BKMDyadicKernelL2
    h3BKMLocalizedCoordinateMultiplierL2

  rw [SchwartzMap.toLp_fourier_eq]

  unfold h3BKMDyadicKernelSchwartz

  rw [FourierTransform.fourier_fourierInv_eq]

end

end Euclidean
end Bridge
end PrimeTensor
