import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicYoungSchwartzBridge

/-!
# BKM endpoint: Fourier identities for dyadic physical-vorticity convolutions

The endpoint Young/Schwartz bridge now proves for every complex Fourier-carrier
`L²` state `F` that

    𝓕(Kᵢₖ,R * F) = Mᵢₖ,R · 𝓕F.

The canonical physical vorticity components already have exact Fourier
identities, and `DyadicFourierLocalization` already records the corresponding
localized sign conventions:

    M 𝓕ωₓ = -(M C12),
    M 𝓕ωᵧ =   M C02,
    M 𝓕ω_z = -(M C01).

This file specializes the arbitrary-`L²` convolution theorem to those three
physical-vorticity states.  The resulting identities are the exact bundled
Fourier bridge needed to identify each physical dyadic convolution with the
existing localized inverse-Fourier curl reconstruction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open FourierTransform
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicVorticityConvolutionFourier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Fourier transform of the dyadic x-vorticity convolution is minus the localized
`C12` state.
-/
theorem h3BKMDyadicVorticityXConvolutionL2_fourier_eq_neg_localizedCurl12
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
      (h3BKMDyadicVorticityXConvolutionL2
        hInt hMeas R hR i k)
      =
    - h3BKMLocalizedCanonicalCurl12L2
        hFourier R hR i k := by

  unfold h3BKMDyadicVorticityXConvolutionL2

  calc
    (MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
      (h3L1L2Convolution
        (h3BKMDyadicKernelL1 R hR i k)
        (h3PhysicalScalarL2EuclideanComplex
          (h3BKMPhysicalVorticityXL2
            u t hInt hMeas)))
        =
      h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k
        ((MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ)
          (h3PhysicalScalarL2EuclideanComplex
            (h3BKMPhysicalVorticityXL2
              u t hInt hMeas))) := by
          exact
            h3BKMDyadicKernelConvolution_fourier_eq_localized_all
              hR i k
              (h3PhysicalScalarL2EuclideanComplex
                (h3BKMPhysicalVorticityXL2
                  u t hInt hMeas))
    _ =
      h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k
        (h3ScalarFourierL2
          (h3BKMPhysicalVorticityXL2
            u t hInt hMeas)) := by

          have hPhysicalFourier :
              (MeasureTheory.Lp.fourierTransformₗᵢ
                  H3FourierPoint3 ℂ)
                (h3PhysicalScalarL2EuclideanComplex
                  (h3BKMPhysicalVorticityXL2
                    u t hInt hMeas))
                =
              h3ScalarFourierL2
                (h3BKMPhysicalVorticityXL2
                  u t hInt hMeas) := by

            change
              (𝓕
                (h3PhysicalScalarL2EuclideanComplex
                  (h3BKMPhysicalVorticityXL2
                    u t hInt hMeas)) :
                H3FourierComplexL2)
                =
              h3ScalarFourierL2
                (h3BKMPhysicalVorticityXL2
                  u t hInt hMeas)

            exact
              (h3ScalarFourierL2_eq_fourier_physicalScalarL2EuclideanComplex
                (h3BKMPhysicalVorticityXL2
                  u t hInt hMeas)).symm

          rw [hPhysicalFourier]
    _ =
      - h3BKMLocalizedCanonicalCurl12L2
          hFourier R hR i k := by
          exact
            h3BKMLocalizedCoordinateMultiplierApplyL2_physicalVorticityX_fourier
              hFourier hR i k

/--
Fourier transform of the dyadic y-vorticity convolution is the localized
`C02` state.
-/
theorem h3BKMDyadicVorticityYConvolutionL2_fourier_eq_localizedCurl02
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
      (h3BKMDyadicVorticityYConvolutionL2
        hInt hMeas R hR i k)
      =
    h3BKMLocalizedCanonicalCurl02L2
      hFourier R hR i k := by

  unfold h3BKMDyadicVorticityYConvolutionL2

  calc
    (MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
      (h3L1L2Convolution
        (h3BKMDyadicKernelL1 R hR i k)
        (h3PhysicalScalarL2EuclideanComplex
          (h3BKMPhysicalVorticityYL2
            u t hInt hMeas)))
        =
      h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k
        ((MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ)
          (h3PhysicalScalarL2EuclideanComplex
            (h3BKMPhysicalVorticityYL2
              u t hInt hMeas))) := by
          exact
            h3BKMDyadicKernelConvolution_fourier_eq_localized_all
              hR i k
              (h3PhysicalScalarL2EuclideanComplex
                (h3BKMPhysicalVorticityYL2
                  u t hInt hMeas))
    _ =
      h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k
        (h3ScalarFourierL2
          (h3BKMPhysicalVorticityYL2
            u t hInt hMeas)) := by

          have hPhysicalFourier :
              (MeasureTheory.Lp.fourierTransformₗᵢ
                  H3FourierPoint3 ℂ)
                (h3PhysicalScalarL2EuclideanComplex
                  (h3BKMPhysicalVorticityYL2
                    u t hInt hMeas))
                =
              h3ScalarFourierL2
                (h3BKMPhysicalVorticityYL2
                  u t hInt hMeas) := by

            change
              (𝓕
                (h3PhysicalScalarL2EuclideanComplex
                  (h3BKMPhysicalVorticityYL2
                    u t hInt hMeas)) :
                H3FourierComplexL2)
                =
              h3ScalarFourierL2
                (h3BKMPhysicalVorticityYL2
                  u t hInt hMeas)

            exact
              (h3ScalarFourierL2_eq_fourier_physicalScalarL2EuclideanComplex
                (h3BKMPhysicalVorticityYL2
                  u t hInt hMeas)).symm

          rw [hPhysicalFourier]
    _ =
      h3BKMLocalizedCanonicalCurl02L2
        hFourier R hR i k := by
          exact
            h3BKMLocalizedCoordinateMultiplierApplyL2_physicalVorticityY_fourier
              hFourier hR i k

/--
Fourier transform of the dyadic z-vorticity convolution is minus the localized
`C01` state.
-/
theorem h3BKMDyadicVorticityZConvolutionL2_fourier_eq_neg_localizedCurl01
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    (MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
      (h3BKMDyadicVorticityZConvolutionL2
        hInt hMeas R hR i k)
      =
    - h3BKMLocalizedCanonicalCurl01L2
        hFourier R hR i k := by

  unfold h3BKMDyadicVorticityZConvolutionL2

  calc
    (MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
      (h3L1L2Convolution
        (h3BKMDyadicKernelL1 R hR i k)
        (h3PhysicalScalarL2EuclideanComplex
          (h3BKMPhysicalVorticityZL2
            u t hInt hMeas)))
        =
      h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k
        ((MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ)
          (h3PhysicalScalarL2EuclideanComplex
            (h3BKMPhysicalVorticityZL2
              u t hInt hMeas))) := by
          exact
            h3BKMDyadicKernelConvolution_fourier_eq_localized_all
              hR i k
              (h3PhysicalScalarL2EuclideanComplex
                (h3BKMPhysicalVorticityZL2
                  u t hInt hMeas))
    _ =
      h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k
        (h3ScalarFourierL2
          (h3BKMPhysicalVorticityZL2
            u t hInt hMeas)) := by

          have hPhysicalFourier :
              (MeasureTheory.Lp.fourierTransformₗᵢ
                  H3FourierPoint3 ℂ)
                (h3PhysicalScalarL2EuclideanComplex
                  (h3BKMPhysicalVorticityZL2
                    u t hInt hMeas))
                =
              h3ScalarFourierL2
                (h3BKMPhysicalVorticityZL2
                  u t hInt hMeas) := by

            change
              (𝓕
                (h3PhysicalScalarL2EuclideanComplex
                  (h3BKMPhysicalVorticityZL2
                    u t hInt hMeas)) :
                H3FourierComplexL2)
                =
              h3ScalarFourierL2
                (h3BKMPhysicalVorticityZL2
                  u t hInt hMeas)

            exact
              (h3ScalarFourierL2_eq_fourier_physicalScalarL2EuclideanComplex
                (h3BKMPhysicalVorticityZL2
                  u t hInt hMeas)).symm

          rw [hPhysicalFourier]
    _ =
      - h3BKMLocalizedCanonicalCurl01L2
          hFourier R hR i k := by
          exact
            h3BKMLocalizedCoordinateMultiplierApplyL2_physicalVorticityZ_fourier
              hFourier hR i k

end

end Euclidean
end Bridge
end PrimeTensor
