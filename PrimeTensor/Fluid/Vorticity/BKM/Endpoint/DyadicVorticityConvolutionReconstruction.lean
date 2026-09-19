import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.DyadicVorticityConvolutionFourier

/-!
# BKM endpoint: reconstruct dyadic physical-vorticity convolutions

`DyadicVorticityConvolutionFourier` identifies the Fourier transforms of the
three physical dyadic vorticity convolution states:

    𝓕(K * ωₓ) = - localized C12,
    𝓕(K * ωᵧ) =   localized C02,
    𝓕(K * ω_z) = - localized C01.

The localized curl inverse states were already defined as the inverse unitary
Fourier transforms of those localized curl `L²` packages.  Since the `L²`
Fourier transform is an isometric equivalence, applying its inverse now gives

    K * ωₓ = - localizedInverse(C12),
    K * ωᵧ =   localizedInverse(C02),
    K * ω_z = - localizedInverse(C01).

This is the exact bundled reconstruction bridge between the physical
vorticity convolution side and the localized spectral Biot--Savart side.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open FourierTransform
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicVorticityConvolutionReconstruction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
The dyadic x-vorticity convolution is exactly minus the inverse-Fourier
localized `C12` state.
-/
theorem h3BKMDyadicVorticityXConvolutionL2_eq_neg_localizedCurl12InverseL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    h3BKMDyadicVorticityXConvolutionL2
        hInt hMeas R hR i k
      =
    - h3BKMLocalizedCanonicalCurl12InverseL2
        hFourier R hR i k := by

  let T :=
    MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ

  calc
    h3BKMDyadicVorticityXConvolutionL2
        hInt hMeas R hR i k
        =
      T.symm
        (T
          (h3BKMDyadicVorticityXConvolutionL2
            hInt hMeas R hR i k)) := by
          exact
            (T.symm_apply_apply
              (h3BKMDyadicVorticityXConvolutionL2
                hInt hMeas R hR i k)).symm

    _ =
      T.symm
        (- h3BKMLocalizedCanonicalCurl12L2
          hFourier R hR i k) := by
          rw [
            h3BKMDyadicVorticityXConvolutionL2_fourier_eq_neg_localizedCurl12
              hFourier hR i k
          ]

    _ =
      - T.symm
          (h3BKMLocalizedCanonicalCurl12L2
            hFourier R hR i k) := by
          exact
            T.symm.map_neg
              (h3BKMLocalizedCanonicalCurl12L2
                hFourier R hR i k)

    _ =
      - h3BKMLocalizedCanonicalCurl12InverseL2
          hFourier R hR i k := by
          rfl

/--
The dyadic y-vorticity convolution is exactly the inverse-Fourier localized
`C02` state.
-/
theorem h3BKMDyadicVorticityYConvolutionL2_eq_localizedCurl02InverseL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    h3BKMDyadicVorticityYConvolutionL2
        hInt hMeas R hR i k
      =
    h3BKMLocalizedCanonicalCurl02InverseL2
      hFourier R hR i k := by

  let T :=
    MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ

  calc
    h3BKMDyadicVorticityYConvolutionL2
        hInt hMeas R hR i k
        =
      T.symm
        (T
          (h3BKMDyadicVorticityYConvolutionL2
            hInt hMeas R hR i k)) := by
          exact
            (T.symm_apply_apply
              (h3BKMDyadicVorticityYConvolutionL2
                hInt hMeas R hR i k)).symm

    _ =
      T.symm
        (h3BKMLocalizedCanonicalCurl02L2
          hFourier R hR i k) := by
          rw [
            h3BKMDyadicVorticityYConvolutionL2_fourier_eq_localizedCurl02
              hFourier hR i k
          ]

    _ =
      h3BKMLocalizedCanonicalCurl02InverseL2
        hFourier R hR i k := by
          rfl

/--
The dyadic z-vorticity convolution is exactly minus the inverse-Fourier
localized `C01` state.
-/
theorem h3BKMDyadicVorticityZConvolutionL2_eq_neg_localizedCurl01InverseL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3) :
    h3BKMDyadicVorticityZConvolutionL2
        hInt hMeas R hR i k
      =
    - h3BKMLocalizedCanonicalCurl01InverseL2
        hFourier R hR i k := by

  let T :=
    MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ

  calc
    h3BKMDyadicVorticityZConvolutionL2
        hInt hMeas R hR i k
        =
      T.symm
        (T
          (h3BKMDyadicVorticityZConvolutionL2
            hInt hMeas R hR i k)) := by
          exact
            (T.symm_apply_apply
              (h3BKMDyadicVorticityZConvolutionL2
                hInt hMeas R hR i k)).symm

    _ =
      T.symm
        (- h3BKMLocalizedCanonicalCurl01L2
          hFourier R hR i k) := by
          rw [
            h3BKMDyadicVorticityZConvolutionL2_fourier_eq_neg_localizedCurl01
              hFourier hR i k
          ]

    _ =
      - T.symm
          (h3BKMLocalizedCanonicalCurl01L2
            hFourier R hR i k) := by
          exact
            T.symm.map_neg
              (h3BKMLocalizedCanonicalCurl01L2
                hFourier R hR i k)

    _ =
      - h3BKMLocalizedCanonicalCurl01InverseL2
          hFourier R hR i k := by
          rfl

end

end Euclidean
end Bridge
end PrimeTensor
