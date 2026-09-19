import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.LowFrequencyGradientSpectral
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Round.Trip

/-!
# BKM endpoint: physical L² control of the low-frequency gradient

`LowFrequencyGradientSpectral` bounds the fixed low-frequency gradient by the
canonical raw Fourier `L²` mass of one weighted H³ spectral component.

For a genuine encoded velocity snapshot that raw Fourier state is not merely
comparable to the physical velocity: the encoder/decoder round-trip identifies
it exactly with the zeroth-order Fourier transform of the corresponding
physical velocity component.  Plancherel therefore gives the exact norm
identity

    ‖rawFourierL2 (encoded u_j)‖₂ = ‖u_j‖₂.

This file inserts that identity into the BKM low-frequency estimate.  The
result is the form needed for the later kinetic-energy conservation step: the
low term depends only on physical base velocity `L²`, not on the growing H³
energy.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointLowFrequencyGradientPhysicalL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Raw Fourier mass equals physical base velocity mass -/

/--
For a genuinely encoded H³ velocity component, the norm of its canonical raw
Fourier `L²` package is exactly the physical zeroth-order component `L²` norm.
-/
theorem norm_h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j : Fin 3) :
    ‖h3SpectralScalarRawFourierL2
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j)‖
      =
    ‖velocityH3L2JetAt
        u t hInt hMeas
        (h3JetSlot0 j)‖ := by

  rw [
    h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
      hFourier j
  ]

  change
    ‖h3ScalarFourierL2
        (velocityH3L2JetAt
          u t hInt hMeas
          (h3JetSlot0 j))‖
      =
    ‖velocityH3L2JetAt
        u t hInt hMeas
        (h3JetSlot0 j)‖

  exact
    norm_h3ScalarFourierL2
      (velocityH3L2JetAt
        u t hInt hMeas
        (h3JetSlot0 j))

/-! ## Sharp physical low-frequency bound -/

/--
The fixed-scale low-frequency gradient of one genuine encoded velocity
component is bounded pointwise by the physical `L²` mass of that component.
-/
theorem norm_fourierInv_h3BKMLowGradientAmplitude_zero_le_physicalL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t : ℝ}
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (j i : Fin 3)
    (x : H3FourierPoint3) :
    ‖FourierTransformInv.fourierInv
        (h3BKMLowGradientAmplitude
          0
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j)
          i)
        x‖
      ≤
    h3BKMLowGradientUnitL2Constant
      *
    ‖velocityH3L2JetAt
        u t hInt hMeas
        (h3JetSlot0 j)‖ := by

  calc
    ‖FourierTransformInv.fourierInv
        (h3BKMLowGradientAmplitude
          0
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j)
          i)
        x‖
        ≤
      h3BKMLowGradientUnitL2Constant
        *
      ‖h3SpectralScalarRawFourierL2
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j)‖ :=
      norm_fourierInv_h3BKMLowGradientAmplitude_zero_le_rawFourierL2
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j)
        i x

    _ =
      h3BKMLowGradientUnitL2Constant
        *
      ‖velocityH3L2JetAt
          u t hInt hMeas
          (h3JetSlot0 j)‖ := by
        rw [
          norm_h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
            hFourier j
        ]

end

end Euclidean
end Bridge
end PrimeTensor
