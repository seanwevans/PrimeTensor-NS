import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Gradient.Low.L2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Raw.Fourier.L2

/-!
# BKM endpoint: low-frequency gradient of a weighted H³ spectral state

`LowFrequencyGradientL2` proves the sharp low-frequency estimate for an
arbitrary base Fourier `L²` state.  The endpoint trichotomy, however, is written
in terms of a weighted H³ spectral state `G` and its raw Fourier derivative.

This file identifies those two formulations.

The canonical raw Fourier package

    h3SpectralScalarRawFourierL2 G

has `h3SpectralScalarRawFourier G` as an almost-everywhere representative.
Consequently

    χ_lo d_i G_raw

is a.e. the same amplitude as the generic low-gradient multiplier applied to
that raw `L²` package.  At the fixed endpoint scale `lo = 0`, the sharp bound
from the previous file therefore applies directly to the concrete trichotomy
amplitude.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointLowFrequencyGradientSpectral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Identification with the canonical raw Fourier L² package -/

/--
The concrete low-frequency derivative amplitude of a weighted H³ state is a.e.
the generic low-gradient multiplier applied to its canonical raw Fourier `L²`
package.
-/
theorem h3BKMLowGradientAmplitude_ae_rawFourierL2
    (lo : ℕ)
    (G : H3SpectralScalarState)
    (i : Fin 3) :
    h3BKMLowGradientAmplitude lo G i
      =ᵐ[(volume : Measure H3FourierPoint3)]
    fun ξ : H3FourierPoint3 =>
      h3BKMLowGradientMultiplier lo i ξ
        * h3SpectralScalarRawFourierL2 G ξ := by

  filter_upwards [
    h3SpectralScalarRawFourierL2_ae G
  ] with ξ hRaw

  rw [hRaw]

  unfold
    h3BKMLowGradientAmplitude
    h3BKMLowGradientMultiplier
    h3SpectralScalarRawFourierCoordinateDerivative

  ring

/--
Equivalently, the generic `L¹` Hölder package built from the canonical raw
Fourier `L²` state has the concrete trichotomy amplitude as its a.e.
representative.
-/
theorem h3BKMLowGradientHolderL1_rawFourier_ae
    (lo : ℕ)
    (G : H3SpectralScalarState)
    (i : Fin 3) :
    (h3BKMLowGradientHolderL1
        lo i
        (h3SpectralScalarRawFourierL2 G) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3BKMLowGradientAmplitude lo G i := by

  filter_upwards [
    h3BKMLowGradientHolderL1_ae
      lo i
      (h3SpectralScalarRawFourierL2 G),
    h3SpectralScalarRawFourierL2_ae G
  ] with ξ hHolder hRaw

  rw [hHolder, hRaw]

  unfold
    h3BKMLowGradientAmplitude
    h3BKMLowGradientMultiplier
    h3SpectralScalarRawFourierCoordinateDerivative

  ring

/-! ## Fixed-scale sharp low-frequency estimate -/

/--
The ordinary inverse Fourier reconstruction of the concrete fixed-scale
low-frequency gradient is bounded by the raw base Fourier `L²` mass.
-/
theorem norm_fourierInv_h3BKMLowGradientAmplitude_zero_le_rawFourierL2
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖FourierTransformInv.fourierInv
        (h3BKMLowGradientAmplitude 0 G i)
        x‖
      ≤
    h3BKMLowGradientUnitL2Constant
      * ‖h3SpectralScalarRawFourierL2 G‖ := by

  have hInv :
      FourierTransformInv.fourierInv
          (h3BKMLowGradientAmplitude 0 G i)
          x
        =
      FourierTransformInv.fourierInv
          (fun ξ : H3FourierPoint3 =>
            h3BKMLowGradientMultiplier 0 i ξ
              * h3SpectralScalarRawFourierL2 G ξ)
          x :=
    _root_.Real.fourierInv_congr_ae
      (h3BKMLowGradientAmplitude_ae_rawFourierL2
        0 G i)
      x

  rw [hInv]

  exact
    norm_fourierInv_h3BKMLowGradientHolderL1_zero_le
      i
      (h3SpectralScalarRawFourierL2 G)
      x

/--
The raw Fourier `L²` mass is itself bounded by the weighted H³ norm, giving a
coarser compatibility corollary while keeping the sharper base-mass theorem
available for the later kinetic-energy bridge.
-/
theorem norm_fourierInv_h3BKMLowGradientAmplitude_zero_le
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖FourierTransformInv.fourierInv
        (h3BKMLowGradientAmplitude 0 G i)
        x‖
      ≤
    h3BKMLowGradientUnitL2Constant * ‖G‖ := by

  calc
    ‖FourierTransformInv.fourierInv
        (h3BKMLowGradientAmplitude 0 G i)
        x‖
        ≤
      h3BKMLowGradientUnitL2Constant
        * ‖h3SpectralScalarRawFourierL2 G‖ :=
      norm_fourierInv_h3BKMLowGradientAmplitude_zero_le_rawFourierL2
        G i x

    _ ≤
      h3BKMLowGradientUnitL2Constant * ‖G‖ := by
        exact
          mul_le_mul_of_nonneg_left
            (norm_h3SpectralScalarRawFourierL2_le G)
            h3BKMLowGradientUnitL2Constant_nonneg

end

end Euclidean
end Bridge
end PrimeTensor
