import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Dyadic.Young.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Density

/-!
# BKM endpoint: close the dyadic convolution identity from Schwartz data

The two sides of the desired dyadic multiplier/convolution theorem are now
continuous on Fourier-carrier `L²`:

* `DyadicLocalizationContinuity` proves continuity of

      F ↦ Mᵢₖ,R · 𝓕F;

* `DyadicYoungContinuity` proves continuity of

      F ↦ 𝓕(Kᵢₖ,R * F),

  where convolution is the project's endpoint `L¹ * L² → L²` Bochner
  construction.

Schwartz functions are dense in the same `L²` carrier.  Therefore equality of
these two operators on Schwartz inputs extends automatically to all `L²`
inputs.

This file records exactly that closure theorem.  It deliberately assumes only
the smooth Schwartz anchor

    𝓕(K * P) = M · 𝓕P

for `P : 𝓢(H3FourierPoint3, ℂ)` and performs no further convolution analysis.
The next checkpoint can focus entirely on proving that smooth anchor.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal FourierTransform

noncomputable section

noncomputable local instance axisFintypeBKMEndpointDyadicConvolutionClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
A dyadic Fourier/convolution identity proved for every Schwartz `L²` input
extends to every Fourier-carrier complex `L²` input.

This is the exact density closure needed for the BKM endpoint bridge.
-/
theorem h3BKMDyadicKernelConvolution_fourier_eq_localized_of_schwartz
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (hSchwartz :
      ∀ P : SchwartzMap H3FourierPoint3 ℂ,
        (MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ)
          (h3L1L2Convolution
            (h3BKMDyadicKernelL1 R hR i k)
            (P.toLp
              2
              (volume : Measure H3FourierPoint3)))
          =
        h3BKMLocalizedCoordinateMultiplierApplyL2
          R hR i k
          ((MeasureTheory.Lp.fourierTransformₗᵢ
              H3FourierPoint3 ℂ)
            (P.toLp
              2
              (volume : Measure H3FourierPoint3)))) :
    ∀ F : H3FourierComplexL2,
      (MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ)
        (h3L1L2Convolution
          (h3BKMDyadicKernelL1 R hR i k)
          F)
        =
      h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k
        ((MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ) F) := by

  let A : H3FourierComplexL2 → H3FourierComplexL2 :=
    fun F =>
      (MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ)
        (h3L1L2Convolution
          (h3BKMDyadicKernelL1 R hR i k)
          F)

  let B : H3FourierComplexL2 → H3FourierComplexL2 :=
    fun F =>
      h3BKMLocalizedCoordinateMultiplierApplyL2
        R hR i k
        ((MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ) F)

  let p : H3FourierComplexL2 → Prop :=
    fun F => A F = B F

  have hA : Continuous A := by
    dsimp only [A]
    exact
      continuous_h3BKMDyadicKernelConvolutionL2_fourier
        hR i k

  have hB : Continuous B := by
    dsimp only [B]
    exact
      continuous_h3BKMFourierLocalizedCoordinateMultiplierApplyL2
        hR i k

  have hpClosed :
      IsClosed {F : H3FourierComplexL2 | p F} := by
    dsimp only [p]
    exact isClosed_eq hA hB

  intro F

  apply DenseRange.induction_on
    (p := p)
    h3Schwartz_denseRange_toSpectralScalar
    F

  · exact hpClosed

  intro P

  simpa only [
    p,
    A,
    B
  ] using hSchwartz P

/--
Pointwise formulation of the same closure principle: to prove the dyadic
Fourier/convolution identity for one arbitrary `L²` input, it is enough to
supply the uniform Schwartz anchor theorem.
-/
theorem h3BKMDyadicKernelConvolution_fourier_eq_localized
    {R : ℝ}
    (hR : 0 < R)
    (i k : Fin 3)
    (F : H3FourierComplexL2)
    (hSchwartz :
      ∀ P : SchwartzMap H3FourierPoint3 ℂ,
        (MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ)
          (h3L1L2Convolution
            (h3BKMDyadicKernelL1 R hR i k)
            (P.toLp
              2
              (volume : Measure H3FourierPoint3)))
          =
        h3BKMLocalizedCoordinateMultiplierApplyL2
          R hR i k
          ((MeasureTheory.Lp.fourierTransformₗᵢ
              H3FourierPoint3 ℂ)
            (P.toLp
              2
              (volume : Measure H3FourierPoint3)))) :
    (MeasureTheory.Lp.fourierTransformₗᵢ
        H3FourierPoint3 ℂ)
      (h3L1L2Convolution
        (h3BKMDyadicKernelL1 R hR i k)
        F)
      =
    h3BKMLocalizedCoordinateMultiplierApplyL2
      R hR i k
      ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ) F) := by

  exact
    h3BKMDyadicKernelConvolution_fourier_eq_localized_of_schwartz
      hR i k hSchwartz F

end

end Euclidean
end Bridge
end PrimeTensor
