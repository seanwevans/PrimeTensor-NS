import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.SelectedMiddleGradientReconstruction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Point3Derivative

/-!
# BKM endpoint: reconstruct the complete selected gradient model

The selected middle Fourier amplitude has now been reconstructed back to the
physical middle proxy.  The low and high pieces already live directly in
ordinary inverse-Fourier form.

This file closes the exact low/middle/high reconstruction of one encoded H³
velocity-coordinate derivative.

First, the selected middle amplitude identity is rearranged to the exact
frequency decomposition

    raw derivative = low + middle + high

almost everywhere.  `Real.fourierInv_congr_ae` upgrades that Fourier a.e.
identity to pointwise equality of ordinary inverse-Fourier reconstructions.
Linearity of the Fourier integral then separates the three pieces.

After pulling to `Point3`, the selected-middle reconstruction theorem replaces
the ordinary inverse Fourier middle piece almost everywhere by the canonical
physical middle proxy.  Thus the complete selected gradient model agrees almost
everywhere with the genuine raw-coordinate inverse Fourier derivative.

Finally, the existing arbitrary-H³ `Point3` derivative theorem identifies the
real part of that inverse Fourier derivative with `spatial3.d`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointSelectedGradientReconstruction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointSelectedGradientReconstruction :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Exact selected frequency decomposition -/

/--
The genuine raw Fourier coordinate derivative is the sum of the selected low,
middle, and high Fourier amplitudes almost everywhere.
-/
theorem h3SpectralScalarRawFourierCoordinateDerivative_ae_eq_selected_low_middle_high
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (A : ℝ)
    (j i : Fin 3) :
    h3SpectralScalarRawFourierCoordinateDerivative
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j)
        i
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3BKMLowGradientAmplitude
        0
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j)
        i
      +
    h3BKMSelectedMiddleGradientFourierAmplitude
        hFourier A j i
      +
    h3BKMHighGradientAmplitude
        (h3BKMUpperCutoffIndex A)
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j)
        i := by

  have hMiddle :=
    h3BKMSelectedMiddleGradientFourierAmplitude_ae_eq_raw_sub_low_sub_high
      hNS ht hFourier A j i

  filter_upwards [hMiddle] with ξ hξ

  change
    h3SpectralScalarRawFourierCoordinateDerivative
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j)
        i ξ
      =
    h3BKMLowGradientAmplitude
        0
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j)
        i ξ
      +
    h3BKMSelectedMiddleGradientFourierAmplitude
        hFourier A j i ξ
      +
    h3BKMHighGradientAmplitude
        (h3BKMUpperCutoffIndex A)
        (velocityH3SpectralScalarAt
          u t hInt hMeas hFourier j)
        i ξ

  rw [hξ]
  abel

/-! ## Pointwise ordinary inverse-Fourier reconstruction -/

/--
On the Fourier carrier, the ordinary inverse Fourier transform of the genuine
raw derivative is exactly the sum of the ordinary inverse Fourier transforms of
the selected low, middle, and high amplitudes.
-/
theorem fourierInv_h3SpectralScalarRawFourierCoordinateDerivative_eq_selected_low_middle_high
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (A : ℝ)
    (j i : Fin 3)
    (x : H3FourierPoint3) :
    FourierTransformInv.fourierInv
        (h3SpectralScalarRawFourierCoordinateDerivative
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j)
          i)
        x
      =
    FourierTransformInv.fourierInv
        (h3BKMLowGradientAmplitude
          0
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j)
          i)
        x
      +
    FourierTransformInv.fourierInv
        (h3BKMSelectedMiddleGradientFourierAmplitude
          hFourier A j i)
        x
      +
    FourierTransformInv.fourierInv
        (h3BKMHighGradientAmplitude
          (h3BKMUpperCutoffIndex A)
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j)
          i)
        x := by

  let G : H3SpectralScalarState :=
    velocityH3SpectralScalarAt
      u t hInt hMeas hFourier j

  let L : H3FourierPoint3 → ℂ :=
    h3BKMLowGradientAmplitude 0 G i

  let M : H3FourierPoint3 → ℂ :=
    h3BKMSelectedMiddleGradientFourierAmplitude
      hFourier A j i

  let H : H3FourierPoint3 → ℂ :=
    h3BKMHighGradientAmplitude
      (h3BKMUpperCutoffIndex A) G i

  have hAmp :
      h3SpectralScalarRawFourierCoordinateDerivative G i
        =ᵐ[(volume : Measure H3FourierPoint3)]
      L + M + H := by
    dsimp only [G, L, M, H]
    exact
      h3SpectralScalarRawFourierCoordinateDerivative_ae_eq_selected_low_middle_high
        hNS ht hFourier A j i

  have hL :
      Integrable L
        (volume : Measure H3FourierPoint3) := by
    dsimp only [L]
    exact h3BKMLowGradientAmplitude_integrable 0 G i

  have hM :
      Integrable M
        (volume : Measure H3FourierPoint3) := by
    dsimp only [M, G]
    exact
      h3BKMSelectedMiddleGradientFourierAmplitude_integrable
        hNS ht hFourier A j i

  have hH :
      Integrable H
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3BKMHighGradientAmplitude_integrable
        (h3BKMUpperCutoffIndex A) G i

  have hInnerNegContinuous :
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          ((-(innerₗ H3FourierPoint3)) p.1) p.2) := by
    change
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          -inner ℝ p.1 p.2)
    exact
      (continuous_inner
        (𝕜 := ℝ)
        (E := H3FourierPoint3)).neg

  have hInvEq :
      FourierTransformInv.fourierInv
          (h3SpectralScalarRawFourierCoordinateDerivative G i)
          x
        =
      FourierTransformInv.fourierInv
          (L + M + H)
          x := by
    exact
      _root_.Real.fourierInv_congr_ae
        hAmp x

  have hLM :
      Integrable (L + M)
        (volume : Measure H3FourierPoint3) :=
    hL.add hM

  have hInvOuter :
      FourierTransformInv.fourierInv
          (L + M + H)
          x
        =
      FourierTransformInv.fourierInv
          (L + M)
          x
        +
      FourierTransformInv.fourierInv
          H
          x := by

    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((L + M) + H)
          x
        =
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (L + M)
          x
        +
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          H
          x

    exact
      congrFun
        (VectorFourier.fourierIntegral_add
          (e := Real.fourierChar)
          (μ := (volume : Measure H3FourierPoint3))
          (L := -(innerₗ H3FourierPoint3))
          Real.continuous_fourierChar
          hInnerNegContinuous
          hLM
          hH)
        x

  have hInvInner :
      FourierTransformInv.fourierInv
          (L + M)
          x
        =
      FourierTransformInv.fourierInv
          L
          x
        +
      FourierTransformInv.fourierInv
          M
          x := by

    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (L + M)
          x
        =
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          L
          x
        +
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          M
          x

    exact
      congrFun
        (VectorFourier.fourierIntegral_add
          (e := Real.fourierChar)
          (μ := (volume : Measure H3FourierPoint3))
          (L := -(innerₗ H3FourierPoint3))
          Real.continuous_fourierChar
          hInnerNegContinuous
          hL
          hM)
        x

  calc
    FourierTransformInv.fourierInv
        (h3SpectralScalarRawFourierCoordinateDerivative G i)
        x
        =
      FourierTransformInv.fourierInv
        (L + M + H)
        x := hInvEq

    _ =
      FourierTransformInv.fourierInv
        (L + M)
        x
        +
      FourierTransformInv.fourierInv H x := hInvOuter

    _ =
      (FourierTransformInv.fourierInv L x
        +
       FourierTransformInv.fourierInv M x)
        +
      FourierTransformInv.fourierInv H x := by
      rw [hInvInner]

    _ =
      FourierTransformInv.fourierInv
          (h3BKMLowGradientAmplitude
            0
            (velocityH3SpectralScalarAt
              u t hInt hMeas hFourier j)
            i)
          x
        +
      FourierTransformInv.fourierInv
          (h3BKMSelectedMiddleGradientFourierAmplitude
            hFourier A j i)
          x
        +
      FourierTransformInv.fourierInv
          (h3BKMHighGradientAmplitude
            (h3BKMUpperCutoffIndex A)
            (velocityH3SpectralScalarAt
              u t hInt hMeas hFourier j)
            i)
          x := by
      rfl

/-! ## Physical-carrier reconstruction -/

/--
Pulled to `Point3`, the genuine raw-coordinate inverse Fourier derivative
agrees almost everywhere with the complete selected gradient model.
-/
theorem fourierInv_h3SpectralScalarRawFourierCoordinateDerivative_toLp_ae_eq_selectedGradientModel
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {g : ℝ → ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (j i : Fin 3) :
    (fun x : Point3 =>
      FourierTransformInv.fourierInv
        (h3SpectralScalarRawFourierCoordinateDerivative
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j)
          i)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    h3BKMSelectedGradientModel
      hFourier A j i := by

  have hMiddle :=
    fourierInv_h3BKMSelectedMiddleGradientFourierAmplitude_toLp_ae_eq_physical
      hNS ht hFourier hEnvelope A j i

  filter_upwards [hMiddle] with x hMidx

  have hSplit :=
    fourierInv_h3SpectralScalarRawFourierCoordinateDerivative_eq_selected_low_middle_high
      hNS ht hFourier A j i
      ((WithLp.toLp 2 :
        Point3 → H3FourierPoint3) x)

  rw [hMidx] at hSplit

  change
    FourierTransformInv.fourierInv
        (h3SpectralScalarRawFourierCoordinateDerivative
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j)
          i)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x)
      =
    h3BKMSelectedGradientModel
      hFourier A j i x

  simpa [h3BKMSelectedGradientModel] using hSplit

/-! ## Real physical derivative bridge -/

/--
The intrinsic spatial derivative of the arbitrary-H³ real representative is
almost everywhere the real part of the complete selected BKM gradient model.
-/
theorem spatialDerivative_h3SpectralScalarRealC1RepresentativeOnPoint3_ae_eq_selectedGradientModel_re
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    {g : ℝ → ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (A : ℝ)
    (j i : Fin 3) :
    (fun x : Point3 =>
      spatial3.d
        (h3AxisOfFin3 i)
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (velocityH3SpectralScalarAt
            u t hInt hMeas hFourier j))
        x)
      =ᵐ[(volume : Measure Point3)]
    fun x : Point3 =>
      (h3BKMSelectedGradientModel
        hFourier A j i x).re := by

  have hModel :=
    fourierInv_h3SpectralScalarRawFourierCoordinateDerivative_toLp_ae_eq_selectedGradientModel
      hNS ht hFourier hEnvelope A j i

  filter_upwards [hModel] with x hx

  rw [
    h3SpectralScalarRealC1RepresentativeOnPoint3_spatialDerivative_fin
  ]

  exact congrArg Complex.re hx

end

end Euclidean
end Bridge
end PrimeTensor
