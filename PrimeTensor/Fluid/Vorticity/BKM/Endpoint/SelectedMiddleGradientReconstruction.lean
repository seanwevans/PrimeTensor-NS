import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.SelectedMiddleGradientFourierAmplitude
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Reconstruction.Compatibility

/-!
# BKM endpoint: reconstruct the selected middle gradient

The selected middle Fourier amplitude is now known to be an ordinary
`L¹ ∩ L²` function, and by construction it is the chosen representative of
the unitary Fourier transform of the selected middle inverse `L²` state.

The generic `L¹ ∩ L²` compatibility theorem therefore identifies its ordinary
inverse Fourier transform almost everywhere with the unitary `L²` inverse
Fourier transform.  Unitarity collapses that inverse transform back to the
selected middle state itself.

After transporting from the Fourier carrier to `Point3`, the already-proved
physical representative theorem identifies that state almost everywhere with
the canonical selected physical middle-gradient proxy.

Thus the selected middle proxy is now represented by the ordinary inverse
Fourier transform of the selected middle Fourier amplitude, in exactly the
same language as the low and high pieces.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointSelectedMiddleGradientReconstruction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointSelectedMiddleGradientReconstruction :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Reconstruction on the Fourier carrier -/

/--
Ordinary inverse Fourier reconstruction of the selected middle amplitude agrees
almost everywhere with the selected middle inverse `L²` state.
-/
theorem fourierInv_h3BKMSelectedMiddleGradientFourierAmplitude_ae_eq_inverseL2
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    {hInt : VelocityH3IntegrableAt u t}
    {hMeas : VelocityH3MeasurableAt u t}
    (hFourier : VelocityH3FourierCompatibleAt u t hInt hMeas)
    (A : ℝ)
    (j i : Fin 3) :
    FourierTransformInv.fourierInv
        (h3BKMSelectedMiddleGradientFourierAmplitude
          hFourier A j i)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    ((h3BKMSelectedMiddleGradientInverseL2
        hFourier A j i :
        H3FourierComplexL2) :
      H3FourierPoint3 → ℂ) := by

  let S : H3FourierComplexL2 :=
    h3BKMSelectedMiddleGradientInverseL2
      hFourier A j i

  let FT :=
    MeasureTheory.Lp.fourierTransformₗᵢ
      H3FourierPoint3 ℂ

  let F : H3FourierComplexL2 :=
    FT S

  have hAmp :
      h3BKMSelectedMiddleGradientFourierAmplitude
          hFourier A j i
        =
      ((F : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) := by
    funext ξ
    rfl

  have hF1 :
      Integrable
        (((F : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ))
        (volume : Measure H3FourierPoint3) := by
    rw [← hAmp]
    exact
      h3BKMSelectedMiddleGradientFourierAmplitude_integrable
        hNS ht hFourier A j i

  have hF2 :
      MemLp
        (((F : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ))
        2
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.Lp.memLp F

  have hCompat :=
    h3FourierInv_integrable_memLp2_ae_eq_L2
      hF1 hF2

  have hToLp :
      hF2.toLp
          (((F : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ))
        =
      F := by
    apply MeasureTheory.Lp.ext
    exact hF2.coeFn_toLp

  rw [hToLp] at hCompat

  have hInv :
      FT.symm F = S := by
    dsimp only [F]
    exact FT.symm_apply_apply S

  change
    FourierTransformInv.fourierInv
        (((F : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ))
      =ᵐ[(volume : Measure H3FourierPoint3)]
    ((FT.symm F : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
    at hCompat

  rw [hInv] at hCompat
  rw [hAmp]
  simpa only [S] using hCompat

/-! ## Transport to the physical carrier -/

/--
On `Point3`, ordinary inverse Fourier reconstruction of the selected middle
amplitude agrees almost everywhere with the canonical selected physical
middle-gradient proxy.
-/
theorem fourierInv_h3BKMSelectedMiddleGradientFourierAmplitude_toLp_ae_eq_physical
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
        (h3BKMSelectedMiddleGradientFourierAmplitude
          hFourier A j i)
        ((WithLp.toLp 2 :
          Point3 → H3FourierPoint3) x))
      =ᵐ[(volume : Measure Point3)]
    h3BKMSelectedMiddleGradient
      u t A j i := by

  let S : H3FourierComplexL2 :=
    h3BKMSelectedMiddleGradientInverseL2
      hFourier A j i

  have hFourierCarrier :=
    fourierInv_h3BKMSelectedMiddleGradientFourierAmplitude_ae_eq_inverseL2
      hNS ht hFourier A j i

  have hPull :
      (fun x : Point3 =>
        FourierTransformInv.fourierInv
          (h3BKMSelectedMiddleGradientFourierAmplitude
            hFourier A j i)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      fun x : Point3 =>
        (S : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x) := by

    have hComp :=
      (PiLp.volume_preserving_toLp
        (PrimeTensor.Axis Depth.three)).quasiMeasurePreserving.ae_eq_comp
          hFourierCarrier

    change
      (fun x : Point3 =>
        FourierTransformInv.fourierInv
          (h3BKMSelectedMiddleGradientFourierAmplitude
            hFourier A j i)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      (fun x : Point3 =>
        (S : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x))
      at hComp

    exact hComp

  have hPhysical :=
    h3BKMSelectedMiddleGradientInverseL2_ae_eq
      hInt hMeas hFourier hEnvelope A j i

  have hPhysical' :
      (fun x : Point3 =>
        (S : H3FourierPoint3 → ℂ)
          ((WithLp.toLp 2 :
            Point3 → H3FourierPoint3) x))
        =ᵐ[(volume : Measure Point3)]
      h3BKMSelectedMiddleGradient
        u t A j i := by
    simpa only [S] using hPhysical

  exact hPull.trans hPhysical'

end

end Euclidean
end Bridge
end PrimeTensor
