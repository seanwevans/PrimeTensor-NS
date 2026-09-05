import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Selected.Raw.Fourier.Amplitude
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Bridge

/-!
# Pointwise C¹ reconstruction of the full selected Duhamel contribution

`SelectedRawFourierAmplitude` identifies an explicit full raw Fourier amplitude
almost everywhere with the actual deweighted selected Duhamel coordinate.

Every H³ spectral scalar state already has a canonical raw Fourier amplitude in
`L¹`, and the corresponding inverse Fourier integral is the canonical spatial
`C¹` representative.  This file transfers that generic H³ reconstruction to
the explicit selected Duhamel amplitude.

The key point is quotient safety:

* first identify the two Fourier amplitudes almost everywhere;
* inherit `L¹` integrability from the actual H³ state; and
* use `Real.fourierInv_congr_ae` to upgrade Fourier a.e. equality to pointwise
  equality of inverse Fourier reconstructions.

No point evaluation of an `L²` equivalence class is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralDuhamelTailSelectedC1Representative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The generic deweighted raw Fourier amplitude of the actual selected
Duhamel coordinate agrees almost everywhere with the explicit full amplitude. -/
theorem h3SpectralScalarRawFourier_selectedDuhamel_ae_eq_rawAmplitude
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3SpectralScalarRawFourier
        (h3SpectralFinHeatLerayDuhamel ν t hν W W i)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SelectedDuhamelRawFourierAmplitude
      ν A t hν U₀ hA hU₀ ht i := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let G : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W i

  have hRawL2 :
      ((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
          (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourier G := by
    have h :=
      h3SpectralScalarRawFourierL2_ae G
    dsimp only [G, W] at h
    unfold h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
    simpa only [
      h3SpectralFinCoordinateRawFourierL2CLM_apply
    ] using h

  have hExplicit :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  dsimp only [G] at hRawL2
  dsimp only [W]
  exact hRawL2.symm.trans hExplicit

/-- The explicit selected Duhamel raw Fourier amplitude is genuinely `L¹`. -/
theorem h3SelectedDuhamelRawFourierAmplitude_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelRawFourierAmplitude
        ν A t hν U₀ hA hU₀ ht i)
      (volume : Measure H3FourierPoint3) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let G : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W i

  have hRaw :
      Integrable
        (h3SpectralScalarRawFourier G)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)

  have hEq :=
    h3SpectralScalarRawFourier_selectedDuhamel_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  dsimp only [W, G] at hRaw
  simpa only [W] using hRaw.congr hEq

/-- Classical inverse-Fourier reconstruction of the explicit full selected
Duhamel raw amplitude. -/
noncomputable def h3SelectedDuhamelC1Representative
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SelectedDuhamelRawFourierAmplitude
      ν A t hν U₀ hA hU₀ ht i)

/-- The explicit selected-Duhamel inverse Fourier reconstruction is pointwise
identical to the canonical H³ `C¹` representative of the actual selected
spectral Duhamel coordinate. -/
theorem h3SelectedDuhamelC1Representative_eq_spectralScalarC1Representative
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3SelectedDuhamelC1Representative
        ν A t hν U₀ hA hU₀ ht i
      =
    h3SpectralScalarC1Representative
      (h3SpectralFinHeatLerayDuhamel ν t hν W W i) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hEq :=
    h3SpectralScalarRawFourier_selectedDuhamel_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  funext x
  unfold h3SelectedDuhamelC1Representative
  unfold h3SpectralScalarC1Representative
  exact (_root_.Real.fourierInv_congr_ae hEq x).symm

/-- The explicit selected Duhamel reconstruction is spatially `C¹`. -/
theorem h3SelectedDuhamelC1Representative_contDiff_one
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    ContDiff ℝ 1
      (h3SelectedDuhamelC1Representative
        ν A t hν U₀ hA hU₀ ht i) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  rw [
    h3SelectedDuhamelC1Representative_eq_spectralScalarC1Representative
      hν U₀ hA hU₀ ht i
  ]

  exact
    h3SpectralScalarC1Representative_contDiff_one
      (h3SpectralFinHeatLerayDuhamel ν t hν W W i)

/-- The explicit pointwise selected Duhamel reconstruction is an a.e.
representative of the actual complex physical `L²` decoder. -/
theorem h3SelectedDuhamelC1Representative_ae_eq_decodeComplexL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3SelectedDuhamelC1Representative
        ν A t hν U₀ hA hU₀ ht i
      =ᵐ[(volume : Measure H3FourierPoint3)]
    ((h3SpectralScalarDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamel ν t hν W W i) :
      H3ComplexPhysicalScalarL2) :
      H3FourierPoint3 → ℂ) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  rw [
    h3SelectedDuhamelC1Representative_eq_spectralScalarC1Representative
      hν U₀ hA hU₀ ht i
  ]

  exact
    h3SpectralScalarC1Representative_ae_eq_decodeComplexL2
      (h3SpectralFinHeatLerayDuhamel ν t hν W W i)

end

end Euclidean
end Bridge
end PrimeTensor
