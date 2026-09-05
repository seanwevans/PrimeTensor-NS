import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.Diagonal.Right.Candidate
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Reconstruction.L2.Bridge

/-!
# Selected Duhamel old-history heat / canonical C¹ bridge

The diagonal right-quotient candidate is already assembled.  Its old-history
term is intentionally written using the explicit inverse-Fourier heat orbit of
the complete selected Duhamel raw amplitude.

The physical Duhamel cocycle, on the other hand, advances the spectral
Duhamel state by the H³ heat semigroup.  This file identifies those two
descriptions pointwise.

For the selected Duhamel coordinate `D(t)` and every elapsed heat time `h`,

    oldHistoryHeat(h)
      = F⁻¹[m_h · raw(D(t))].

At strictly positive `h`, the explicit heat raw amplitude is the same L²
deweighting representative as the actual spectral state `H_h D(t)`.  Hence

    oldHistoryHeat(h)
      = C1Representative (H_h D(t)).

The proof stays quotient-safe: both identifications are made at the raw
Fourier level almost everywhere, and only then transported through ordinary
inverse Fourier reconstruction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3DuhamelHistoryHeatC1Bridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The explicit selected old-history heat representative is exactly the
ordinary positive-lag heat reconstruction of the actual selected Duhamel
spectral coordinate.  This raw-level identity itself does not require the
elapsed heat time to be positive. -/
theorem h3SelectedDuhamelHistoryHeatRepresentative_eq_heatC3Representative
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let D : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel ν t hν W W i
    h3SelectedDuhamelHistoryHeatRepresentative
        ν A t h hν U₀ hA hU₀ ht i
      =
    h3SpectralScalarHeatC3Representative ν h D := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W i

  have hSelected0 :=
    h3SpectralScalarRawFourier_selectedDuhamel_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  have hSelected :
      h3SpectralScalarRawFourier D
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SelectedDuhamelRawFourierAmplitude
        ν A t hν U₀ hA hU₀ ht i := by
    simpa only [D, W] using hSelected0

  have hRaw :
      h3SelectedDuhamelHistoryHeatRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarHeatRawRepresentative ν h D := by
    filter_upwards [hSelected] with ξ hξ
    unfold h3SelectedDuhamelHistoryHeatRawAmplitude
    unfold h3SpectralScalarHeatRawRepresentative
    rw [← hξ]

  funext x
  unfold h3SelectedDuhamelHistoryHeatRepresentative
  unfold h3SpectralScalarHeatC3Representative
  exact _root_.Real.fourierInv_congr_ae hRaw x

/-- At positive elapsed heat time, the explicit old-history heat
reconstruction is the canonical H³ `C¹` representative of the actual
heat-evolved selected Duhamel spectral coordinate. -/
theorem h3SelectedDuhamelHistoryHeatRepresentative_eq_spectralScalarC1Representative_heatApplyNN
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let D : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel ν t hν W W i
    h3SelectedDuhamelHistoryHeatRepresentative
        ν A t h hν U₀ hA hU₀ ht i
      =
    h3SpectralScalarC1Representative
      (h3SpectralScalarHeatApplyNN
        ν hν.le (NNReal.mk h hh.le) D) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W i

  let H : H3SpectralScalarState :=
    h3SpectralScalarHeatApplyNN
      ν hν.le (NNReal.mk h hh.le) D

  have hOld :
      h3SelectedDuhamelHistoryHeatRepresentative
          ν A t h hν U₀ hA hU₀ ht i
        =
      h3SpectralScalarHeatC3Representative ν h D := by
    dsimp only [D, W]
    exact
      h3SelectedDuhamelHistoryHeatRepresentative_eq_heatC3Representative
        hν U₀ hA hU₀ ht i

  have hPkg :
      h3SpectralScalarHeatRawRepresentativeL2 ν h hν hh D
        =
      h3SpectralScalarRawFourierL2 H := by
    dsimp only [H]
    exact
      h3SpectralScalarHeatRawRepresentativeL2_eq_rawFourierL2_heatApplyNN
        hν hh D

  have hHeatAE :=
    h3SpectralScalarHeatRawRepresentativeL2_ae hν hh D

  rw [hPkg] at hHeatAE

  have hRawAE :
      ((h3SpectralScalarRawFourierL2 H : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourier H := by
    exact h3SpectralScalarRawFourierL2_ae H

  have hRaw :
      h3SpectralScalarHeatRawRepresentative ν h D
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourier H :=
    hHeatAE.symm.trans hRawAE

  have hHeatC1 :
      h3SpectralScalarHeatC3Representative ν h D
        =
      h3SpectralScalarC1Representative H := by
    funext x
    unfold h3SpectralScalarHeatC3Representative
    unfold h3SpectralScalarC1Representative
    exact _root_.Real.fourierInv_congr_ae hRaw x

  rw [hOld]
  simpa only [H] using hHeatC1

end

end Euclidean
end Bridge
end PrimeTensor
