import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.MildSecond

/-!
# Canonical raw Fourier second moment of the selected positive-time mild state

`MildSecond` proves the second raw Fourier moment on the quotient-safe `L²`
package obtained by coordinate projection and exact H³ deweighting.

The nonlinear forcing layer, however, is written in terms of the canonical
pointwise representative

    h3SpectralScalarRawFourier (W t i).

This file closes that representation gap.  The standard
`h3SpectralScalarRawFourierL2_ae` theorem identifies the canonical raw
representative almost everywhere with the named deweighted `L²` class.
Therefore the selected positive-time state inherits the same second-moment
integrability in exactly the pointwise form consumed by
`h3RawProductConvolution`.

No new estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedMildRawSecond
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The named selected mild-state raw Fourier `L²` package is exactly the
canonical scalar deweighting package of the selected coordinate. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_eq_scalarRawFourierL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
        hν U₀ hA hU₀ t i
      =
    h3SpectralScalarRawFourierL2
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ t i) := by
  unfold h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
  exact h3SpectralFinCoordinateRawFourierL2CLM_apply i
    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀ t)

/-- The canonical raw Fourier representative of one selected positive-time
coordinate agrees almost everywhere with the coercion of the named raw
Fourier `L²` state. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_rawFourier
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    ((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
        hν U₀ hA hU₀ t i : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SpectralScalarRawFourier
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ t i) := by
  rw [
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_eq_scalarRawFourierL2
      hν U₀ hA hU₀ i
  ]
  exact
    h3SpectralScalarRawFourierL2_ae
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ t i)

/-- The weighted second-moment density of the canonical raw Fourier
representative agrees almost everywhere with the density of the named selected
raw Fourier `L²` package. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_secondMoment_ae_eq_rawFourierL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    (fun ξ : H3FourierPoint3 =>
      ‖ξ‖ ^ 2 *
        ‖h3SpectralScalarRawFourier
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ t i) ξ‖)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ‖ξ‖ ^ 2 *
        ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
            hν U₀ hA hU₀ t i : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ‖) := by
  have hRep :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_rawFourier
      (t := t)
      hν U₀ hA hU₀ i

  filter_upwards [hRep] with ξ hξ
  rw [hξ]

/-- Every selected positive-time coordinate has an integrable second moment in
the canonical raw Fourier representative used by the nonlinear forcing layer. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_secondMoment_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarRawFourier
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ t i) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hNamed :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_secondMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hEq :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_secondMoment_ae_eq_rawFourierL2
      (t := t)
      hν U₀ hA hU₀ i

  exact hNamed.congr hEq.symm

end
end Euclidean
end Bridge
end PrimeTensor
