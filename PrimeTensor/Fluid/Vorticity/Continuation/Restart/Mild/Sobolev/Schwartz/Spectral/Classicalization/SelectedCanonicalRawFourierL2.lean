import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedCanonicalRawFourierRepresentative

/-!
# Classicalization: package the selected canonical raw Fourier representative in L²

The selected restart state now has an explicit raw Fourier representative,

    heat raw representative - Duhamel raw amplitude,

identified almost everywhere with the ordinary deweighted Fourier
representative of the actual Banach-valued state.

This file turns that representative statement back into an exact quotient-safe
`L²` identity.

First, the canonical explicit amplitude inherits `L²` membership from the
ordinary raw representative.  We then package it with `MemLp.toLp` and prove
that this package is exactly `h3SpectralScalarRawFourierL2` of the selected
state.

The result is a useful normalization boundary for the next reconstruction
step: subsequent inverse-Fourier arguments can use the explicit canonical
amplitude while retaining exact equality with the actual selected `L²` state.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalRawFourierL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The explicit canonical selected raw Fourier amplitude belongs to Fourier
`L²` at every strict positive time in the restart interval. -/
theorem h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    MemLp
      (h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier
        hν U₀ hA hU₀ t i)
      2
      (volume : Measure H3FourierPoint3) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hRaw :
      MemLp
        (h3SpectralScalarRawFourier (W t i))
        2
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarRawFourier_memLp2 (W t i)

  have hEq :
      h3SpectralScalarRawFourier (W t i)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier
        hν U₀ hA hU₀ t i := by
    simpa only [W] using
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_rawFourier_ae_eq_canonical
        hν U₀ hA hU₀ ht htR i

  exact MeasureTheory.MemLp.ae_eq hEq hRaw

/-- Canonical Fourier-`L²` package of the explicit selected raw Fourier
amplitude. -/
noncomputable def h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourierL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  (h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier_memLp2
    hν U₀ hA hU₀ ht htR i).toLp
      (h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier
        hν U₀ hA hU₀ t i)

/-- The packaged canonical selected amplitude has its defining explicit
representative almost everywhere. -/
theorem h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourierL2_ae
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourierL2
        hν U₀ hA hU₀ ht htR i :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier
      hν U₀ hA hU₀ t i := by
  exact
    MemLp.coeFn_toLp
      (h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier_memLp2
        hν U₀ hA hU₀ ht htR i)

/-- The canonical explicit raw Fourier package is exactly the ordinary
deweighted Fourier `L²` state of the selected restart solution. -/
theorem h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourierL2_eq_rawFourierL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourierL2
        hν U₀ hA hU₀ ht htR i
      =
    h3SpectralScalarRawFourierL2
      ((h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hν U₀ hA hU₀) t i) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hCanonical :=
    h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourierL2_ae
      hν U₀ hA hU₀ ht htR i

  have hRaw :=
    h3SpectralScalarRawFourierL2_ae (W t i)

  have hEq :
      h3SpectralScalarRawFourier (W t i)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier
        hν U₀ hA hU₀ t i := by
    simpa only [W] using
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_rawFourier_ae_eq_canonical
        hν U₀ hA hU₀ ht htR i

  apply MeasureTheory.Lp.ext

  filter_upwards [
    hCanonical,
    hRaw,
    hEq
  ] with ξ hCanonicalξ hRawξ hEqξ

  rw [hCanonicalξ, hRawξ]
  exact hEqξ.symm

end

end Euclidean
end Bridge
end PrimeTensor
