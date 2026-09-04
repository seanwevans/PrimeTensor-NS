import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedCanonicalRawFourierL2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Bridge

/-!
# Classicalization: inverse-Fourier reconstruction of the selected canonical amplitude

The selected restart state now has an explicit canonical raw Fourier amplitude

    heat raw representative - Duhamel raw amplitude

which is known both

* almost everywhere to represent the ordinary raw Fourier function of the
  selected H³ state, and
* exactly, after `L²` packaging, to equal the selected state's deweighted
  Fourier `L²` class.

This file crosses from that canonical frequency-space object back to the
ordinary spatial inverse-Fourier representative.

First we record that the canonical amplitude also belongs to Fourier `L¹`.
That follows by transporting the existing H³ `L¹` deweighting theorem across
the established almost-everywhere representative equality.  Hence its ordinary
inverse Fourier integral is a genuine integrable reconstruction.

We then define that reconstruction and prove it is exactly the generic H³ `C¹`
representative of the actual selected restart state.  The proof is the
representative-safe one: Fourier a.e. equality is transported by
`Real.fourierInv_congr_ae`; no point evaluation of an `L²` class occurs.

Finally, the explicit canonical reconstruction inherits spatial `C¹`
regularity from the already-proved arbitrary-H³ reconstruction theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalC1Representative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected canonical raw Fourier amplitude is also in Fourier `L¹`. -/
theorem h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier_memLp1
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
      1
      (volume : Measure H3FourierPoint3) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hRaw :
      MemLp
        (h3SpectralScalarRawFourier (W t i))
        1
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarRawFourier_memLp1 (W t i)

  have hEq :
      h3SpectralScalarRawFourier (W t i)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier
        hν U₀ hA hU₀ t i := by
    simpa only [W] using
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_rawFourier_ae_eq_canonical
        hν U₀ hA hU₀ ht htR i

  exact MeasureTheory.MemLp.ae_eq hEq hRaw

/-- The selected canonical raw Fourier amplitude is integrable, so its ordinary
inverse Fourier reconstruction is not relying on totalized nonintegrable
behavior. -/
theorem h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier
        hν U₀ hA hU₀ t i)
      (volume : Measure H3FourierPoint3) := by
  exact
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier_memLp1
        hν U₀ hA hU₀ ht htR i)

/-- Ordinary inverse-Fourier reconstruction of the explicit canonical selected
raw Fourier amplitude. -/
noncomputable def h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (t : ℝ)
    (i : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SpectralFinHeatLerayRestartRadiusCanonicalRawFourier
      hν U₀ hA hU₀ t i)

/-- The arbitrary-H³ `C¹` representative of the actual selected restart state
is exactly the ordinary inverse-Fourier reconstruction of its explicit
canonical raw amplitude. -/
theorem h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_C1Representative_eq_canonical
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    h3SpectralScalarC1Representative
        ((h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
          hν U₀ hA hU₀) t i)
      =
    h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
      hν U₀ hA hU₀ t i := by
  funext x

  unfold h3SpectralScalarC1Representative
  unfold h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative

  exact
    _root_.Real.fourierInv_congr_ae
      (h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_rawFourier_ae_eq_canonical
        hν U₀ hA hU₀ ht htR i)
      x

/-- The explicit canonical inverse-Fourier reconstruction is spatially `C¹`. -/
theorem h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative_contDiff_one
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    ContDiff ℝ 1
      (h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
        hν U₀ hA hU₀ t i) := by
  have hEq :=
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_C1Representative_eq_canonical
      hν U₀ hA hU₀ ht htR i

  rw [← hEq]

  exact
    h3SpectralScalarC1Representative_contDiff_one
      ((h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hν U₀ hA hU₀) t i)

end

end Euclidean
end Bridge
end PrimeTensor
