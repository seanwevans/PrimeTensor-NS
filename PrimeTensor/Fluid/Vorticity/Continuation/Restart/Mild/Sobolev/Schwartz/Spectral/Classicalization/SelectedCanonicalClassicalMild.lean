import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedCanonicalC1Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedPointwiseMild

/-!
# Classicalization: identify the canonical reconstruction with the classical mild formula

The selected canonical raw Fourier amplitude has now been transported through
ordinary inverse Fourier reconstruction and identified exactly with the generic
H³ `C¹` representative of the actual selected restart state.

The older selected classicalization stack already proves that the same generic
`C¹` representative is the literal pointwise heat-minus-Duhamel formula.  Its
selected path is written with the historical long physical-extension name,
while the new variation-of-constants route introduced a shorter modern name
directly from the canonical restart-radius path.

These two paths are definitionally the same object.  We record that fact
explicitly, then splice the two reconstruction routes together.

The resulting theorem says that the inverse Fourier transform of the explicit
canonical raw amplitude is literally

    heat C³ representative - classical Duhamel C³ representative

at every spatial point and every strict positive time in the restart interval.

Thus the new quotient-safe Fourier route and the pre-existing classical
physical-space route meet at an exact pointwise identity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalClassicalMild
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The modern short canonical physical-extension name and the historical
selected physical-extension name are definitionally the same path. -/
theorem h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_eq_mildSolutionAtRestartRadiusPhysicalExtension
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
      =
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀ := by
  unfold h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
  unfold h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
  unfold h3SpectralFinHeatLerayMildSolutionPhysicalExtension
  unfold h3SpectralFinHeatLerayMildSolutionAtRestartRadius
  rfl

/-- At every strict positive restart time, the inverse Fourier reconstruction
of the explicit canonical raw amplitude is exactly the classical
heat-minus-Duhamel `C¹` mild representative. -/
theorem h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative_mild_at
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
        hν U₀ hA hU₀ t i
      =
    h3SpectralScalarHeatC3Representative
        ν t (U₀ i)
      -
    h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t W W i := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let Wold : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hBridge :
      W = Wold := by
    dsimp only [W, Wold]
    exact
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_eq_mildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hCanonical :
      h3SpectralScalarC1Representative (W t i)
        =
      h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
        hν U₀ hA hU₀ t i := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_C1Representative_eq_canonical
        hν U₀ hA hU₀ ht htR i

  have hMild :
      h3SpectralScalarC1Representative (Wold t i)
        =
      h3SpectralScalarHeatC3Representative
          ν t (U₀ i)
        -
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t Wold Wold i := by
    dsimp only [Wold]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_mild_at
        hν U₀ hA hU₀ ht htR i

  rw [hBridge] at hCanonical

  change
    h3SpectralFinHeatLerayRestartRadiusCanonicalC1Representative
        hν U₀ hA hU₀ t i
      =
    h3SpectralScalarHeatC3Representative
        ν t (U₀ i)
      -
    h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t W W i

  rw [hBridge]

  exact hCanonical.symm.trans hMild

end

end Euclidean
end Bridge
end PrimeTensor
