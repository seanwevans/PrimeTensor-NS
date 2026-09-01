import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.SelectedC1Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.PhysicalL2Integral

/-!
# Selected pointwise Duhamel reconstruction as the physical L² integral

The full selected Duhamel coordinate now has two quotient-safe physical
realizations:

* `SelectedC1Representative` gives the canonical pointwise spatial `C¹`
  representative of the actual selected spectral Duhamel coordinate; and
* `PhysicalL2Integral` gives the source-time Bochner integral of the
  endpoint-safe physical `L²` retarded forcing, exactly equal to the decoder
  of that same spectral coordinate.

This file simply joins those two identities.  Under the existing explicit
Bochner interval-integrability premise, the selected pointwise reconstruction
is therefore an almost-everywhere representative of the integrated physical
`L²` Duhamel object itself.

No new estimate, Fourier interchange, or point evaluation of an `L²` class is
used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralDuhamelTailSelectedPhysicalL2Representative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical pointwise selected Duhamel reconstruction is an a.e.
representative of the source-time-integrated physical `L²` Duhamel
coordinate. -/
theorem h3SelectedDuhamelC1Representative_ae_eq_physicalL2Duhamel
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hInt :
      let W : ℝ → H3SpectralFinVectorState :=
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν W W)
        volume
        0
        t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3SelectedDuhamelC1Representative
        ν A t hν U₀ hA hU₀ ht i
      =ᵐ[(volume : Measure H3FourierPoint3)]
    ((h3RawFinLerayOuterProductDivergenceHeatPhysicalL2Duhamel
        ν t hν W W i : H3ComplexPhysicalScalarL2) :
      H3FourierPoint3 → ℂ) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hRep :=
    h3SelectedDuhamelC1Representative_ae_eq_decodeComplexL2
      hν U₀ hA hU₀ ht i

  have hPhysical :
      h3RawFinLerayOuterProductDivergenceHeatPhysicalL2Duhamel
          ν t hν W W i
        =
      h3SpectralScalarDecodeComplexL2
        ((h3SpectralFinHeatLerayDuhamel ν t hν W W) i) :=
    h3RawFinLerayOuterProductDivergenceHeatPhysicalL2Duhamel_eq_decodeComplexL2
      hν W W hInt i

  dsimp only at hRep ⊢

  have hPhysicalFun :
      (((h3SpectralScalarDecodeComplexL2
          ((h3SpectralFinHeatLerayDuhamel ν t hν W W) i) :
        H3ComplexPhysicalScalarL2) :
        H3FourierPoint3 → ℂ))
        =
      (((h3RawFinLerayOuterProductDivergenceHeatPhysicalL2Duhamel
          ν t hν W W i : H3ComplexPhysicalScalarL2) :
        H3FourierPoint3 → ℂ)) := by
    exact
      congrArg
        (fun Z : H3ComplexPhysicalScalarL2 =>
          ((Z : H3ComplexPhysicalScalarL2) :
            H3FourierPoint3 → ℂ))
        hPhysical.symm

  filter_upwards [hRep] with x hx
  rw [hx]
  exact congrFun hPhysicalFun x

end

end Euclidean
end Bridge
end PrimeTensor
