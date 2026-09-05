import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Selected.Physical.L2.Closure

/-!
# Simultaneous selected physical L² Duhamel representative

`SelectedPhysicalL2Closure` closes the physical `L²` representative theorem one
spectral coordinate at a time.

The physical velocity reconstruction is three-component, so downstream
classicalization should not have to reopen that scalar argument separately for
each `Fin 3` coordinate.  This file packages the three closed coordinate
statements into a single almost-everywhere equality of `Fin 3 → ℂ` valued
functions.

No new estimate, integration argument, Fourier interchange, or quotient
evaluation is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralDuhamelTailSelectedPhysicalL2VectorRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The three canonical selected Duhamel `C¹` representatives, packaged as one
pointwise complex `Fin 3` vector. -/
noncomputable def h3SelectedDuhamelC1FinVectorRepresentative
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t) :
    H3FourierPoint3 → (Fin 3 → ℂ) :=
  fun x i =>
    h3SelectedDuhamelC1Representative
      ν A t hν U₀ hA hU₀ ht i x

/-- For the canonical restart-radius selected path, all three pointwise
selected Duhamel coordinates simultaneously represent their source-time
physical `L²` Bochner integrals almost everywhere in space. -/
theorem h3SelectedDuhamelC1FinVectorRepresentative_ae_eq_physicalL2Duhamel
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3SelectedDuhamelC1FinVectorRepresentative
        ν A t hν U₀ hA hU₀ ht
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun x i =>
      ((h3RawFinLerayOuterProductDivergenceHeatPhysicalL2Duhamel
          ν t hν W W i : H3ComplexPhysicalScalarL2) :
        H3FourierPoint3 → ℂ) x) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have h0 :=
    h3SelectedDuhamelC1Representative_ae_eq_physicalL2Duhamel_closed
      hν U₀ hA hU₀ ht (0 : Fin 3)
  have h1 :=
    h3SelectedDuhamelC1Representative_ae_eq_physicalL2Duhamel_closed
      hν U₀ hA hU₀ ht (1 : Fin 3)
  have h2 :=
    h3SelectedDuhamelC1Representative_ae_eq_physicalL2Duhamel_closed
      hν U₀ hA hU₀ ht (2 : Fin 3)

  dsimp only at h0 h1 h2 ⊢
  unfold h3SelectedDuhamelC1FinVectorRepresentative

  filter_upwards [h0, h1, h2] with x hx0 hx1 hx2

  funext i
  fin_cases i
  · exact hx0
  · exact hx1
  · exact hx2

end

end Euclidean
end Bridge
end PrimeTensor
