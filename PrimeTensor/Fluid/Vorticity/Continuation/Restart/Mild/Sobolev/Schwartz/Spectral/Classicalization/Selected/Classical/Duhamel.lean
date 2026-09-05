import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.FullPointwise
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Selected.Physical.L2.Vector.Representative

/-!
# Classical selected Duhamel field

`FullPointwise` identifies the canonical selected-Duhamel `C¹` reconstruction
with the literal classical retarded Duhamel integral at every spatial point,
provided the target time lies inside the canonical restart radius.

The physical `L²` stack had already identified that same selected `C¹`
reconstruction almost everywhere with the source-time Bochner integral of the
endpoint-safe physical heat--Leray forcing.

This file joins those two interfaces.

First, the literal classical retarded Duhamel integral is shown to be an
almost-everywhere representative of the physical `L²` Duhamel coordinate.
Then the three coordinates are packaged into one `Fin 3`-valued classical
field and the same compatibility is proved simultaneously.

No new estimate, Fourier interchange, or point evaluation of an `L²`
equivalence class is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedClassicalDuhamel
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Inside the canonical restart radius, the literal classical retarded
Duhamel integral is an a.e. representative of the endpoint-safe physical `L²`
Duhamel Bochner integral. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selected_ae_eq_physicalL2Duhamel
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t W W i
      =ᵐ[(volume : Measure H3FourierPoint3)]
    ((h3RawFinLerayOuterProductDivergenceHeatPhysicalL2Duhamel
        ν t hν W W i : H3ComplexPhysicalScalarL2) :
      H3FourierPoint3 → ℂ) := by
  have hPoint :=
    h3SelectedDuhamelC1Representative_eq_C3Duhamel
      hν U₀ hA hU₀ ht htR i

  have hPhysical :=
    h3SelectedDuhamelC1Representative_ae_eq_physicalL2Duhamel_closed
      hν U₀ hA hU₀ ht i

  dsimp only at hPoint hPhysical ⊢

  filter_upwards [hPhysical] with x hx

  exact (congrFun hPoint x).symm.trans hx

/-- The three literal classical selected Duhamel coordinates, packaged as one
pointwise complex `Fin 3` vector. -/
noncomputable def h3SelectedClassicalDuhamelFinVectorRepresentative
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    H3FourierPoint3 → (Fin 3 → ℂ) :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  fun x i =>
    h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
      ν t W W i x

/-- Inside the restart radius, the previously packaged canonical selected
Duhamel `C¹` vector is pointwise identical to the literal classical Duhamel
vector. -/
theorem h3SelectedDuhamelC1FinVectorRepresentative_eq_classicalDuhamel
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    h3SelectedDuhamelC1FinVectorRepresentative
        ν A t hν U₀ hA hU₀ ht
      =
    h3SelectedClassicalDuhamelFinVectorRepresentative
      ν A t hν U₀ hA hU₀ := by
  funext x i

  unfold h3SelectedDuhamelC1FinVectorRepresentative
  unfold h3SelectedClassicalDuhamelFinVectorRepresentative

  exact
    congrFun
      (h3SelectedDuhamelC1Representative_eq_C3Duhamel
        hν U₀ hA hU₀ ht htR i)
      x

/-- For the canonical selected path, all three literal classical Duhamel
coordinates simultaneously represent their physical `L²` Bochner integrals
almost everywhere in space. -/
theorem h3SelectedClassicalDuhamelFinVectorRepresentative_ae_eq_physicalL2Duhamel
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3SelectedClassicalDuhamelFinVectorRepresentative
        ν A t hν U₀ hA hU₀
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun x i =>
      ((h3RawFinLerayOuterProductDivergenceHeatPhysicalL2Duhamel
          ν t hν W W i : H3ComplexPhysicalScalarL2) :
        H3FourierPoint3 → ℂ) x) := by
  have h0 :=
    h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selected_ae_eq_physicalL2Duhamel
      hν U₀ hA hU₀ ht htR (0 : Fin 3)

  have h1 :=
    h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selected_ae_eq_physicalL2Duhamel
      hν U₀ hA hU₀ ht htR (1 : Fin 3)

  have h2 :=
    h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_selected_ae_eq_physicalL2Duhamel
      hν U₀ hA hU₀ ht htR (2 : Fin 3)

  dsimp only at h0 h1 h2 ⊢
  unfold h3SelectedClassicalDuhamelFinVectorRepresentative
  dsimp only

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
