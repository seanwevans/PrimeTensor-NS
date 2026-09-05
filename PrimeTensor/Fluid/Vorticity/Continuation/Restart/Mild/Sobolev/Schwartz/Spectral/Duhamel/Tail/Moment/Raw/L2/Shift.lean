import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.SelectedSecond
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Integral.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Weighted.Convolution.Pointwise
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Topology.CompactOpen

/-!
# Raw H³ Fourier `L²` deweighting and reflected-shift continuity

For the selected terminal-tail Fubini argument we need joint measurability in
output frequency and source time. The nonlinear kernel is built from raw
Fourier convolutions

    ∫ η, f̂(η) ĝ(ξ - η) dη.

The correct topology for this expression is `L² × L²`, not pointwise
evaluation of an `Lp` representative.

This file packages two reusable facts:

* deweighting a weighted H³ spectral state to its raw Fourier `L²` state is a
  contractive complex continuous linear map;
* the reflected translate `ĝ(ξ - ·)` varies continuously jointly in the
  weighted H³ state `G` and output frequency `ξ`.

The next checkpoint can identify the raw scalar convolution with one complex
`L²` inner product and obtain joint continuity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzTailRawL2Shift
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact H³ deweighting, bundled as a complex linear map into Fourier `L²`. -/
noncomputable def h3SpectralScalarRawFourierL2LinearMap :
    H3SpectralScalarState →ₗ[ℂ] H3FourierComplexL2 where
  toFun := h3SpectralScalarRawFourierL2
  map_add' := h3SpectralScalarRawFourierL2_add
  map_smul' := h3SpectralScalarRawFourierL2_smul_complex

/-- Exact H³ deweighting as a contractive complex continuous linear map. -/
noncomputable def h3SpectralScalarRawFourierL2CLM :
    H3SpectralScalarState →L[ℂ] H3FourierComplexL2 :=
  h3SpectralScalarRawFourierL2LinearMap.mkContinuous
    1
    (fun G => by
      change ‖h3SpectralScalarRawFourierL2 G‖ ≤ 1 * ‖G‖
      simpa using norm_h3SpectralScalarRawFourierL2_le G)

@[simp]
theorem h3SpectralScalarRawFourierL2CLM_apply
    (G : H3SpectralScalarState) :
    h3SpectralScalarRawFourierL2CLM G
      =
    h3SpectralScalarRawFourierL2 G :=
  rfl

/-- The reflected-translation family `ξ ↦ (η ↦ ξ - η)` as a continuous map
into the compact-open function space. -/
noncomputable def h3FourierSubLeftContinuousMapFamily :
    C(H3FourierPoint3, C(H3FourierPoint3, H3FourierPoint3)) :=
  ContinuousMap.curry
    ⟨(fun p : H3FourierPoint3 × H3FourierPoint3 => p.1 - p.2),
      continuous_fst.sub continuous_snd⟩

@[simp]
theorem h3FourierSubLeftContinuousMapFamily_apply
    (ξ η : H3FourierPoint3) :
    h3FourierSubLeftContinuousMapFamily ξ η = ξ - η :=
  rfl

/-- Every member of the reflected-translation family preserves Fourier
volume. -/
theorem h3FourierSubLeftContinuousMapFamily_measurePreserving
    (ξ : H3FourierPoint3) :
    MeasurePreserving
      (h3FourierSubLeftContinuousMapFamily ξ)
      (volume : Measure H3FourierPoint3)
      (volume : Measure H3FourierPoint3) := by
  change
    MeasurePreserving
      (fun η : H3FourierPoint3 => ξ - η)
      (volume : Measure H3FourierPoint3)
      (volume : Measure H3FourierPoint3)
  exact h3MeasurePreserving_sub_left ξ

/-- Raw Fourier `L²` state after reflected translation by output frequency
`ξ`. -/
noncomputable def h3SpectralScalarRawFourierReflectedShiftL2
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    H3FourierComplexL2 :=
  MeasureTheory.Lp.compMeasurePreserving
    (h3FourierSubLeftContinuousMapFamily ξ)
    (h3FourierSubLeftContinuousMapFamily_measurePreserving ξ)
    (h3SpectralScalarRawFourierL2 G)

/-- The reflected raw `L²` state has the expected representative almost
everywhere. -/
theorem h3SpectralScalarRawFourierReflectedShiftL2_ae
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    (h3SpectralScalarRawFourierReflectedShiftL2 G ξ :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun η : H3FourierPoint3 =>
      h3SpectralScalarRawFourier G (ξ - η)) := by
  unfold h3SpectralScalarRawFourierReflectedShiftL2

  have hComp :=
    MeasureTheory.Lp.coeFn_compMeasurePreserving
      (h3SpectralScalarRawFourierL2 G)
      (h3FourierSubLeftContinuousMapFamily_measurePreserving ξ)

  have hRaw :=
    h3SpectralScalarRawFourierL2_ae G

  have hShift :=
    hRaw.comp_tendsto
      (quasiMeasurePreserving_sub_left_of_right_invariant
        (volume : Measure H3FourierPoint3) ξ).tendsto_ae

  filter_upwards [hComp, hShift] with η hCompη hShiftη
  rw [hCompη]
  simpa only [
    Function.comp_apply,
    h3FourierSubLeftContinuousMapFamily_apply
  ] using hShiftη

/-- Reflected translation of the raw Fourier `L²` state is jointly continuous
in the weighted H³ input state and output frequency. -/
theorem continuous_h3SpectralScalarRawFourierReflectedShiftL2 :
    Continuous
      (fun p : H3SpectralScalarState × H3FourierPoint3 =>
        h3SpectralScalarRawFourierReflectedShiftL2 p.1 p.2) := by
  let f :
      H3SpectralScalarState × H3FourierPoint3 →
        H3FourierComplexL2 :=
    fun p => h3SpectralScalarRawFourierL2CLM p.1

  let g :
      H3SpectralScalarState × H3FourierPoint3 →
        C(H3FourierPoint3, H3FourierPoint3) :=
    fun p => h3FourierSubLeftContinuousMapFamily p.2

  have hf : Continuous f := by
    dsimp only [f]
    exact
      h3SpectralScalarRawFourierL2CLM.continuous.comp
        continuous_fst

  have hg : Continuous g := by
    dsimp only [g]
    exact
      h3FourierSubLeftContinuousMapFamily.continuous.comp
        continuous_snd

  have hgm :
      ∀ p : H3SpectralScalarState × H3FourierPoint3,
        MeasurePreserving
          (g p)
          (volume : Measure H3FourierPoint3)
          (volume : Measure H3FourierPoint3) := by
    intro p
    dsimp only [g]
    exact
      h3FourierSubLeftContinuousMapFamily_measurePreserving p.2

  have h :=
    hf.compMeasurePreservingLp
      hg
      hgm
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)

  simpa only [
    f,
    g,
    h3SpectralScalarRawFourierL2CLM_apply,
    h3SpectralScalarRawFourierReflectedShiftL2
  ] using h

end
end Euclidean
end Bridge
end PrimeTensor
