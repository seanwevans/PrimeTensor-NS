import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.RawL2Shift
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Joint continuity of the genuine raw H³ Fourier convolution

The terminal-tail Fubini step needs joint measurability of the variable-state
nonlinear Fourier kernel.  The previous file put the reflected translate

    (G, ξ) ↦ [η ↦ ĝ(ξ - η)]

in the correct `L²` topology.

This file closes the scalar convolution topology.  Complex `L²` uses the
Mathlib convention

    ⟪f, g⟫ = ∫ η, g(η) * conj (f(η)).

Therefore, after conjugating the first raw `L²` state,

    ∫ η, f̂(η) * ĝ(ξ - η)
      =
    ⟪conj f̂, ĝ(ξ - ·)⟫.

Both Hilbert-space inputs vary continuously, so the genuine raw convolution is
jointly continuous in both weighted H³ inputs and the output frequency.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzTailRawConvolutionContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Raw Fourier `L²` state with pointwise complex conjugation. -/
noncomputable def h3SpectralScalarRawFourierConjL2
    (G : H3SpectralScalarState) :
    H3FourierComplexL2 :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLp
    (h3SpectralScalarRawFourierL2 G)

/-- The conjugated raw `L²` state has the expected representative almost
everywhere. -/
theorem h3SpectralScalarRawFourierConjL2_ae
    (G : H3SpectralScalarState) :
    (h3SpectralScalarRawFourierConjL2 G :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun η : H3FourierPoint3 =>
      (Complex.conjCLE : ℂ →L[ℝ] ℂ)
        (h3SpectralScalarRawFourier G η)) := by
  unfold h3SpectralScalarRawFourierConjL2

  have hConj :=
    ContinuousLinearMap.coeFn_compLp
      (Complex.conjCLE : ℂ →L[ℝ] ℂ)
      (h3SpectralScalarRawFourierL2 G)

  have hRaw :=
    h3SpectralScalarRawFourierL2_ae G

  filter_upwards [hConj, hRaw] with η hConjη hRawη

  rw [hConjη, hRawη]

/-- Conjugated raw Fourier `L²` deweighting is continuous in the weighted H³
state. -/
theorem continuous_h3SpectralScalarRawFourierConjL2 :
    Continuous
      (fun G : H3SpectralScalarState =>
        h3SpectralScalarRawFourierConjL2 G) := by
  have hConj :
      Continuous
        (fun f : H3FourierComplexL2 =>
          (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLp f) := by
    exact
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL
        (2 : ℝ≥0∞)
        (volume : Measure H3FourierPoint3)).continuous

  exact
    hConj.comp
      h3SpectralScalarRawFourierL2CLM.continuous

/-- The genuine scalar raw convolution is exactly one complex `L²` inner
product: conjugate the first raw state and pair it with the reflected translate
of the second. -/
theorem h3RawProductConvolution_eq_inner_conjRaw_shift
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3RawProductConvolution F G ξ
      =
    inner ℂ
      (h3SpectralScalarRawFourierConjL2 F)
      (h3SpectralScalarRawFourierReflectedShiftL2 G ξ) := by
  rw [MeasureTheory.L2.inner_def]

  unfold h3RawProductConvolution

  apply integral_congr_ae

  filter_upwards [
    h3SpectralScalarRawFourierConjL2_ae F,
    h3SpectralScalarRawFourierReflectedShiftL2_ae G ξ
  ] with η hF hG

  rw [hF, hG]
  simp [RCLike.inner_apply, Complex.conjCLE_apply, mul_comm]

/-- The genuine raw scalar Fourier convolution is jointly continuous in both
weighted H³ input states and the output frequency. -/
theorem continuous_h3RawProductConvolution :
    Continuous
      (fun p :
          H3SpectralScalarState ×
            (H3SpectralScalarState × H3FourierPoint3) =>
        h3RawProductConvolution
          p.1
          p.2.1
          p.2.2) := by
  have hLeft :
      Continuous
        (fun p :
            H3SpectralScalarState ×
              (H3SpectralScalarState × H3FourierPoint3) =>
          h3SpectralScalarRawFourierConjL2 p.1) :=
    continuous_h3SpectralScalarRawFourierConjL2.comp
      continuous_fst

  have hRight :
      Continuous
        (fun p :
            H3SpectralScalarState ×
              (H3SpectralScalarState × H3FourierPoint3) =>
          h3SpectralScalarRawFourierReflectedShiftL2
            p.2.1
            p.2.2) :=
    continuous_h3SpectralScalarRawFourierReflectedShiftL2.comp
      continuous_snd

  have hInner :
      Continuous
        (fun p :
            H3SpectralScalarState ×
              (H3SpectralScalarState × H3FourierPoint3) =>
          inner ℂ
            (h3SpectralScalarRawFourierConjL2 p.1)
            (h3SpectralScalarRawFourierReflectedShiftL2
              p.2.1
              p.2.2)) :=
    hLeft.inner hRight

  simpa only [
    h3RawProductConvolution_eq_inner_conjRaw_shift
  ] using hInner

end
end Euclidean
end Bridge
end PrimeTensor
