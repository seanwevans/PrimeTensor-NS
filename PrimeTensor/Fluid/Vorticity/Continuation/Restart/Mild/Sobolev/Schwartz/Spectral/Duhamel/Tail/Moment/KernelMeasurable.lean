import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Raw.Convolution.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.SelectedSecond

/-!
# Joint measurability of the selected terminal-tail second-moment kernel

The scalar raw H³ convolution is now jointly continuous in both weighted H³
inputs and output frequency.  This file lifts that fact through the finite
outer-product divergence and then through the Fourier Leray multiplier.

The distinction between those two steps matters:

* the raw finite divergence is genuinely continuous in `(U,V,ξ)`;
* the finite Leray symbol has the usual exceptional zero-frequency point, so
  the complete raw Leray forcing is asserted only to be measurable.

The retarded heat multiplier is jointly continuous in source time and
frequency.  Composing with the continuous selected restart path therefore
makes the actual terminal-tail kernel jointly measurable on
`ℝ × H3FourierPoint3`.

Finally we package the nonnegative second-moment density

    ‖ξ‖² ‖H_{t-s}(ξ) P(ξ) div(W(s) ⊗ W(s))(ξ)‖.

This is the precise missing hypothesis for the next Tonelli/Fubini checkpoint.
No interchange of integrals is performed here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzTailKernelMeasurable
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The raw finite outer-product divergence is jointly continuous in both H³
velocity inputs and output frequency. -/
theorem continuous_h3RawFinOuterProductDivergence_joint
    (i : Fin 3) :
    Continuous
      (fun p :
          H3SpectralFinVectorState ×
            (H3SpectralFinVectorState × H3FourierPoint3) =>
        h3RawFinOuterProductDivergence
          p.1 p.2.1 i p.2.2) := by
  unfold h3RawFinOuterProductDivergence

  apply continuous_finsetSum
  intro j hj

  have hU :
      Continuous
        (fun p :
            H3SpectralFinVectorState ×
              (H3SpectralFinVectorState × H3FourierPoint3) =>
          p.1 i) := by
    exact
      (continuous_apply i).comp continuous_fst

  have hVbase :
      Continuous
        (fun p :
            H3SpectralFinVectorState ×
              (H3SpectralFinVectorState × H3FourierPoint3) =>
          p.2.1) := by
    exact continuous_fst.comp continuous_snd

  have hV :
      Continuous
        (fun p :
            H3SpectralFinVectorState ×
              (H3SpectralFinVectorState × H3FourierPoint3) =>
          p.2.1 j) := by
    exact
      (continuous_apply j).comp hVbase

  have hξ :
      Continuous
        (fun p :
            H3SpectralFinVectorState ×
              (H3SpectralFinVectorState × H3FourierPoint3) =>
          p.2.2) := by
    exact continuous_snd.comp continuous_snd

  have hInput :
      Continuous
        (fun p :
            H3SpectralFinVectorState ×
              (H3SpectralFinVectorState × H3FourierPoint3) =>
          (p.1 i, (p.2.1 j, p.2.2))) := by
    exact
      Continuous.prodMk hU
        (Continuous.prodMk hV hξ)

  have hConv :
      Continuous
        (fun p :
            H3SpectralFinVectorState ×
              (H3SpectralFinVectorState × H3FourierPoint3) =>
          h3RawProductConvolution
            (p.1 i) (p.2.1 j) p.2.2) := by
    exact
      continuous_h3RawProductConvolution.comp hInput

  have hDer :
      Continuous
        (fun p :
            H3SpectralFinVectorState ×
              (H3SpectralFinVectorState × H3FourierPoint3) =>
          h3FourierDerivativeSymbol j p.2.2) := by
    exact
      (h3FourierDerivativeSymbol_continuous j).comp hξ

  exact hDer.mul hConv

/-- The retarded scalar heat multiplier is jointly continuous in source time
and Fourier frequency. -/
theorem continuous_h3HeatFourierSymbol_retarded
    (ν t : ℝ) :
    Continuous
      (fun p : ℝ × H3FourierPoint3 =>
        h3HeatFourierSymbol ν (t - p.1) p.2) := by
  unfold h3HeatFourierSymbol
  fun_prop

/-- Along the canonical selected restart path, the complete raw Leray forcing
is jointly measurable in source time and Fourier frequency.

We deliberately prove measurability only after composing with the selected
path.  The H³ Banach state spaces in this development carry topology but no
global `MeasurableSpace` instance, so a theorem quantified over the full state
product would introduce an unnecessary measurable-space obligation. -/
theorem measurable_h3RawFinLerayOuterProductDivergence_selectedRestart_joint
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Measurable
      (fun p : ℝ × H3FourierPoint3 =>
        h3RawFinLerayOuterProductDivergence
          (W p.1) (W p.1) i p.2) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hWs :
      Continuous
        (fun p : ℝ × H3FourierPoint3 =>
          W p.1) :=
    hWcont.comp continuous_fst

  have hInput :
      Continuous
        (fun p : ℝ × H3FourierPoint3 =>
          (W p.1, (W p.1, p.2))) := by
    exact
      Continuous.prodMk hWs
        (Continuous.prodMk hWs continuous_snd)

  unfold h3RawFinLerayOuterProductDivergence

  apply Finset.measurable_sum
  intro k hk

  have hLeray :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3LerayCoefficient p.2 i k) := by
    exact
      (measurable_h3LerayCoefficient i k).comp measurable_snd

  have hDiv :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3RawFinOuterProductDivergence
            (W p.1) (W p.1) k p.2) := by
    exact
      ((continuous_h3RawFinOuterProductDivergence_joint k).comp
        hInput).measurable

  exact hLeray.mul hDiv

/-- The actual retarded selected heat--Leray forcing kernel is jointly
measurable in source time and Fourier frequency. -/
theorem measurable_h3RawFinLerayOuterProductDivergenceHeat_selectedRestart_joint
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Measurable
      (fun p : ℝ × H3FourierPoint3 =>
        h3HeatFourierSymbol ν (t - p.1) p.2 *
          h3RawFinLerayOuterProductDivergence
            (W p.1) (W p.1) i p.2) := by
  dsimp only

  have hHeat :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3HeatFourierSymbol ν (t - p.1) p.2) :=
    (continuous_h3HeatFourierSymbol_retarded ν t).measurable

  have hForcing :=
    measurable_h3RawFinLerayOuterProductDivergence_selectedRestart_joint
      hν U₀ hA hU₀ i

  exact hHeat.mul hForcing

/-- Nonnegative second-moment density of the actual selected retarded tail
kernel on the time--frequency product space. -/
noncomputable def h3SelectedDuhamelTailSecondMomentKernel
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (p : ℝ × H3FourierPoint3) : ℝ :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  ‖p.2‖ ^ 2 *
    ‖h3HeatFourierSymbol ν (t - p.1) p.2 *
      h3RawFinLerayOuterProductDivergence
        (W p.1) (W p.1) i p.2‖

/-- The selected terminal-tail second-moment density is jointly measurable. -/
theorem measurable_h3SelectedDuhamelTailSecondMomentKernel
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    Measurable
      (h3SelectedDuhamelTailSecondMomentKernel
        ν A t hν U₀ hA hU₀ i) := by
  unfold h3SelectedDuhamelTailSecondMomentKernel

  have hWeight :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          ‖p.2‖ ^ 2) := by
    exact
      ((continuous_norm.comp continuous_snd).pow 2).measurable

  have hKernel :=
    measurable_h3RawFinLerayOuterProductDivergenceHeat_selectedRestart_joint
      (t := t) hν U₀ hA hU₀ i

  exact hWeight.mul hKernel.norm

/-- Product-measure form required by Tonelli/Fubini in the next checkpoint. -/
theorem h3SelectedDuhamelTailSecondMomentKernel_aestronglyMeasurable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    AEStronglyMeasurable
      (h3SelectedDuhamelTailSecondMomentKernel
        ν A t hν U₀ hA hU₀ i)
      ((volume : Measure ℝ).prod
        (volume : Measure H3FourierPoint3)) :=
  (measurable_h3SelectedDuhamelTailSecondMomentKernel
    hν U₀ hA hU₀ i).aestronglyMeasurable

end
end Euclidean
end Bridge
end PrimeTensor
