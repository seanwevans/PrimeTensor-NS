import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdFrozenMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdVariationZeroEnvelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Amplitude

/-!
# Quantitative full selected third-moment terminal tail

The varying and frozen full-third terminal contributions are now both
quantitative on the same terminal half `(t/2,t)`.

This file recombines them into the actual selected weighted tail kernel

    |ξ|^3 H_{t-s}(ξ) N(W(s),W(s))(ξ).

The algebraic identity is

    full = variation + frozen.

No new endpoint estimate is introduced.  Product integrability is inherited by
addition, and the iterated norm integral is bounded by the sum of the already
closed variation and frozen budgets.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzThirdFullTailMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The actual selected terminal-half kernel after inserting the radial third
Fourier weight. -/
noncomputable def h3SelectedDuhamelTailThirdComplexKernel
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (p : ℝ × H3FourierPoint3) : ℂ :=
  ((‖p.2‖ ^ 3 : ℝ) : ℂ) *
    h3SelectedDuhamelTailComplexKernel
      ν A t hν U₀ hA hU₀ i p

/-- Complete selected full-third terminal-half budget. -/
noncomputable def h3SelectedDuhamelTailThirdFullBudget
    (ν A t : ℝ) : ℝ :=
  h3SelectedDuhamelTailThirdVariationUniformBudget ν A (t / 2) t +
    h3SelectedDuhamelTailThirdFrozenBudget ν A t

/-- The actual radial-third tail kernel is the sum of its varying and frozen
terminal pieces. -/
theorem h3SelectedDuhamelTailThirdComplexKernel_eq_variation_add_frozen
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    h3SelectedDuhamelTailThirdComplexKernel
        ν A t hν U₀ hA hU₀ i
      =
    (fun p : ℝ × H3FourierPoint3 =>
      h3SelectedDuhamelTailThirdVariationComplexKernel
          ν A t hν U₀ hA hU₀ i p
        +
      h3SelectedDuhamelTailThirdFrozenComplexKernel
          ν A t hν U₀ hA hU₀ i p) := by
  funext p
  unfold
    h3SelectedDuhamelTailThirdComplexKernel
    h3SelectedDuhamelTailThirdVariationComplexKernel
    h3SelectedDuhamelTailThirdFrozenComplexKernel
    h3SelectedDuhamelTailComplexKernel
  dsimp only
  ring

/-- The selected varying full-third kernel is genuinely integrable on the
terminal-half product measure, with all state envelopes discharged. -/
theorem h3SelectedDuhamelTailThirdVariationComplexKernel_halfTail_fubini_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailThirdVariationComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
        (volume : Measure H3FourierPoint3)) := by
  have hhalf0 : 0 < t / 2 := by
    positivity

  have hhalf : t / 2 < t := by
    linarith

  let M9 : ℝ :=
    h3SelectedMildNineQuarterMomentUniformEnvelope ν A (t / 2) t

  have hM9 : 0 ≤ M9 := by
    dsimp only [M9]
    exact
      h3SelectedMildNineQuarterMomentUniformEnvelope_nonneg
        hν U₀ hA hU₀ hhalf0 hhalf htR

  have hState9 :
      ∀ r ∈ Set.Icc (t / 2) t, ∀ k : Fin 3,
        h3SpectralScalarRawFourierNineQuarterMass
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ r k)
          ≤ M9 := by
    intro r hr k
    dsimp only [M9]
    have h :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineQuarterMass_le_uniform_on
        hν U₀ hA hU₀ hhalf0 hr.1 hr.2 htR k
    simpa only [h3SpectralScalarRawFourierNineQuarterMass] using h

  exact
    h3SelectedDuhamelTailThirdVariationComplexKernel_fubini_integrable_of_nineQuarterStateEnvelope
      (M9 := M9)
      hν U₀ hA hU₀
      hhalf0 hhalf htR
      hM9 hState9 i

/-- The actual selected radial-third terminal-half kernel is genuinely
integrable on source-time × frequency. -/
theorem h3SelectedDuhamelTailThirdComplexKernel_fubini_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailThirdComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
        (volume : Measure H3FourierPoint3)) := by
  have hVariation :=
    h3SelectedDuhamelTailThirdVariationComplexKernel_halfTail_fubini_integrable
      hν U₀ hA hU₀ ht htR i

  have hFrozen :=
    h3SelectedDuhamelTailThirdFrozenComplexKernel_fubini_integrable
      hν U₀ hA hU₀ ht htR i

  rw [
    h3SelectedDuhamelTailThirdComplexKernel_eq_variation_add_frozen
      (ν := ν) (A := A) (t := t)
      hν U₀ hA hU₀ i
  ]

  exact hVariation.add hFrozen

/-- Quantitative complete full-third terminal-half norm budget. -/
theorem h3SelectedDuhamelTailThirdComplexKernel_iteratedNormIntegral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let μt : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)
    (∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelTailThirdComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt)
      ≤
    h3SelectedDuhamelTailThirdFullBudget ν A t := by
  dsimp only

  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)

  let V : ℝ × H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelTailThirdVariationComplexKernel
      ν A t hν U₀ hA hU₀ i

  let F : ℝ × H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelTailThirdFrozenComplexKernel
      ν A t hν U₀ hA hU₀ i

  let Z : ℝ × H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelTailThirdComplexKernel
      ν A t hν U₀ hA hU₀ i

  have hhalf0 : 0 < t / 2 := by
    positivity

  have hhalf : t / 2 < t := by
    linarith

  have hVarProd :
      Integrable
        V
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [V, μt]
    exact
      h3SelectedDuhamelTailThirdVariationComplexKernel_halfTail_fubini_integrable
        hν U₀ hA hU₀ ht htR i

  have hFrozenProd :
      Integrable
        F
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [F, μt]
    exact
      h3SelectedDuhamelTailThirdFrozenComplexKernel_fubini_integrable
        hν U₀ hA hU₀ ht htR i

  have hFullProd :
      Integrable
        Z
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [Z, μt]
    exact
      h3SelectedDuhamelTailThirdComplexKernel_fubini_integrable
        hν U₀ hA hU₀ ht htR i

  have hVarSections :
      ∀ᵐ s : ℝ ∂μt,
        Integrable
          (fun ξ : H3FourierPoint3 => V (s, ξ))
          (volume : Measure H3FourierPoint3) :=
    ((integrable_prod_iff hVarProd.aestronglyMeasurable).1 hVarProd).1

  have hFrozenSections :
      ∀ᵐ s : ℝ ∂μt,
        Integrable
          (fun ξ : H3FourierPoint3 => F (s, ξ))
          (volume : Measure H3FourierPoint3) :=
    ((integrable_prod_iff hFrozenProd.aestronglyMeasurable).1 hFrozenProd).1

  have hFullOuter :
      Integrable
        (fun s : ℝ =>
          ∫ ξ : H3FourierPoint3, ‖Z (s, ξ)‖)
        μt := by
    exact
      ((integrable_prod_iff hFullProd.aestronglyMeasurable).1 hFullProd).2

  have hVarOuter :
      Integrable
        (fun s : ℝ =>
          ∫ ξ : H3FourierPoint3, ‖V (s, ξ)‖)
        μt := by
    exact
      ((integrable_prod_iff hVarProd.aestronglyMeasurable).1 hVarProd).2

  have hFrozenOuter :
      Integrable
        (fun s : ℝ =>
          ∫ ξ : H3FourierPoint3, ‖F (s, ξ)‖)
        μt := by
    exact
      ((integrable_prod_iff hFrozenProd.aestronglyMeasurable).1 hFrozenProd).2

  have hMajorOuter :
      Integrable
        (fun s : ℝ =>
          (∫ ξ : H3FourierPoint3, ‖V (s, ξ)‖) +
            ∫ ξ : H3FourierPoint3, ‖F (s, ξ)‖)
        μt :=
    hVarOuter.add hFrozenOuter

  have hKernelEq :=
    h3SelectedDuhamelTailThirdComplexKernel_eq_variation_add_frozen
      (ν := ν) (A := A) (t := t)
      hν U₀ hA hU₀ i

  have hDom :
      ∀ᵐ s : ℝ ∂μt,
        (∫ ξ : H3FourierPoint3, ‖Z (s, ξ)‖)
          ≤
        (∫ ξ : H3FourierPoint3, ‖V (s, ξ)‖) +
          ∫ ξ : H3FourierPoint3, ‖F (s, ξ)‖ := by
    filter_upwards [hVarSections, hFrozenSections] with s hVs hFs

    have hFullSec :
        Integrable
          (fun ξ : H3FourierPoint3 => Z (s, ξ))
          (volume : Measure H3FourierPoint3) := by
      have hSum := hVs.add hFs
      dsimp only [Z, V, F]
      rw [hKernelEq]
      exact hSum

    have hPoint :
        ∀ ξ : H3FourierPoint3,
          ‖Z (s, ξ)‖
            ≤
          ‖V (s, ξ)‖ + ‖F (s, ξ)‖ := by
      intro ξ
      dsimp only [Z, V, F]
      rw [congrFun hKernelEq (s, ξ)]
      exact norm_add_le _ _

    calc
      (∫ ξ : H3FourierPoint3, ‖Z (s, ξ)‖)
          ≤
        ∫ ξ : H3FourierPoint3,
          (‖V (s, ξ)‖ + ‖F (s, ξ)‖) :=
        integral_mono
          hFullSec.norm
          (hVs.norm.add hFs.norm)
          hPoint
      _ =
        (∫ ξ : H3FourierPoint3, ‖V (s, ξ)‖) +
          ∫ ξ : H3FourierPoint3, ‖F (s, ξ)‖ := by
        rw [integral_add hVs.norm hFs.norm]

  have hSplit :
      (∫ s : ℝ,
          (∫ ξ : H3FourierPoint3, ‖Z (s, ξ)‖
            ∂(volume : Measure H3FourierPoint3))
        ∂μt)
        ≤
      (∫ s : ℝ,
          (∫ ξ : H3FourierPoint3, ‖V (s, ξ)‖
            ∂(volume : Measure H3FourierPoint3))
        ∂μt)
        +
      ∫ s : ℝ,
        (∫ ξ : H3FourierPoint3, ‖F (s, ξ)‖
          ∂(volume : Measure H3FourierPoint3))
      ∂μt := by
    calc
      (∫ s : ℝ,
          (∫ ξ : H3FourierPoint3, ‖Z (s, ξ)‖
            ∂(volume : Measure H3FourierPoint3))
        ∂μt)
          ≤
        ∫ s : ℝ,
          ((∫ ξ : H3FourierPoint3, ‖V (s, ξ)‖
              ∂(volume : Measure H3FourierPoint3)) +
            ∫ ξ : H3FourierPoint3, ‖F (s, ξ)‖
              ∂(volume : Measure H3FourierPoint3))
        ∂μt :=
        integral_mono_ae hFullOuter hMajorOuter hDom
      _ =
        (∫ s : ℝ,
            (∫ ξ : H3FourierPoint3, ‖V (s, ξ)‖
              ∂(volume : Measure H3FourierPoint3))
          ∂μt)
          +
        ∫ s : ℝ,
          (∫ ξ : H3FourierPoint3, ‖F (s, ξ)‖
            ∂(volume : Measure H3FourierPoint3))
        ∂μt := by
        rw [integral_add hVarOuter hFrozenOuter]

  have hVariationBound :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            ‖V (s, ξ)‖
          ∂(volume : Measure H3FourierPoint3)
        ∂μt)
        ≤
      h3SelectedDuhamelTailThirdVariationUniformBudget
        ν A (t / 2) t := by
    dsimp only [V, μt]
    exact
      h3SelectedDuhamelTailThirdVariationComplexKernel_iteratedNormIntegral_le_uniformEnvelope
        hν U₀ hA hU₀
        hhalf0 hhalf htR i

  have hFrozenBound :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            ‖F (s, ξ)‖
          ∂(volume : Measure H3FourierPoint3)
        ∂μt)
        ≤
      h3SelectedDuhamelTailThirdFrozenBudget ν A t := by
    dsimp only [F, μt]
    exact
      h3SelectedDuhamelTailThirdFrozenComplexKernel_iteratedNormIntegral_le
        hν U₀ hA hU₀ ht htR i

  unfold h3SelectedDuhamelTailThirdFullBudget

  exact
    le_trans hSplit
      (add_le_add hVariationBound hFrozenBound)

end
end Euclidean
end Bridge
end PrimeTensor
