import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.UniformNineteenQuarterMomentEnvelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.FifthMass

/-!
# Sixth Fréchet endpoint: interval-uniform selected fifteen-quarter forcing envelope

The selected mild state now carries one `19/4` raw Fourier mass bound valid on
every positive interval `[a,t]`.

This file pushes that interval constant through the already-closed nonlinear
algebra:

    state M_{19/4}
      -> product convolution M_{19/4}
      -> one derivative M_{15/4}
      -> finite divergence/Leray forcing M_{15/4}.

The resulting forcing constant is then substituted into the abstract
full-fifth source-mass theorem. Consequently the full-fifth Duhamel source
kernel is product-integrable with the explicit subcritical budget

    B_{15/4}^{[a,t]}
      * (8/3)
      * C_5(ν)
      * (t-a)^(3/8).
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSixthEndpointUniformFifteenQuarterForcingEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One interval-uniform `15/4` bound for every selected scalar
derivative-convolution term. -/
noncomputable def h3SelectedDerivativeFifteenQuarterMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  (2 * Real.pi) *
    (h3FourierNineteenQuarterSplitCoefficient *
      (h3SelectedMildNineteenQuarterMomentUniformEnvelope ν A a t *
          h3SelectedRestartRawFourierL1Envelope A +
        h3SelectedRestartRawFourierL1Envelope A *
          h3SelectedMildNineteenQuarterMomentUniformEnvelope ν A a t))

/-- Every selected scalar derivative-convolution term at `r ∈ [a,t]` is
bounded by the same `15/4` interval constant. -/
theorem h3FourierDerivativeRawProductConvolution_selectedRestart_fifteenQuarterMass_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i j : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3FourierDerivativeRawProductConvolutionFifteenQuarterMass
        (W r i) (W r j) j
      ≤
    h3SelectedDerivativeFifteenQuarterMomentUniformEnvelope
      ν A a t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have hrR :
      r ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hrt htR

  have hWi19 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier (W r i) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineteenQuarterMoment_integrable
        hν U₀ hA hU₀ hr hrR i

  have hWj19 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier (W r j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineteenQuarterMoment_integrable
        hν U₀ hA hU₀ hr hrR j

  have hBase :=
    h3FourierDerivativeRawProductConvolutionFifteenQuarterMass_le_stateMasses
      (W r i) (W r j) j hWi19 hWj19

  let M19 : ℝ :=
    h3SelectedMildNineteenQuarterMomentUniformEnvelope ν A a t

  let M0 : ℝ :=
    h3SelectedRestartRawFourierL1Envelope A

  have hM0nonneg : 0 ≤ M0 := by
    dsimp only [M0]
    exact
      h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  have hWi19m :
      h3SpectralScalarRawFourierNineteenQuarterMass (W r i)
        ≤ M19 := by
    dsimp only [M19, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineteenQuarterMass_le_uniform_on
        hν U₀ hA hU₀ ha har hrt htR i

  have hWj19m :
      h3SpectralScalarRawFourierNineteenQuarterMass (W r j)
        ≤ M19 := by
    dsimp only [M19, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineteenQuarterMass_le_uniform_on
        hν U₀ hA hU₀ ha har hrt htR j

  have hM19nonneg : 0 ≤ M19 := by
    exact
      le_trans
        (h3SpectralScalarRawFourierNineteenQuarterMass_nonneg (W r i))
        hWi19m

  have hWi0 :
      h3SpectralScalarRawFourierL1Mass (W r i)
        ≤ M0 := by
    dsimp only [M0, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1Mass_le
        hν U₀ hA hU₀ r i

  have hWj0 :
      h3SpectralScalarRawFourierL1Mass (W r j)
        ≤ M0 := by
    dsimp only [M0, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1Mass_le
        hν U₀ hA hU₀ r j

  have hi0 :
      0 ≤ h3SpectralScalarRawFourierL1Mass (W r i) :=
    h3SpectralScalarRawFourierL1Mass_nonneg (W r i)

  have hj0 :
      0 ≤ h3SpectralScalarRawFourierL1Mass (W r j) :=
    h3SpectralScalarRawFourierL1Mass_nonneg (W r j)

  have hi19 :
      0 ≤ h3SpectralScalarRawFourierNineteenQuarterMass (W r i) :=
    h3SpectralScalarRawFourierNineteenQuarterMass_nonneg (W r i)

  have hj19 :
      0 ≤ h3SpectralScalarRawFourierNineteenQuarterMass (W r j) :=
    h3SpectralScalarRawFourierNineteenQuarterMass_nonneg (W r j)

  have hLeft :
      h3SpectralScalarRawFourierNineteenQuarterMass (W r i) *
          h3SpectralScalarRawFourierL1Mass (W r j)
        ≤
      M19 * M0 :=
    mul_le_mul
      hWi19m hWj0
      hj0 hM19nonneg

  have hRight :
      h3SpectralScalarRawFourierL1Mass (W r i) *
          h3SpectralScalarRawFourierNineteenQuarterMass (W r j)
        ≤
      M0 * M19 :=
    mul_le_mul
      hWi0 hWj19m
      hj19 hM0nonneg

  have hPair :
      h3SpectralScalarRawFourierNineteenQuarterMass (W r i) *
            h3SpectralScalarRawFourierL1Mass (W r j)
          +
        h3SpectralScalarRawFourierL1Mass (W r i) *
            h3SpectralScalarRawFourierNineteenQuarterMass (W r j)
        ≤
      M19 * M0 + M0 * M19 :=
    add_le_add hLeft hRight

  have hSplit0 :
      0 ≤ h3FourierNineteenQuarterSplitCoefficient :=
    h3FourierNineteenQuarterSplitCoefficient_nonneg

  have hInner :
      h3FourierNineteenQuarterSplitCoefficient *
          (h3SpectralScalarRawFourierNineteenQuarterMass (W r i) *
                h3SpectralScalarRawFourierL1Mass (W r j)
            +
            h3SpectralScalarRawFourierL1Mass (W r i) *
                h3SpectralScalarRawFourierNineteenQuarterMass (W r j))
        ≤
      h3FourierNineteenQuarterSplitCoefficient *
        (M19 * M0 + M0 * M19) :=
    mul_le_mul_of_nonneg_left hPair hSplit0

  unfold h3SelectedDerivativeFifteenQuarterMomentUniformEnvelope

  exact
    le_trans hBase
      (mul_le_mul_of_nonneg_left
        hInner
        (by positivity))

/-- The interval-uniform scalar derivative envelope is nonnegative. -/
theorem h3SelectedDerivativeFifteenQuarterMomentUniformEnvelope_nonneg
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    0 ≤
      h3SelectedDerivativeFifteenQuarterMomentUniformEnvelope
        ν A a t := by
  have hM19 :
      0 ≤ h3SelectedMildNineteenQuarterMomentUniformEnvelope ν A a t :=
    h3SelectedMildNineteenQuarterMomentUniformEnvelope_nonneg
      hν U₀ hA hU₀ ha hat htR

  have hM0 :
      0 ≤ h3SelectedRestartRawFourierL1Envelope A :=
    h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  unfold h3SelectedDerivativeFifteenQuarterMomentUniformEnvelope

  exact
    mul_nonneg
      (by positivity)
      (mul_nonneg
        h3FourierNineteenQuarterSplitCoefficient_nonneg
        (add_nonneg
          (mul_nonneg hM19 hM0)
          (mul_nonneg hM0 hM19)))

/-- One interval-uniform `15/4` forcing envelope for every selected forcing
coordinate. -/
noncomputable def h3SelectedForcingFifteenQuarterMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  2 *
    ∑ _k : Fin 3,
      ∑ _j : Fin 3,
        h3SelectedDerivativeFifteenQuarterMomentUniformEnvelope
          ν A a t

/-- Every selected forcing coordinate at `r ∈ [a,t]` has `15/4` raw Fourier
mass bounded by one interval-uniform constant. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_fifteenQuarterMass_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3RawFinLerayOuterProductDivergenceFifteenQuarterMass
        (W r) (W r) i
      ≤
    h3SelectedForcingFifteenQuarterMomentUniformEnvelope
      ν A a t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have hrR :
      r ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hrt htR

  have hDeriv :
      ∀ k j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierFifteenQuarterWeight ξ *
              ‖h3FourierDerivativeSymbol j ξ *
                h3RawProductConvolution (W r k) (W r j) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k j
    dsimp only [W]
    exact
      h3FourierDerivative_mul_rawProductConvolution_selectedRestart_fifteenQuarterMoment_integrable
        hν U₀ hA hU₀ hr hrR k j

  have hDiv :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierFifteenQuarterWeight ξ *
              ‖h3RawFinOuterProductDivergence (W r) (W r) k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    exact
      h3RawFinOuterProductDivergence_fifteenQuarterMoment_integrable_of_derivatives
        (W r) (W r) k (hDeriv k)

  have hLeray :=
    h3RawFinLerayOuterProductDivergenceFifteenQuarterMass_le
      (W r) (W r) i hDiv

  have hDivBound :
      ∀ k : Fin 3,
        h3RawFinOuterProductDivergenceFifteenQuarterMass
            (W r) (W r) k
          ≤
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionFifteenQuarterMass
            (W r k) (W r j) j := by
    intro k
    exact
      h3RawFinOuterProductDivergenceFifteenQuarterMass_le
        (W r) (W r) k (hDeriv k)

  have hDerivativeBound :
      ∀ k j : Fin 3,
        h3FourierDerivativeRawProductConvolutionFifteenQuarterMass
            (W r k) (W r j) j
          ≤
        h3SelectedDerivativeFifteenQuarterMomentUniformEnvelope
          ν A a t := by
    intro k j
    dsimp only [W]
    exact
      h3FourierDerivativeRawProductConvolution_selectedRestart_fifteenQuarterMass_le_uniform_on
        hν U₀ hA hU₀ ha har hrt htR k j

  have hDivSum :
      (∑ k : Fin 3,
          h3RawFinOuterProductDivergenceFifteenQuarterMass
            (W r) (W r) k)
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionFifteenQuarterMass
            (W r k) (W r j) j :=
    Finset.sum_le_sum fun k _ =>
      hDivBound k

  have hDerivativeSum :
      (∑ k : Fin 3,
          ∑ j : Fin 3,
            h3FourierDerivativeRawProductConvolutionFifteenQuarterMass
              (W r k) (W r j) j)
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          h3SelectedDerivativeFifteenQuarterMomentUniformEnvelope
            ν A a t :=
    Finset.sum_le_sum fun k _ =>
      Finset.sum_le_sum fun j _ =>
        hDerivativeBound k j

  unfold h3SelectedForcingFifteenQuarterMomentUniformEnvelope

  exact
    le_trans hLeray
      (mul_le_mul_of_nonneg_left
        (le_trans hDivSum hDerivativeSum)
        (by norm_num))

/-- The interval-uniform selected forcing `15/4` envelope is nonnegative. -/
theorem h3SelectedForcingFifteenQuarterMomentUniformEnvelope_nonneg
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    0 ≤
      h3SelectedForcingFifteenQuarterMomentUniformEnvelope
        ν A a t := by
  have hD0 :
      0 ≤
        h3SelectedDerivativeFifteenQuarterMomentUniformEnvelope
          ν A a t :=
    h3SelectedDerivativeFifteenQuarterMomentUniformEnvelope_nonneg
      hν U₀ hA hU₀ ha hat htR

  unfold h3SelectedForcingFifteenQuarterMomentUniformEnvelope

  exact
    mul_nonneg
      (by norm_num)
      (Finset.sum_nonneg fun _k _ =>
        Finset.sum_nonneg fun _j _ =>
          hD0)

/-- Explicit full-fifth source budget obtained by inserting the
interval-uniform selected forcing `15/4` constant. -/
noncomputable def h3SelectedDuhamelFifthUniformBudget
    (ν A a t : ℝ) : ℝ :=
  h3SelectedDuhamelFifthSourceBudget
    ν a t
    (h3SelectedForcingFifteenQuarterMomentUniformEnvelope
      ν A a t)

/-- The selected full-fifth source kernel is genuinely product-integrable on
every positive source interval using the uniform `15/4` forcing envelope. -/
theorem h3SelectedDuhamelFifthComplexKernel_fubini_integrable_uniformEnvelope
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelFifthComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let B : ℝ :=
    h3SelectedForcingFifteenQuarterMomentUniformEnvelope
      ν A a t

  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact
      h3SelectedForcingFifteenQuarterMomentUniformEnvelope_nonneg
        hν U₀ hA hU₀ ha hat htR

  have hMassI :
      ∀ s ∈ Set.Ioo a t,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        h3RawFinLerayOuterProductDivergenceFifteenQuarterMass
          (W s) (W s) i ≤ B := by
    intro s hs
    dsimp only [B]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_fifteenQuarterMass_le_uniform_on
        hν U₀ hA hU₀
        ha hs.1.le hs.2.le htR i

  exact
    h3SelectedDuhamelFifthComplexKernel_fubini_integrable_of_fifteenQuarterMass_le
      (B := B)
      hν U₀ hA hU₀ ha hat htR hB0 i hMassI

/-- Quantitative iterated-norm estimate for the selected full-fifth source
kernel with the actual uniform forcing envelope inserted. -/
theorem h3SelectedDuhamelFifthComplexKernel_iteratedNormIntegral_le_uniformEnvelope
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let μt : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Ioo a t)
    (∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelFifthComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt)
      ≤
    h3SelectedDuhamelFifthUniformBudget ν A a t := by
  dsimp only

  let B : ℝ :=
    h3SelectedForcingFifteenQuarterMomentUniformEnvelope
      ν A a t

  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact
      h3SelectedForcingFifteenQuarterMomentUniformEnvelope_nonneg
        hν U₀ hA hU₀ ha hat htR

  have hMassI :
      ∀ s ∈ Set.Ioo a t,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        h3RawFinLerayOuterProductDivergenceFifteenQuarterMass
          (W s) (W s) i ≤ B := by
    intro s hs
    dsimp only [B]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_fifteenQuarterMass_le_uniform_on
        hν U₀ hA hU₀
        ha hs.1.le hs.2.le htR i

  unfold h3SelectedDuhamelFifthUniformBudget

  exact
    h3SelectedDuhamelFifthComplexKernel_iteratedNormIntegral_le_of_fifteenQuarterMass_le
      (B := B)
      hν U₀ hA hU₀ ha hat htR hB0 i hMassI

end
end Euclidean
end Bridge
end PrimeTensor
