import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.UniformFourthMomentEnvelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.NineteenQuarterMass

/-!
# Sixth Fréchet endpoint: interval-uniform cubic forcing envelope

The selected mild state now carries one full-fourth raw Fourier mass bound valid
on every positive interval `[a,t]`.

This file pushes that interval constant through the already-closed sixth-layer
nonlinear algebra:

    state M₄
      -> product convolution M₄
      -> one derivative M₃
      -> finite divergence/Leray forcing M₃.

The resulting interval-uniform forcing constant is then substituted into the
abstract `19/4` source-mass theorem.  Hence the selected `19/4` Duhamel source
kernel is product-integrable with the explicit subcritical budget

    B₃^[a,t] * 8 * C₇(ν) * (t-a)^(1/8).
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSixthEndpointUniformThirdForcingEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One interval-uniform cubic bound for every selected scalar
derivative-convolution term. -/
noncomputable def h3SelectedDerivativeThirdMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  (2 * Real.pi) *
    (h3FourierFourthSplitCoefficient *
      (h3SelectedMildFourthMomentUniformEnvelope ν A a t *
          h3SelectedRestartRawFourierL1Envelope A +
        h3SelectedRestartRawFourierL1Envelope A *
          h3SelectedMildFourthMomentUniformEnvelope ν A a t))

/-- Every selected scalar derivative-convolution term at `r ∈ [a,t]` is
bounded by the same cubic interval constant. -/
theorem h3FourierDerivativeRawProductConvolution_selectedRestart_thirdMass_le_uniform_on
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
    h3FourierDerivativeRawProductConvolutionThirdMass
        (W r i) (W r j) j
      ≤
    h3SelectedDerivativeThirdMomentUniformEnvelope
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

  have hWi4 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier (W r i) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fourthMoment_integrable
        hν U₀ hA hU₀ hr hrR i

  have hWj4 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier (W r j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fourthMoment_integrable
        hν U₀ hA hU₀ hr hrR j

  have hBase :=
    h3FourierDerivativeRawProductConvolutionThirdMass_le_stateMasses
      (W r i) (W r j) j hWi4 hWj4

  let M4 : ℝ :=
    h3SelectedMildFourthMomentUniformEnvelope ν A a t

  let M0 : ℝ :=
    h3SelectedRestartRawFourierL1Envelope A

  have hM0nonneg : 0 ≤ M0 := by
    dsimp only [M0]
    exact
      h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  have hWi4m :
      h3SpectralScalarRawFourierFourthMass (W r i)
        ≤ M4 := by
    dsimp only [M4, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fourthMass_le_uniform_on
        hν U₀ hA hU₀ ha har hrt htR i

  have hWj4m :
      h3SpectralScalarRawFourierFourthMass (W r j)
        ≤ M4 := by
    dsimp only [M4, W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fourthMass_le_uniform_on
        hν U₀ hA hU₀ ha har hrt htR j

  have hM4nonneg : 0 ≤ M4 := by
    exact
      le_trans
        (h3SpectralScalarRawFourierFourthMass_nonneg (W r i))
        hWi4m

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

  have hi4 :
      0 ≤ h3SpectralScalarRawFourierFourthMass (W r i) :=
    h3SpectralScalarRawFourierFourthMass_nonneg (W r i)

  have hj4 :
      0 ≤ h3SpectralScalarRawFourierFourthMass (W r j) :=
    h3SpectralScalarRawFourierFourthMass_nonneg (W r j)

  have hLeft :
      h3SpectralScalarRawFourierFourthMass (W r i) *
          h3SpectralScalarRawFourierL1Mass (W r j)
        ≤
      M4 * M0 :=
    mul_le_mul
      hWi4m hWj0
      hj0 hM4nonneg

  have hRight :
      h3SpectralScalarRawFourierL1Mass (W r i) *
          h3SpectralScalarRawFourierFourthMass (W r j)
        ≤
      M0 * M4 :=
    mul_le_mul
      hWi0 hWj4m
      hj4 hM0nonneg

  have hPair :
      h3SpectralScalarRawFourierFourthMass (W r i) *
            h3SpectralScalarRawFourierL1Mass (W r j)
          +
        h3SpectralScalarRawFourierL1Mass (W r i) *
            h3SpectralScalarRawFourierFourthMass (W r j)
        ≤
      M4 * M0 + M0 * M4 :=
    add_le_add hLeft hRight

  have hSplit0 :
      0 ≤ h3FourierFourthSplitCoefficient :=
    h3FourierFourthSplitCoefficient_nonneg

  have hInner :
      h3FourierFourthSplitCoefficient *
          (h3SpectralScalarRawFourierFourthMass (W r i) *
                h3SpectralScalarRawFourierL1Mass (W r j)
            +
            h3SpectralScalarRawFourierL1Mass (W r i) *
                h3SpectralScalarRawFourierFourthMass (W r j))
        ≤
      h3FourierFourthSplitCoefficient *
        (M4 * M0 + M0 * M4) :=
    mul_le_mul_of_nonneg_left hPair hSplit0

  unfold h3SelectedDerivativeThirdMomentUniformEnvelope

  exact
    le_trans hBase
      (mul_le_mul_of_nonneg_left
        hInner
        (by positivity))

/-- The interval-uniform scalar derivative cubic envelope is nonnegative. -/
theorem h3SelectedDerivativeThirdMomentUniformEnvelope_nonneg
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    0 ≤
      h3SelectedDerivativeThirdMomentUniformEnvelope
        ν A a t := by
  have hM4 :
      0 ≤ h3SelectedMildFourthMomentUniformEnvelope ν A a t :=
    h3SelectedMildFourthMomentUniformEnvelope_nonneg
      hν U₀ hA hU₀ ha hat htR

  have hM0 :
      0 ≤ h3SelectedRestartRawFourierL1Envelope A :=
    h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  unfold h3SelectedDerivativeThirdMomentUniformEnvelope

  exact
    mul_nonneg
      (by positivity)
      (mul_nonneg
        h3FourierFourthSplitCoefficient_nonneg
        (add_nonneg
          (mul_nonneg hM4 hM0)
          (mul_nonneg hM0 hM4)))

/-- One interval-uniform cubic forcing envelope for every selected forcing
coordinate. -/
noncomputable def h3SelectedForcingThirdMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  2 *
    ∑ _k : Fin 3,
      ∑ _j : Fin 3,
        h3SelectedDerivativeThirdMomentUniformEnvelope
          ν A a t

/-- Every selected forcing coordinate at `r ∈ [a,t]` has cubic raw Fourier
mass bounded by one interval-uniform constant. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_thirdMass_le_uniform_on
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
    h3RawFinLerayOuterProductDivergenceThirdMass
        (W r) (W r) i
      ≤
    h3SelectedForcingThirdMomentUniformEnvelope
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
            ‖ξ‖ ^ 3 *
              ‖h3FourierDerivativeSymbol j ξ *
                h3RawProductConvolution (W r k) (W r j) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k j
    dsimp only [W]
    exact
      h3FourierDerivative_mul_rawProductConvolution_selectedRestart_thirdMoment_integrable
        hν U₀ hA hU₀ hr hrR k j

  have hDiv :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3RawFinOuterProductDivergence (W r) (W r) k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    exact
      h3RawFinOuterProductDivergence_thirdMoment_integrable_of_derivatives
        (W r) (W r) k (hDeriv k)

  have hLeray :=
    h3RawFinLerayOuterProductDivergenceThirdMass_le
      (W r) (W r) i hDiv

  have hDivBound :
      ∀ k : Fin 3,
        h3RawFinOuterProductDivergenceThirdMass
            (W r) (W r) k
          ≤
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionThirdMass
            (W r k) (W r j) j := by
    intro k
    exact
      h3RawFinOuterProductDivergenceThirdMass_le
        (W r) (W r) k (hDeriv k)

  have hDerivativeBound :
      ∀ k j : Fin 3,
        h3FourierDerivativeRawProductConvolutionThirdMass
            (W r k) (W r j) j
          ≤
        h3SelectedDerivativeThirdMomentUniformEnvelope
          ν A a t := by
    intro k j
    dsimp only [W]
    exact
      h3FourierDerivativeRawProductConvolution_selectedRestart_thirdMass_le_uniform_on
        hν U₀ hA hU₀ ha har hrt htR k j

  have hDivSum :
      (∑ k : Fin 3,
          h3RawFinOuterProductDivergenceThirdMass
            (W r) (W r) k)
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionThirdMass
            (W r k) (W r j) j :=
    Finset.sum_le_sum fun k _ =>
      hDivBound k

  have hDerivativeSum :
      (∑ k : Fin 3,
          ∑ j : Fin 3,
            h3FourierDerivativeRawProductConvolutionThirdMass
              (W r k) (W r j) j)
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          h3SelectedDerivativeThirdMomentUniformEnvelope
            ν A a t :=
    Finset.sum_le_sum fun k _ =>
      Finset.sum_le_sum fun j _ =>
        hDerivativeBound k j

  unfold h3SelectedForcingThirdMomentUniformEnvelope

  exact
    le_trans hLeray
      (mul_le_mul_of_nonneg_left
        (le_trans hDivSum hDerivativeSum)
        (by norm_num))

/-- The interval-uniform selected cubic forcing envelope is nonnegative. -/
theorem h3SelectedForcingThirdMomentUniformEnvelope_nonneg
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    0 ≤
      h3SelectedForcingThirdMomentUniformEnvelope
        ν A a t := by
  have hD0 :
      0 ≤
        h3SelectedDerivativeThirdMomentUniformEnvelope
          ν A a t :=
    h3SelectedDerivativeThirdMomentUniformEnvelope_nonneg
      hν U₀ hA hU₀ ha hat htR

  unfold h3SelectedForcingThirdMomentUniformEnvelope

  exact
    mul_nonneg
      (by norm_num)
      (Finset.sum_nonneg fun _k _ =>
        Finset.sum_nonneg fun _j _ =>
          hD0)

/-- Explicit `19/4` source budget obtained by inserting the interval-uniform
selected cubic forcing constant. -/
noncomputable def h3SelectedDuhamelNineteenQuarterUniformBudget
    (ν A a t : ℝ) : ℝ :=
  h3SelectedDuhamelNineteenQuarterSourceBudget
    ν a t
    (h3SelectedForcingThirdMomentUniformEnvelope
      ν A a t)

/-- The selected `19/4` source kernel is product-integrable on every positive
source interval using the uniform cubic forcing envelope. -/
theorem h3SelectedDuhamelNineteenQuarterComplexKernel_fubini_integrable_uniformEnvelope
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
      (h3SelectedDuhamelNineteenQuarterComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let B : ℝ :=
    h3SelectedForcingThirdMomentUniformEnvelope
      ν A a t

  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact
      h3SelectedForcingThirdMomentUniformEnvelope_nonneg
        hν U₀ hA hU₀ ha hat htR

  have hMassI :
      ∀ s ∈ Set.Ioo a t,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        h3RawFinLerayOuterProductDivergenceThirdMass
          (W s) (W s) i ≤ B := by
    intro s hs
    dsimp only [B]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_thirdMass_le_uniform_on
        hν U₀ hA hU₀
        ha hs.1.le hs.2.le htR i

  exact
    h3SelectedDuhamelNineteenQuarterComplexKernel_fubini_integrable_of_thirdMass_le
      (B := B)
      hν U₀ hA hU₀ ha hat htR hB0 i hMassI

/-- Quantitative iterated-norm estimate for the selected `19/4` source kernel
with the actual uniform cubic forcing envelope inserted. -/
theorem h3SelectedDuhamelNineteenQuarterComplexKernel_iteratedNormIntegral_le_uniformEnvelope
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
          ‖h3SelectedDuhamelNineteenQuarterComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt)
      ≤
    h3SelectedDuhamelNineteenQuarterUniformBudget
      ν A a t := by
  dsimp only

  let B : ℝ :=
    h3SelectedForcingThirdMomentUniformEnvelope
      ν A a t

  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact
      h3SelectedForcingThirdMomentUniformEnvelope_nonneg
        hν U₀ hA hU₀ ha hat htR

  have hMassI :
      ∀ s ∈ Set.Ioo a t,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        h3RawFinLerayOuterProductDivergenceThirdMass
          (W s) (W s) i ≤ B := by
    intro s hs
    dsimp only [B]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_thirdMass_le_uniform_on
        hν U₀ hA hU₀
        ha hs.1.le hs.2.le htR i

  unfold h3SelectedDuhamelNineteenQuarterUniformBudget

  exact
    h3SelectedDuhamelNineteenQuarterComplexKernel_iteratedNormIntegral_le_of_thirdMass_le
      (B := B)
      hν U₀ hA hU₀ ha hat htR hB0 i hMassI

end
end Euclidean
end Bridge
end PrimeTensor
