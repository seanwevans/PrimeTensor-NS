import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVariationOfConstantsStateReduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.RawConvolutionContinuity

/-!
# Classicalization: discharge selected weighted-forcing integrability

The state-level selected variation-of-constants reduction leaves three
fixed-frequency hypotheses.  The weighted-forcing integrability hypothesis is
actually a direct consequence of Banach-path continuity.

The full Leray symbol is not globally continuous in Fourier frequency because
of its exceptional zero mode.  That does not matter here: variation of
constants freezes the frequency `ξ`.  At fixed `ξ`, every Leray coefficient is
a constant.  We therefore avoid composing the large joint finite-vector
continuity theorem and instead build fixed-frequency continuity in two cheap
finite-sum stages:

* scalar raw convolution continuity gives continuity of each divergence
  summand along the two Banach paths;
* the finite divergence coordinates are then combined with the frozen Leray
  coefficients.

Multiplying the resulting continuous forcing by the continuous integrating
factor

    exp (ν * |2πξ|² * s)

preserves continuity, and every continuous scalar function on a compact real
interval is interval integrable.

For the canonical restart path, continuity is already supplied by the modern
physical extension.  Thus the selected state-level variation-of-constants
theorem now requires only the two genuinely pointwise mode inputs:

* raw-mode time continuity;
* the heat--Leray mode ODE.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedVariationOfConstantsWeightedForcing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At fixed output frequency, one raw finite outer-product divergence
coordinate is continuous in source time along continuous H³ velocity paths. -/
theorem continuous_h3RawFinOuterProductDivergence_fixedFrequency
    (U V : ℝ → H3SpectralFinVectorState)
    (hU : Continuous U)
    (hV : Continuous V)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    Continuous
      (fun s : ℝ =>
        h3RawFinOuterProductDivergence
          (U s) (V s) i ξ) := by
  unfold h3RawFinOuterProductDivergence

  apply continuous_finsetSum
  intro j hj

  have hUi :
      Continuous
        (fun s : ℝ => U s i) := by
    exact (continuous_apply i).comp hU

  have hVj :
      Continuous
        (fun s : ℝ => V s j) := by
    exact (continuous_apply j).comp hV

  have hInput :
      Continuous
        (fun s : ℝ =>
          (U s i, (V s j, ξ))) := by
    exact
      Continuous.prodMk hUi
        (Continuous.prodMk hVj continuous_const)

  have hConv :
      Continuous
        (fun s : ℝ =>
          h3RawProductConvolution
            (U s i) (V s j) ξ) := by
    exact
      continuous_h3RawProductConvolution.comp hInput

  exact continuous_const.mul hConv

/-- At a fixed Fourier frequency, the complete finite Leray forcing is
continuous in source time along continuous H³ velocity paths.  The possible
zero-frequency discontinuity of the Leray multiplier disappears because the
frequency is frozen. -/
theorem continuous_h3RawFinLerayOuterProductDivergence_fixedFrequency
    (U V : ℝ → H3SpectralFinVectorState)
    (hU : Continuous U)
    (hV : Continuous V)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    Continuous
      (fun s : ℝ =>
        h3RawFinLerayOuterProductDivergence
          (U s) (V s) i ξ) := by
  unfold h3RawFinLerayOuterProductDivergence

  apply continuous_finsetSum
  intro k hk

  have hDiv :
      Continuous
        (fun s : ℝ =>
          h3RawFinOuterProductDivergence
            (U s) (V s) k ξ) :=
    continuous_h3RawFinOuterProductDivergence_fixedFrequency
      U V hU hV k ξ

  exact continuous_const.mul hDiv

/-- The fixed-frequency Leray forcing multiplied by the integrating factor is
interval integrable along arbitrary continuous H³ velocity paths. -/
theorem h3RawFinLerayOuterProductDivergence_weighted_intervalIntegrable_of_continuous
    (ν : ℝ)
    (ξ : H3FourierPoint3)
    (U V : ℝ → H3SpectralFinVectorState)
    (hU : Continuous U)
    (hV : Continuous V)
    (i : Fin 3)
    (a b : ℝ) :
    IntervalIntegrable
      (fun s : ℝ =>
        Real.exp
            (ν * h3FourierGradientSquare ξ * s)
          •
        h3RawFinLerayOuterProductDivergence
          (U s) (V s) i ξ)
      volume
      a
      b := by
  have hExp :
      Continuous
        (fun s : ℝ =>
          Real.exp
            (ν * h3FourierGradientSquare ξ * s)) := by
    fun_prop

  have hForcing :
      Continuous
        (fun s : ℝ =>
          h3RawFinLerayOuterProductDivergence
            (U s) (V s) i ξ) :=
    continuous_h3RawFinLerayOuterProductDivergence_fixedFrequency
      U V hU hV i ξ

  have hWeighted :
      Continuous
        (fun s : ℝ =>
          Real.exp
              (ν * h3FourierGradientSquare ξ * s)
            •
          h3RawFinLerayOuterProductDivergence
            (U s) (V s) i ξ) := by
    exact hExp.smul hForcing

  exact hWeighted.intervalIntegrable a b

/-- The modern canonical restart extension automatically satisfies the
weighted-forcing integrability hypothesis at every fixed frequency and
coordinate. -/
theorem h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_weightedForcing_intervalIntegrable
    {ν A a b : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ξ : H3FourierPoint3)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    IntervalIntegrable
      (fun s : ℝ =>
        Real.exp
            (ν * h3FourierGradientSquare ξ * s)
          •
        h3RawFinLerayOuterProductDivergence
          (W s) (W s) i ξ)
      volume
      a
      b := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWcont : Continuous W := by
    dsimp only [
      W,
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
    ]
    exact
      continuous_h3PathPhysicalRealExtension
        (h3FinHeatLerayRestartRadius ν A)
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadius
          hν U₀ hA hU₀)

  exact
    h3RawFinLerayOuterProductDivergence_weighted_intervalIntegrable_of_continuous
      ν ξ W W hWcont hWcont i a b

/-- After discharging weighted-forcing integrability from path continuity, the
selected H³ state-level variation-of-constants identity depends only on raw-mode
time continuity and the concrete Fourier-mode ODE. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_variationOfConstants_state_of_mode_continuity_and_ODE
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hFContinuous :
      ∀ ξ : H3FourierPoint3, ∀ i : Fin 3,
        ContinuousOn
          (fun s : ℝ =>
            h3SpectralScalarRawFourier
              ((h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
                hν U₀ hA hU₀) s i) ξ)
          (Set.Icc (0 : ℝ) t))
    (hODE :
      ∀ ξ : H3FourierPoint3,
        ∀ s ∈ Set.Ioo (0 : ℝ) t,
          H3FinHeatLerayModeODEAt
            ν ξ
            (h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
              hν U₀ hA hU₀)
            s) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    W t
      =
    h3SpectralVelocityHeatApplyNN
        ν hν.le (NNReal.mk t ht.le) (W 0)
      -
    h3SpectralFinHeatLerayDuhamel
      ν t hν W W := by
  apply
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_variationOfConstants_state_of_mode_data
      hν U₀ hA hU₀ ht htR hFContinuous hODE

  intro ξ i

  exact
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_weightedForcing_intervalIntegrable
      (a := (0 : ℝ)) (b := t)
      hν U₀ hA hU₀ ξ i

end

end Euclidean
end Bridge
end PrimeTensor
