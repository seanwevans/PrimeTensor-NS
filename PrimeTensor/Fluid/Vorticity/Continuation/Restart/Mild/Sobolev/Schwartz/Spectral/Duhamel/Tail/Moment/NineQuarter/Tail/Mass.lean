import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NineQuarter.Variation.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NineQuarterAmplitude

/-!
# Quantitative nine-quarter mass of the selected terminal tail

The selected terminal-half `9/4` kernel has two quantitative pieces:

* `NineQuarterVariationMass`:
  the source-state variation is bounded by the exact integral of the normalized
  `-7/8` cancellation majorant;
* `NineQuarterFrozenMass`:
  the frozen terminal forcing is bounded by the exact second-heat primitive
  coefficient times the selected quarter forcing envelope.

Both kernels are already genuinely integrable on the product space.  Fubini
therefore rotates the variation budget into the frequency-outer orientation
used by the amplitude layer.

The algebraic identity

    full = variation + frozen

and `norm_integral_le_integral_norm` then give

    ∫ |ξ|^(9/4) |T_i(ξ)| dξ
      ≤
    B_var(ν,A,t) + B_frozen(ν,A,t),

where `T_i` is the actual selected terminal-tail raw Fourier amplitude.

No new endpoint estimate is introduced here.  This is the quantitative
recombination of the two terminal-half pieces.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzNineQuarterTailMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit total budget for the selected terminal-half `9/4` tail. -/
noncomputable def h3SelectedDuhamelTailNineQuarterBudget
    (ν A t : ℝ) : ℝ :=
  h3SelectedDuhamelTailNineQuarterVariationBudget ν A t +
    h3SelectedDuhamelTailNineQuarterFrozenBudget ν A t

/-- Quantitative `9/4` raw Fourier mass bound for the actual selected
terminal-tail amplitude. -/
theorem h3SelectedDuhamelTailRawFourierAmplitude_nineQuarterMass_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖)
      ≤
    h3SelectedDuhamelTailNineQuarterBudget ν A t := by
  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)

  let V : ℝ × H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelTailNineQuarterVariationComplexKernel
      ν A t hν U₀ hA hU₀ i

  let Z : ℝ × H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
      ν A t hν U₀ hA hU₀ i

  let K : ℝ × H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelTailNineQuarterComplexKernel
      ν A t hν U₀ hA hU₀ i

  have hVProd :
      Integrable
        V
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [V, μt]
    exact
      h3SelectedDuhamelTailNineQuarterVariationComplexKernel_fubini_integrable
        hν U₀ hA hU₀ ht htR i

  have hZProd :
      Integrable
        Z
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [Z, μt]
    exact
      h3SelectedDuhamelTailNineQuarterFrozenComplexKernel_fubini_integrable
        hν U₀ hA hU₀ ht htR i

  have hVOuter :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∫ s : ℝ, ‖V (s, ξ)‖ ∂μt)
        (volume : Measure H3FourierPoint3) :=
    hVProd.integral_norm_prod_right

  have hZOuter :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∫ s : ℝ, ‖Z (s, ξ)‖ ∂μt)
        (volume : Measure H3FourierPoint3) :=
    hZProd.integral_norm_prod_right

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (∫ s : ℝ, ‖V (s, ξ)‖ ∂μt) +
            ∫ s : ℝ, ‖Z (s, ξ)‖ ∂μt)
        (volume : Measure H3FourierPoint3) :=
    hVOuter.add hZOuter

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ *
            ‖h3SelectedDuhamelTailRawFourierAmplitude
              ν A t hν U₀ hA hU₀ i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SelectedDuhamelTailRawFourierAmplitude_nineQuarterMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hVSec :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun s : ℝ => V (s, ξ))
          μt :=
    hVProd.prod_left_ae

  have hZSec :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun s : ℝ => Z (s, ξ))
          μt :=
    hZProd.prod_left_ae

  have hKernelEq :
      K
        =
      (fun p : ℝ × H3FourierPoint3 =>
        V p + Z p) := by
    dsimp only [K, V, Z]
    exact
      h3SelectedDuhamelTailNineQuarterComplexKernel_eq_variation_add_frozen
        (ν := ν) (A := A) (t := t) hν U₀ hA hU₀ i

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        h3FourierNineQuarterWeight ξ *
            ‖h3SelectedDuhamelTailRawFourierAmplitude
              ν A t hν U₀ hA hU₀ i ξ‖
          ≤
        (∫ s : ℝ, ‖V (s, ξ)‖ ∂μt) +
          ∫ s : ℝ, ‖Z (s, ξ)‖ ∂μt := by
    filter_upwards [hVSec, hZSec] with ξ hVξ hZξ

    have hWeight0 :
        0 ≤ h3FourierNineQuarterWeight ξ := by
      unfold h3FourierNineQuarterWeight
      positivity

    have hWeightedNorm :
        h3FourierNineQuarterWeight ξ *
            ‖h3SelectedDuhamelTailRawFourierAmplitude
              ν A t hν U₀ hA hU₀ i ξ‖
          =
        ‖h3SelectedDuhamelTailNineQuarterFourierAmplitude
          ν A t hν U₀ hA hU₀ i ξ‖ := by
      rw [
        h3SelectedDuhamelTailNineQuarterFourierAmplitude_eq_weight_mul_raw
          hν U₀ hA hU₀ i ξ,
        norm_mul,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg hWeight0
      ]

    have hSectionEq :
        (fun s : ℝ => K (s, ξ))
          =
        (fun s : ℝ => V (s, ξ) + Z (s, ξ)) := by
      funext s
      exact congrFun hKernelEq (s, ξ)

    have hFullξ :
        Integrable
          (fun s : ℝ => K (s, ξ))
          μt := by
      rw [hSectionEq]
      exact hVξ.add hZξ

    have hFullNorm :
        Integrable
          (fun s : ℝ => ‖K (s, ξ)‖)
          μt :=
      hFullξ.norm

    have hSumNorm :
        Integrable
          (fun s : ℝ =>
            ‖V (s, ξ)‖ + ‖Z (s, ξ)‖)
          μt :=
      hVξ.norm.add hZξ.norm

    rw [hWeightedNorm]

    change
      ‖∫ s : ℝ, K (s, ξ) ∂μt‖
        ≤
      (∫ s : ℝ, ‖V (s, ξ)‖ ∂μt) +
        ∫ s : ℝ, ‖Z (s, ξ)‖ ∂μt

    calc
      ‖∫ s : ℝ, K (s, ξ) ∂μt‖
          ≤
        ∫ s : ℝ, ‖K (s, ξ)‖ ∂μt :=
        norm_integral_le_integral_norm _
      _ ≤
        ∫ s : ℝ,
          (‖V (s, ξ)‖ + ‖Z (s, ξ)‖)
          ∂μt := by
        exact
          integral_mono
            hFullNorm
            hSumNorm
            (fun s => by
              have hsEq :
                  K (s, ξ) = V (s, ξ) + Z (s, ξ) :=
                congrFun hSectionEq s
              rw [hsEq]
              exact norm_add_le (V (s, ξ)) (Z (s, ξ)))
      _ =
        (∫ s : ℝ, ‖V (s, ξ)‖ ∂μt) +
          ∫ s : ℝ, ‖Z (s, ξ)‖ ∂μt := by
        rw [integral_add hVξ.norm hZξ.norm]

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ *
            ‖h3SelectedDuhamelTailRawFourierAmplitude
              ν A t hν U₀ hA hU₀ i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ((∫ s : ℝ, ‖V (s, ξ)‖ ∂μt) +
          ∫ s : ℝ, ‖Z (s, ξ)‖ ∂μt) :=
    integral_mono_ae hTarget hMajor hDom

  have hVSwap :
      (∫ ξ : H3FourierPoint3,
          ∫ s : ℝ, ‖V (s, ξ)‖ ∂μt)
        =
      ∫ s : ℝ,
        ∫ ξ : H3FourierPoint3, ‖V (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
        ∂μt := by
    exact
      (MeasureTheory.integral_integral_swap
        (f := fun s : ℝ => fun ξ : H3FourierPoint3 => ‖V (s, ξ)‖)
        hVProd.norm).symm

  have hVBudget :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3, ‖V (s, ξ)‖
          ∂(volume : Measure H3FourierPoint3)
        ∂μt)
        ≤
      h3SelectedDuhamelTailNineQuarterVariationBudget ν A t := by
    dsimp only [V, μt]
    exact
      h3SelectedDuhamelTailNineQuarterVariationComplexKernel_iteratedNormIntegral_le
        hν U₀ hA hU₀ ht htR i

  have hVFrequencyBudget :
      (∫ ξ : H3FourierPoint3,
          ∫ s : ℝ, ‖V (s, ξ)‖ ∂μt)
        ≤
      h3SelectedDuhamelTailNineQuarterVariationBudget ν A t := by
    rw [hVSwap]
    exact hVBudget

  have hZBudget :
      (∫ ξ : H3FourierPoint3,
          ∫ s : ℝ, ‖Z (s, ξ)‖ ∂μt)
        ≤
      h3SelectedDuhamelTailNineQuarterFrozenBudget ν A t := by
    dsimp only [Z, μt]
    exact
      h3SelectedDuhamelTailNineQuarterFrozenComplexKernel_iteratedNormIntegral_le
        hν U₀ hA hU₀ ht htR i

  unfold h3SelectedDuhamelTailNineQuarterBudget

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ((∫ s : ℝ, ‖V (s, ξ)‖ ∂μt) +
          ∫ s : ℝ, ‖Z (s, ξ)‖ ∂μt) :=
      hIntegral
    _ =
      (∫ ξ : H3FourierPoint3,
          ∫ s : ℝ, ‖V (s, ξ)‖ ∂μt)
        +
      ∫ ξ : H3FourierPoint3,
        ∫ s : ℝ, ‖Z (s, ξ)‖ ∂μt := by
      rw [integral_add hVOuter hZOuter]
    _ ≤
      h3SelectedDuhamelTailNineQuarterVariationBudget ν A t +
        h3SelectedDuhamelTailNineQuarterFrozenBudget ν A t :=
      add_le_add hVFrequencyBudget hZBudget

end
end Euclidean
end Bridge
end PrimeTensor
