import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.MomentSource
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NamedSecond

/-!
# Fréchet endpoint induction: generic terminal-tail moment transfer

`MomentSource` closes the source-time/Fubini estimate for an arbitrary output
moment `p`.  This file performs the next purely measure-theoretic step once.

For the selected terminal half `(t/2,t)`, define

    A_p(ξ) = ∫ K_p(s,ξ) ds,

where `K_p` is the generic weighted selected Duhamel source kernel.  Since the
radial weight is independent of source time,

    A_p(ξ)
      =
    w_p(ξ) T(ξ),

with `T` the actual raw selected terminal-tail Fourier amplitude.

Hence product-space integrability of `K_p` gives an integrable `p` moment of
the raw tail amplitude.  The same a.e. representative identity then transfers
that result to the quotient-safe named terminal-tail `L²` state used by the
midpoint Duhamel decomposition.

No named Fourier exponent occurs in this file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFrechetInductionMomentTail
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Source-time integral of the selected generic weighted terminal-tail
kernel. -/
noncomputable def h3SelectedDuhamelTailMomentFourierAmplitude
    (p ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  ∫ s in Set.Ioo (t / 2) t,
    h3SelectedDuhamelMomentComplexKernel
      p ν A t hν U₀ hA hU₀ i (s, ξ)

/-- Product-space integrability of the generic weighted source kernel on the
terminal half implies frequency integrability of its source-time integral. -/
theorem h3SelectedDuhamelTailMomentFourierAmplitude_integrable_of_product
    {p ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (hProd :
      Integrable
        (h3SelectedDuhamelMomentComplexKernel
          p ν A t hν U₀ hA hU₀ i)
        (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
          (volume : Measure H3FourierPoint3))) :
    Integrable
      (h3SelectedDuhamelTailMomentFourierAmplitude
        p ν A t hν U₀ hA hU₀ i)
      (volume : Measure H3FourierPoint3) := by
  have hOuter := hProd.integral_prod_right

  unfold h3SelectedDuhamelTailMomentFourierAmplitude
  exact hOuter

/-- Pulling the generic radial weight through source time identifies the
weighted source integral with the weight times the actual raw terminal-tail
amplitude. -/
theorem h3SelectedDuhamelTailMomentFourierAmplitude_eq_weight_mul_raw
    {p ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3SelectedDuhamelTailMomentFourierAmplitude
        p ν A t hν U₀ hA hU₀ i ξ
      =
    ((h3FourierMomentWeight p ξ : ℝ) : ℂ) *
      h3SelectedDuhamelTailRawFourierAmplitude
        ν A t hν U₀ hA hU₀ i ξ := by
  unfold
    h3SelectedDuhamelTailMomentFourierAmplitude
    h3SelectedDuhamelMomentComplexKernel
    h3SelectedDuhamelTailRawFourierAmplitude

  change
    (∫ s in Set.Ioo (t / 2) t,
      ((h3FourierMomentWeight p ξ : ℝ) : ℂ) *
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ))
      =
    ((h3FourierMomentWeight p ξ : ℝ) : ℂ) *
      ∫ s in Set.Ioo (t / 2) t,
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ)

  rw [integral_const_mul]

/-- Product-space integrability of the generic weighted source kernel gives an
integrable generic moment of the actual raw selected terminal-tail amplitude. -/
theorem h3SelectedDuhamelTailRawFourierAmplitude_moment_integrable_of_product
    {p ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (hProd :
      Integrable
        (h3SelectedDuhamelMomentComplexKernel
          p ν A t hν U₀ hA hU₀ i)
        (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
          (volume : Measure H3FourierPoint3))) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight p ξ *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hWeighted :=
    h3SelectedDuhamelTailMomentFourierAmplitude_integrable_of_product
      hν U₀ hA hU₀ i hProd

  have hNorm := hWeighted.norm

  refine hNorm.congr ?_
  filter_upwards with ξ

  have hWeight0 :
      0 ≤ h3FourierMomentWeight p ξ :=
    h3FourierMomentWeight_nonneg p ξ

  rw [
    h3SelectedDuhamelTailMomentFourierAmplitude_eq_weight_mul_raw
      hν U₀ hA hU₀ i ξ,
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hWeight0
  ]

/-- The generic raw terminal-tail moment is bounded by the iterated norm
integral of the weighted source kernel. -/
theorem integral_moment_h3SelectedDuhamelTailRawFourierAmplitude_le_iteratedNorm
    {p ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (hProd :
      Integrable
        (h3SelectedDuhamelMomentComplexKernel
          p ν A t hν U₀ hA hU₀ i)
        (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
          (volume : Measure H3FourierPoint3))) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖)
      ≤
    ∫ s : ℝ,
      ∫ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelMomentComplexKernel
          p ν A t hν U₀ hA hU₀ i (s, ξ)‖
      ∂(volume : Measure H3FourierPoint3)
    ∂((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)) := by
  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)

  let Z : ℝ × H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelMomentComplexKernel
      p ν A t hν U₀ hA hU₀ i

  let M : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ∫ s : ℝ,
        ‖Z (s, ξ)‖
        ∂μt

  have hWeightedInt :
      Integrable
        (h3SelectedDuhamelTailMomentFourierAmplitude
          p ν A t hν U₀ hA hU₀ i)
        (volume : Measure H3FourierPoint3) :=
    h3SelectedDuhamelTailMomentFourierAmplitude_integrable_of_product
      hν U₀ hA hU₀ i hProd

  have hWeightedNormInt := hWeightedInt.norm

  have hMInt :
      Integrable M
        (volume : Measure H3FourierPoint3) := by
    dsimp only [M, Z, μt]
    exact hProd.integral_norm_prod_right

  have hPointwise :
      ∀ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelTailMomentFourierAmplitude
            p ν A t hν U₀ hA hU₀ i ξ‖
          ≤
        M ξ := by
    intro ξ
    calc
      ‖h3SelectedDuhamelTailMomentFourierAmplitude
          p ν A t hν U₀ hA hU₀ i ξ‖
          =
        ‖∫ s : ℝ,
            Z (s, ξ)
            ∂μt‖ := by
          rfl
      _ ≤
        ∫ s : ℝ,
          ‖Z (s, ξ)‖
          ∂μt :=
        norm_integral_le_integral_norm _
      _ =
        M ξ := by
          rfl

  have hWeightedOuterLe :
      (∫ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelTailMomentFourierAmplitude
          p ν A t hν U₀ hA hU₀ i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, M ξ := by
    exact
      integral_mono
        hWeightedNormInt
        hMInt
        hPointwise

  have hSwap :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            ‖Z (s, ξ)‖
          ∂(volume : Measure H3FourierPoint3)
        ∂μt)
        =
      ∫ ξ : H3FourierPoint3,
        ∫ s : ℝ,
          ‖Z (s, ξ)‖
        ∂μt := by
    exact
      MeasureTheory.integral_integral_swap
        (f := fun s : ℝ => fun ξ : H3FourierPoint3 => ‖Z (s, ξ)‖)
        hProd.norm

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelTailMomentFourierAmplitude
          p ν A t hν U₀ hA hU₀ i ξ‖ := by
      apply integral_congr_ae
      filter_upwards with ξ
      have hWeight0 :
          0 ≤ h3FourierMomentWeight p ξ :=
        h3FourierMomentWeight_nonneg p ξ
      rw [
        h3SelectedDuhamelTailMomentFourierAmplitude_eq_weight_mul_raw
          hν U₀ hA hU₀ i ξ,
        norm_mul,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg hWeight0
      ]
    _ ≤
      ∫ ξ : H3FourierPoint3, M ξ :=
      hWeightedOuterLe
    _ =
      ∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖Z (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt :=
      hSwap.symm

/-- A scalar source-time budget immediately bounds the actual raw terminal-tail
generic moment. -/
theorem integral_moment_h3SelectedDuhamelTailRawFourierAmplitude_le_of_budget
    {p ν A t B : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (hProd :
      Integrable
        (h3SelectedDuhamelMomentComplexKernel
          p ν A t hν U₀ hA hU₀ i)
        (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
          (volume : Measure H3FourierPoint3)))
    (hBudget :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelMomentComplexKernel
              p ν A t hν U₀ hA hU₀ i (s, ξ)‖
          ∂(volume : Measure H3FourierPoint3)
        ∂((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)))
        ≤ B) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖)
      ≤
    B := by
  exact
    le_trans
      (integral_moment_h3SelectedDuhamelTailRawFourierAmplitude_le_iteratedNorm
        hν U₀ hA hU₀ i hProd)
      hBudget

/-!
## Quotient-safe named terminal tail
-/

/-- The generic weighted density of the named selected terminal-tail raw
Fourier `L²` state agrees almost everywhere with the explicitly estimated raw
tail amplitude density. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_moment_ae_eq_rawAmplitude
    {p ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (fun ξ : H3FourierPoint3 =>
      h3FourierMomentWeight p ξ *
        ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ‖)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3FourierMomentWeight p ξ *
        ‖h3SelectedDuhamelTailRawFourierAmplitude
          ν A t hν U₀ hA hU₀ i ξ‖) := by
  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  filter_upwards [hRep] with ξ hξ
  rw [hξ]

/-- Product-space integrability of the weighted source kernel transfers to an
integrable generic moment of the exact named terminal-tail `L²` state. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_moment_integrable_of_product
    {p ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (hProd :
      Integrable
        (h3SelectedDuhamelMomentComplexKernel
          p ν A t hν U₀ hA hU₀ i)
        (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
          (volume : Measure H3FourierPoint3))) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight p ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
              (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hAmplitude :=
    h3SelectedDuhamelTailRawFourierAmplitude_moment_integrable_of_product
      hν U₀ hA hU₀ i hProd

  have hEq :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_moment_ae_eq_rawAmplitude
      (p := p) hν U₀ hA hU₀ ht i

  exact hAmplitude.congr hEq.symm

/-- Any quantitative raw-tail generic moment budget transfers unchanged to the
named quotient-safe terminal-tail state. -/
theorem integral_moment_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_le_of_budget
    {p ν A t B : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (hRawBudget :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ *
            ‖h3SelectedDuhamelTailRawFourierAmplitude
              ν A t hν U₀ hA hU₀ i ξ‖)
        ≤ B) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
              (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    B := by
  have hEq :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_moment_ae_eq_rawAmplitude
      (p := p) hν U₀ hA hU₀ ht i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
                (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖ :=
    integral_congr_ae hEq

  exact hIntegralEq.trans_le hRawBudget

end
end Euclidean
end Bridge
end PrimeTensor
