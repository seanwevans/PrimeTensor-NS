import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.LocalSlice
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Local product integrability of the selected terminal-tail raw Fourier kernel

For an arbitrary measurable finite-measure frequency set `S`, `LocalSlice`
shows that every strictly preterminal source-time slice of the explicit raw
kernel is `L¹(S)`.

This file supplies the missing outer-in-time estimate.

For a Fourier `L²` state `f`, package the real function `ξ ↦ ‖f ξ‖` as an
`L²` state.  Its `L²` norm is exactly `‖f‖`.  Pairing this state against the
constant-one indicator of `S` and applying Hilbert-space Cauchy--Schwarz gives

    ∫_S ‖f(ξ)‖ dξ
      ≤ ‖1_S‖_{L²} ‖f‖_{L²}.

Applying this to the selected source-time `L²` kernel turns the already-proved
Bochner interval integrability in source time into genuine integrability of
the explicit complex kernel on

    Ioo (t/2,t) × S.

This is exactly the product-integrability hypothesis needed for the local
Fubini swap in the next checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedTailLocalProduct
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Real Fourier `L²` package of the pointwise norm of a complex Fourier
`L²` state. -/
noncomputable def h3FourierComplexL2NormState
    (f : H3FourierComplexL2) :
    Lp ℝ 2 (volume : Measure H3FourierPoint3) :=
  (Lp.memLp f).norm.toLp
    (fun ξ : H3FourierPoint3 => ‖f ξ‖)

/-- The real norm-state package has exactly the same `L²` norm as the original
complex state. -/
theorem norm_h3FourierComplexL2NormState
    (f : H3FourierComplexL2) :
    ‖h3FourierComplexL2NormState f‖ = ‖f‖ := by
  unfold h3FourierComplexL2NormState
  rw [Lp.norm_toLp]
  rw [eLpNorm_norm]
  rfl

/-- The norm-state package is represented almost everywhere by the ordinary
pointwise complex norm. -/
theorem h3FourierComplexL2NormState_ae
    (f : H3FourierComplexL2) :
    ((h3FourierComplexL2NormState f :
        Lp ℝ 2 (volume : Measure H3FourierPoint3)) :
      H3FourierPoint3 → ℝ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 => ‖f ξ‖) := by
  unfold h3FourierComplexL2NormState
  exact MemLp.coeFn_toLp (Lp.memLp f).norm

/-- Finite-measure `L² -> L¹` estimate, expressed with the exact `L²` norm of
the constant-one indicator. -/
theorem setIntegral_norm_fourierL2_le_indicator_norm_mul_norm
    (f : H3FourierComplexL2)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hμS : (volume : Measure H3FourierPoint3) S ≠ ∞) :
    (∫ ξ in S, ‖f ξ‖)
      ≤
    ‖indicatorConstLp
        (μ := (volume : Measure H3FourierPoint3))
        2 hS hμS (1 : ℝ)‖ * ‖f‖ := by
  let ψ : Lp ℝ 2 (volume : Measure H3FourierPoint3) :=
    h3FourierComplexL2NormState f

  let φ : Lp ℝ 2 (volume : Measure H3FourierPoint3) :=
    indicatorConstLp
      (μ := (volume : Measure H3FourierPoint3))
      2 hS hμS (1 : ℝ)

  have hInner :
      inner ℝ φ ψ
        =
      ∫ ξ in S, ψ ξ := by
    dsimp only [φ]
    exact
      MeasureTheory.L2.inner_indicatorConstLp_one
        hS hμS ψ

  have hSet :
      (∫ ξ in S, ψ ξ)
        =
      ∫ ξ in S, ‖f ξ‖ := by
    apply setIntegral_congr_ae hS
    have hRep := h3FourierComplexL2NormState_ae f
    exact hRep.mono (fun ξ hξ _ => hξ)

  have hInner' :
      inner ℝ φ ψ
        =
      ∫ ξ in S, ‖f ξ‖ :=
    hInner.trans hSet

  calc
    (∫ ξ in S, ‖f ξ‖)
        ≤
      |∫ ξ in S, ‖f ξ‖| :=
      le_abs_self _
    _ =
      ‖inner ℝ φ ψ‖ := by
        rw [← hInner', Real.norm_eq_abs]
    _ ≤
      ‖φ‖ * ‖ψ‖ :=
      norm_inner_le_norm _ _
    _ =
      ‖indicatorConstLp
          (μ := (volume : Measure H3FourierPoint3))
          2 hS hμS (1 : ℝ)‖ * ‖f‖ := by
        dsimp only [φ, ψ]
        rw [norm_h3FourierComplexL2NormState]

/-- On a finite-measure frequency set, the explicit raw kernel `L¹` norm is
bounded by a fixed indicator norm times the quotient-safe Fourier `L²` norm of
the source-time slice. -/
theorem integral_norm_h3SelectedDuhamelTailComplexKernel_le_indicator_norm_mul_rawFourierL2
    {ν A t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo (t / 2) t)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hμS : (volume : Measure H3FourierPoint3) S ≠ ∞) :
    (∫ ξ in S,
      ‖h3SelectedDuhamelTailComplexKernel
        ν A t hν U₀ hA hU₀ i (s, ξ)‖)
      ≤
    ‖indicatorConstLp
        (μ := (volume : Measure H3FourierPoint3))
        2 hS hμS (1 : ℝ)‖ *
      ‖h3SelectedDuhamelTailRawFourierL2Integrand
        ν A t hν U₀ hA hU₀ i s‖ := by
  rw [
    integral_norm_h3SelectedDuhamelTailComplexKernel_eq_rawFourierL2
      hν U₀ hA hU₀ i hs S hS
  ]

  exact
    setIntegral_norm_fourierL2_le_indicator_norm_mul_norm
      (h3SelectedDuhamelTailRawFourierL2Integrand
        ν A t hν U₀ hA hU₀ i s)
      S hS hμS

/-- The selected explicit raw terminal-tail kernel is genuinely integrable on
the restricted source-time/frequency product over every measurable
finite-measure frequency set. -/
theorem h3SelectedDuhamelTailComplexKernel_local_product_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hμS : (volume : Measure H3FourierPoint3) S ≠ ∞) :
    Integrable
      (h3SelectedDuhamelTailComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
        ((volume : Measure H3FourierPoint3).restrict S)) := by
  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)

  let μS : Measure H3FourierPoint3 :=
    (volume : Measure H3FourierPoint3).restrict S

  let G : ℝ → H3FourierComplexL2 :=
    h3SelectedDuhamelTailRawFourierL2Integrand
      ν A t hν U₀ hA hU₀ i

  let C : ℝ :=
    ‖indicatorConstLp
        (μ := (volume : Measure H3FourierPoint3))
        2 hS hμS (1 : ℝ)‖

  have hKMeas :
      AEStronglyMeasurable
        (h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (μt.prod μS) := by
    exact
      (measurable_h3SelectedDuhamelTailComplexKernel
        hν U₀ hA hU₀ i).aestronglyMeasurable

  have hSlices :
      ∀ᵐ s ∂μt,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3SelectedDuhamelTailComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ))
          μS := by
    dsimp only [μt, μS]
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    exact
      h3SelectedDuhamelTailComplexKernel_integrableOn_of_mem_Ioo
        hν U₀ hA hU₀ i hs S hS hμS

  have hGInterval :
      IntervalIntegrable
        G
        volume
        (t / 2)
        t := by
    dsimp only [G]
    exact
      h3SelectedDuhamelTailRawFourierL2Integrand_intervalIntegrable
        hν U₀ hA hU₀ ht i

  have hhalf : t / 2 ≤ t := by
    linarith

  have hGOpen :
      Integrable G μt := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf] at hGInterval
    dsimp only [μt]
    rw [restrict_Ioo_eq_restrict_Ioc]
    exact hGInterval

  have hMajor :
      Integrable
        (fun s : ℝ => C * ‖G s‖)
        μt :=
    hGOpen.norm.const_mul C

  have hOuterMeas :
      AEStronglyMeasurable
        (fun s : ℝ =>
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelTailComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖
            ∂μS)
        μt := by
    exact hKMeas.norm.integral_prod_right'

  have hOuter :
      Integrable
        (fun s : ℝ =>
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelTailComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖
            ∂μS)
        μt := by
    refine hMajor.mono' hOuterMeas ?_

    dsimp only [μt] at *
    rw [ae_restrict_iff' measurableSet_Ioo]

    filter_upwards with s hs

    have hBound :=
      integral_norm_h3SelectedDuhamelTailComplexKernel_le_indicator_norm_mul_rawFourierL2
        hν U₀ hA hU₀ i hs S hS hμS

    have hOuterNonneg :
        0 ≤
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelTailComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖
            ∂((volume : Measure H3FourierPoint3).restrict S) :=
      integral_nonneg_of_ae
        (Eventually.of_forall
          (fun ξ =>
            norm_nonneg
              (h3SelectedDuhamelTailComplexKernel
                ν A t hν U₀ hA hU₀ i (s, ξ))))

    rw [Real.norm_eq_abs, abs_of_nonneg hOuterNonneg]

    dsimp only [C, G]
    exact hBound

  exact
    (integrable_prod_iff hKMeas).2
      ⟨hSlices, hOuter⟩

end
end Euclidean
end Bridge
end PrimeTensor
