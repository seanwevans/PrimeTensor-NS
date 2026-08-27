import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.LocalProduct
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# A.e. raw Fourier representative of the selected terminal-tail state

The selected terminal tail has now been linked through four layers:

* the actual named deweighted Fourier `L²` state;
* a Bochner source-time integral of quotient-safe Fourier `L²` kernels;
* explicit raw Fourier representatives of every strictly preterminal slice;
* genuine product integrability on `Ioo (t/2,t) × S` for every measurable
  finite-measure frequency set `S`.

This file closes the representation bridge.

Local product integrability permits Fubini on every finite-measure frequency
set.  The source-time inner integral is exactly the explicit raw Fourier
amplitude.  Hence the actual `L²` state and the explicit amplitude have equal
set integrals on every measurable finite-measure set.

Since Euclidean volume is sigma-finite, Mathlib's
`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite` then identifies the two
functions almost everywhere.

No fixed-frequency evaluation of an `L²` equivalence class is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedTailLocalFubini
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Local Fubini swaps source time and frequency on an arbitrary measurable
finite-measure frequency set, and the frequency-outer inner integral is the
explicit selected-tail raw Fourier amplitude. -/
theorem h3SelectedDuhamelTailComplexKernel_local_integral_swap
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
    (∫ s in (t / 2)..t,
        ∫ ξ in S,
          h3SelectedDuhamelTailComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ))
      =
    ∫ ξ in S,
      h3SelectedDuhamelTailRawFourierAmplitude
        ν A t hν U₀ hA hU₀ i ξ := by
  let f : ℝ → H3FourierPoint3 → ℂ :=
    fun s ξ =>
      h3SelectedDuhamelTailComplexKernel
        ν A t hν U₀ hA hU₀ i (s, ξ)

  have hhalf : t / 2 ≤ t := by
    linarith

  have hInt :
      Integrable
        (Function.uncurry f)
        (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
          ((volume : Measure H3FourierPoint3).restrict S)) := by
    dsimp only [Function.uncurry, f]
    exact
      h3SelectedDuhamelTailComplexKernel_local_product_integrable
        hν U₀ hA hU₀ ht i S hS hμS

  have hSwap :=
    integral_integral_swap
      (μ := ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)))
      (ν := ((volume : Measure H3FourierPoint3).restrict S))
      (f := f)
      hInt

  have hSwapExpanded :
      (∫ s in Set.Ioo (t / 2) t,
          ∫ ξ in S,
            h3SelectedDuhamelTailComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ))
        =
      ∫ ξ in S,
        ∫ s in Set.Ioo (t / 2) t,
          h3SelectedDuhamelTailComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) := by
    simpa only [f] using hSwap

  calc
    (∫ s in (t / 2)..t,
        ∫ ξ in S,
          h3SelectedDuhamelTailComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ))
        =
      ∫ s in Set.Ioo (t / 2) t,
        ∫ ξ in S,
          h3SelectedDuhamelTailComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) := by
          rw [intervalIntegral.integral_of_le hhalf]
          rw [← restrict_Ioo_eq_restrict_Ioc]
    _ =
      ∫ ξ in S,
        ∫ s in Set.Ioo (t / 2) t,
          h3SelectedDuhamelTailComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) :=
      hSwapExpanded
    _ =
      ∫ ξ in S,
        h3SelectedDuhamelTailRawFourierAmplitude
          ν A t hν U₀ hA hU₀ i ξ := by
        rfl

/-- The explicit raw Fourier amplitude is integrable on every measurable
finite-measure frequency set. -/
theorem h3SelectedDuhamelTailRawFourierAmplitude_integrableOn_finite
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
    IntegrableOn
      (h3SelectedDuhamelTailRawFourierAmplitude
        ν A t hν U₀ hA hU₀ i)
      S
      (volume : Measure H3FourierPoint3) := by
  have hProd :=
    h3SelectedDuhamelTailComplexKernel_local_product_integrable
      hν U₀ hA hU₀ ht i S hS hμS

  have hOuter := hProd.integral_prod_right

  unfold h3SelectedDuhamelTailRawFourierAmplitude
  exact hOuter

/-- The actual named deweighted selected tail `L²` state is integrable on every
measurable finite-measure frequency set. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_integrableOn_finite
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hμS : (volume : Measure H3FourierPoint3) S ≠ ∞) :
    IntegrableOn
      (fun ξ : H3FourierPoint3 =>
        ((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)
      S
      (volume : Measure H3FourierPoint3) := by
  exact
    integrableOn_Lp_of_measure_ne_top
      (h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
        (t := t) hν U₀ hA hU₀ i)
      (by norm_num)
      hμS

/-- On every measurable finite-measure frequency set, the actual named selected
tail `L²` state and the explicit raw Fourier amplitude have the same set
integral. -/
theorem setIntegral_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_eq_rawAmplitude
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
    (∫ ξ in S,
      ((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
          (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ)
      =
    ∫ ξ in S,
      h3SelectedDuhamelTailRawFourierAmplitude
        ν A t hν U₀ hA hU₀ i ξ := by
  calc
    (∫ ξ in S,
      ((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
          (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ)
        =
      ∫ s in (t / 2)..t,
        ∫ ξ in S,
          h3SelectedDuhamelTailComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) :=
      setIntegral_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_eq_intervalIntegral
        hν U₀ hA hU₀ ht i S hS hμS
    _ =
      ∫ ξ in S,
        h3SelectedDuhamelTailRawFourierAmplitude
          ν A t hν U₀ hA hU₀ i ξ :=
      h3SelectedDuhamelTailComplexKernel_local_integral_swap
        hν U₀ hA hU₀ ht i S hS hμS

/-- The explicit raw Fourier amplitude is an almost-everywhere representative
of the actual named deweighted selected terminal-tail Fourier `L²` state. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_ae_eq_rawAmplitude
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
          (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ))
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SelectedDuhamelTailRawFourierAmplitude
      ν A t hν U₀ hA hU₀ i := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite

  · intro S hS hμS
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_integrableOn_finite
        hν U₀ hA hU₀ i S hS hμS.ne

  · intro S hS hμS
    exact
      h3SelectedDuhamelTailRawFourierAmplitude_integrableOn_finite
        hν U₀ hA hU₀ ht i S hS hμS.ne

  · intro S hS hμS
    exact
      setIntegral_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_eq_rawAmplitude
        hν U₀ hA hU₀ ht i S hS hμS.ne

end
end Euclidean
end Bridge
end PrimeTensor
