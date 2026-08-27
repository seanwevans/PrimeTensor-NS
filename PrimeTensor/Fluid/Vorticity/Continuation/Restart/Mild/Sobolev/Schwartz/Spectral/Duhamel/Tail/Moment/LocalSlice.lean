import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.SetIntegral

/-!
# Finite-measure `L¹` slices of the selected terminal-tail raw Fourier kernel

The selected terminal-tail source kernel is now represented in Fourier `L²`
for every strictly preterminal source time.

On an arbitrary measurable frequency set of finite measure, the standard
finite-measure embedding `L² ⊂ L¹` therefore makes the raw kernel genuinely
Bochner-integrable.

This is the local slice input needed by the final product-space Fubini step.
The only remaining estimate after this file is to show that the resulting
frequency `L¹` norms are integrable in source time; that will be obtained from
the already-proved interval integrability of the `L²`-valued source kernel.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedTailLocalL1Slice
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every quotient-safe selected-tail Fourier `L²` slice is `L¹` on an
arbitrary measurable finite-measure frequency set. -/
theorem h3SelectedDuhamelTailRawFourierL2Integrand_integrableOn_finite
    {ν A t s : ℝ}
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
        ((h3SelectedDuhamelTailRawFourierL2Integrand
            ν A t hν U₀ hA hU₀ i s : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)
      S
      (volume : Measure H3FourierPoint3) := by
  exact
    integrableOn_Lp_of_measure_ne_top
      (h3SelectedDuhamelTailRawFourierL2Integrand
        ν A t hν U₀ hA hU₀ i s)
      (by norm_num)
      hμS

/-- At every source time in the open terminal half, the explicit raw
heat--Leray kernel is genuinely `L¹` on every measurable finite-measure
frequency set. -/
theorem h3SelectedDuhamelTailComplexKernel_integrableOn_of_mem_Ioo
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
    IntegrableOn
      (fun ξ : H3FourierPoint3 =>
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ))
      S
      (volume : Measure H3FourierPoint3) := by
  have hL2 :=
    h3SelectedDuhamelTailRawFourierL2Integrand_integrableOn_finite
      (t := t) (s := s)
      hν U₀ hA hU₀ i S hS hμS

  have hRep :=
    h3SelectedDuhamelTailRawFourierL2Integrand_ae_of_mem_Ioo
      hν U₀ hA hU₀ i hs

  exact hL2.congr_fun_ae hRep.restrict

/-- The same finite-set slice integrability for the pointwise norm of the raw
kernel. -/
theorem norm_h3SelectedDuhamelTailComplexKernel_integrableOn_of_mem_Ioo
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
    IntegrableOn
      (fun ξ : H3FourierPoint3 =>
        ‖h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ)‖)
      S
      (volume : Measure H3FourierPoint3) :=
  (h3SelectedDuhamelTailComplexKernel_integrableOn_of_mem_Ioo
    hν U₀ hA hU₀ i hs S hS hμS).norm

/-- On finite-measure sets, the norm integral of the explicit raw kernel is
the same as the norm integral of the quotient-safe `L²` representative. -/
theorem integral_norm_h3SelectedDuhamelTailComplexKernel_eq_rawFourierL2
    {ν A t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo (t / 2) t)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S) :
    (∫ ξ in S,
      ‖h3SelectedDuhamelTailComplexKernel
        ν A t hν U₀ hA hU₀ i (s, ξ)‖)
      =
    ∫ ξ in S,
      ‖((h3SelectedDuhamelTailRawFourierL2Integrand
          ν A t hν U₀ hA hU₀ i s : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ‖ := by
  apply setIntegral_congr_ae hS

  have hRep :=
    h3SelectedDuhamelTailRawFourierL2Integrand_ae_of_mem_Ioo
      hν U₀ hA hU₀ i hs

  exact
    hRep.symm.mono
      (fun ξ hξ _ => congrArg norm hξ)

end
end Euclidean
end Bridge
end PrimeTensor
