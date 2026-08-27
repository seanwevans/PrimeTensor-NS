import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Representative
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Finite-measure set integrals of the selected terminal-tail raw Fourier state

The selected terminal tail is now identified in three compatible forms:

* an actual deweighted Fourier `L²` state;
* a Bochner interval integral of quotient-safe Fourier `L²` kernels;
* for every strictly preterminal source time, an explicit raw Fourier
  representative of the corresponding `L²` kernel.

This file tests those identities against finite-measure frequency indicators.

For every measurable frequency set `S` of finite measure, the set integral of
the actual deweighted selected tail equals the source-time integral of the
set integral of the explicit raw heat--Leray kernel.

The proof uses `L2.inner_indicatorConstLp_one` and the Hilbert-space pairing
identity from `Pairing`.  The terminal endpoint is removed with the
Lebesgue-null `Ioo`/`Ioc` restriction identity, so no false pointwise statement
at zero heat lag is introduced.

This is the finite-set identity needed by the next local Fubini checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedTailRawFourierL2SetIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Pairing one quotient-safe source-time `L²` kernel against a finite-measure
indicator gives the set integral of the explicit raw kernel. -/
theorem inner_indicatorConstLp_h3SelectedDuhamelTailRawFourierL2Integrand_eq_setIntegral
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
    inner ℂ
        (indicatorConstLp
          (μ := (volume : Measure H3FourierPoint3))
          2 hS hμS (1 : ℂ))
        (h3SelectedDuhamelTailRawFourierL2Integrand
          ν A t hν U₀ hA hU₀ i s)
      =
    ∫ ξ in S,
      h3SelectedDuhamelTailComplexKernel
        ν A t hν U₀ hA hU₀ i (s, ξ) := by
  let φ : H3FourierComplexL2 :=
    indicatorConstLp
      (μ := (volume : Measure H3FourierPoint3))
      2 hS hμS (1 : ℂ)

  have hIndicator :
      inner ℂ φ
          (h3SelectedDuhamelTailRawFourierL2Integrand
            ν A t hν U₀ hA hU₀ i s)
        =
      ∫ ξ in S,
        ((h3SelectedDuhamelTailRawFourierL2Integrand
            ν A t hν U₀ hA hU₀ i s : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ := by
    dsimp only [φ]
    exact
      MeasureTheory.L2.inner_indicatorConstLp_one
        hS hμS
        (h3SelectedDuhamelTailRawFourierL2Integrand
          ν A t hν U₀ hA hU₀ i s)

  have hRep :=
    h3SelectedDuhamelTailRawFourierL2Integrand_ae_of_mem_Ioo
      hν U₀ hA hU₀ i hs

  have hSet :
      (∫ ξ in S,
        ((h3SelectedDuhamelTailRawFourierL2Integrand
            ν A t hν U₀ hA hU₀ i s : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)
        =
      ∫ ξ in S,
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ) := by
    apply setIntegral_congr_ae hS
    exact hRep.mono (fun ξ hξ _ => hξ)

  change
    inner ℂ φ
        (h3SelectedDuhamelTailRawFourierL2Integrand
          ν A t hν U₀ hA hU₀ i s)
      =
    ∫ ξ in S,
      h3SelectedDuhamelTailComplexKernel
        ν A t hν U₀ hA hU₀ i (s, ξ)

  exact hIndicator.trans hSet

/-- On every finite-measure measurable frequency set, the actual deweighted
selected tail has the same set integral as the source-time integral of the
explicit raw terminal-tail kernel. -/
theorem setIntegral_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_eq_intervalIntegral
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
    ∫ s in (t / 2)..t,
      ∫ ξ in S,
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ) := by
  let φ : H3FourierComplexL2 :=
    indicatorConstLp
      (μ := (volume : Measure H3FourierPoint3))
      2 hS hμS (1 : ℂ)

  have hActual :
      inner ℂ φ
          (h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := t) hν U₀ hA hU₀ i)
        =
      ∫ ξ in S,
        ((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ := by
    dsimp only [φ]
    exact
      MeasureTheory.L2.inner_indicatorConstLp_one
        hS hμS
        (h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
          (t := t) hν U₀ hA hU₀ i)

  have hPair :=
    inner_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_eq_intervalIntegral
      hν U₀ hA hU₀ ht i φ

  have hhalf : t / 2 ≤ t := by
    linarith

  have hOuter :
      (∫ s in (t / 2)..t,
        inner ℂ φ
          (h3SelectedDuhamelTailRawFourierL2Integrand
            ν A t hν U₀ hA hU₀ i s))
        =
      ∫ s in (t / 2)..t,
        ∫ ξ in S,
          h3SelectedDuhamelTailComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) := by
    rw [
      intervalIntegral.integral_of_le hhalf,
      intervalIntegral.integral_of_le hhalf
    ]
    rw [← restrict_Ioo_eq_restrict_Ioc]

    apply integral_congr_ae
    change
      ∀ᵐ s ∂(volume : Measure ℝ).restrict (Set.Ioo (t / 2) t),
        inner ℂ φ
            (h3SelectedDuhamelTailRawFourierL2Integrand
              ν A t hν U₀ hA hU₀ i s)
          =
        ∫ ξ in S,
          h3SelectedDuhamelTailComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)

    rw [ae_restrict_iff' measurableSet_Ioo]

    filter_upwards with s hs

    exact
      inner_indicatorConstLp_h3SelectedDuhamelTailRawFourierL2Integrand_eq_setIntegral
        hν U₀ hA hU₀ i hs S hS hμS

  calc
    (∫ ξ in S,
      ((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
          (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ)
        =
      inner ℂ φ
        (h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
          (t := t) hν U₀ hA hU₀ i) := by
            exact hActual.symm
    _ =
      ∫ s in (t / 2)..t,
        inner ℂ φ
          (h3SelectedDuhamelTailRawFourierL2Integrand
            ν A t hν U₀ hA hU₀ i s) :=
      hPair
    _ =
      ∫ s in (t / 2)..t,
        ∫ ξ in S,
          h3SelectedDuhamelTailComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) :=
      hOuter

end
end Euclidean
end Bridge
end PrimeTensor
