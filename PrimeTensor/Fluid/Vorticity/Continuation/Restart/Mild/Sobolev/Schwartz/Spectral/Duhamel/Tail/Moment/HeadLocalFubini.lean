import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.HeadStateL2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.LocalFubini

/-!
# A.e. raw Fourier representative of the selected Duhamel head

`HeadStateL2` identifies exact H³ deweighting of the named selected midpoint
head with the Fourier `L²`-valued source-time integral of the long retarded
kernel on `0..t/2`.

`HeadGlobalProduct` independently proves genuine product integrability of the
explicit raw kernel on

    (0,t/2) × H3FourierPoint3.

This file joins those two statements exactly as `LocalFubini` did for the
terminal tail.

For every measurable finite-measure frequency set `S`:

* test the quotient-safe head `L²` state against the indicator of `S`;
* commute the Hilbert pairing through the source-time Bochner integral;
* replace every strict source slice by its explicit raw Fourier representative;
* use the global head product theorem to swap source time and frequency.

Thus the named head `L²` state and the explicit source-integrated head raw
amplitude have equal set integrals on every finite-measure measurable set.
Sigma-finite uniqueness then identifies them almost everywhere.

No new Fourier estimate and no fixed-frequency evaluation of an `L²` class is
introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedHeadLocalFubini
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Pairing the quotient-safe selected head raw Fourier state against any
Fourier `L²` test state commutes through the source-time integral on
`0..t/2`. -/
theorem inner_h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_eq_intervalIntegral_longKernel
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (φ : H3FourierComplexL2) :
    inner ℂ φ
        (h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
          hν U₀ hA hU₀ ht i)
      =
    ∫ s in (0 : ℝ)..(t / 2),
      inner ℂ φ
        (h3SelectedDuhamelTailRawFourierL2Integrand
          ν A t hν U₀ hA hU₀ i s) := by
  rw [
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_eq_intervalIntegral_longKernel
      hν U₀ hA hU₀ ht i
  ]

  have hG :=
    h3SelectedDuhamelHeadRawFourierL2Integrand_intervalIntegrable
      hν U₀ hA hU₀ ht i

  let L :
      H3FourierComplexL2 →L[ℂ] ℂ :=
    innerSL ℂ φ

  have hComm :
      (∫ s in (0 : ℝ)..(t / 2),
        L
          (h3SelectedDuhamelTailRawFourierL2Integrand
            ν A t hν U₀ hA hU₀ i s))
        =
      L
        (∫ s in (0 : ℝ)..(t / 2),
          h3SelectedDuhamelTailRawFourierL2Integrand
            ν A t hν U₀ hA hU₀ i s) :=
    L.intervalIntegral_comp_comm hG

  simpa only [L, innerSL_apply_apply] using hComm.symm

/-- On the strict midpoint head, pairing one quotient-safe source-time `L²`
kernel against a finite-measure indicator gives the set integral of the
explicit raw retarded kernel. -/
theorem inner_indicatorConstLp_h3SelectedDuhamelHeadRawFourierL2Integrand_eq_setIntegral
    {ν A t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo (0 : ℝ) (t / 2))
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

  have hst : s < t := by
    linarith [hs.2, ht]

  have hRep :=
    h3SelectedDuhamelTailRawFourierL2Integrand_ae_of_lt
      hν U₀ hA hU₀ i hst

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

/-- On every measurable finite-measure frequency set, the named deweighted
selected head has the same set integral as the source-time integral of the
explicit raw head kernel. -/
theorem setIntegral_h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_eq_intervalIntegral_longKernel
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
      ((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
          hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ)
      =
    ∫ s in (0 : ℝ)..(t / 2),
      ∫ ξ in S,
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ) := by
  let φ : H3FourierComplexL2 :=
    indicatorConstLp
      (μ := (volume : Measure H3FourierPoint3))
      2 hS hμS (1 : ℂ)

  have hActual :
      inner ℂ φ
          (h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
            hν U₀ hA hU₀ ht i)
        =
      ∫ ξ in S,
        ((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
            hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ := by
    dsimp only [φ]
    exact
      MeasureTheory.L2.inner_indicatorConstLp_one
        hS hμS
        (h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
          hν U₀ hA hU₀ ht i)

  have hPair :=
    inner_h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_eq_intervalIntegral_longKernel
      hν U₀ hA hU₀ ht i φ

  have hhalf : 0 ≤ t / 2 := by
    linarith

  have hOuter :
      (∫ s in (0 : ℝ)..(t / 2),
        inner ℂ φ
          (h3SelectedDuhamelTailRawFourierL2Integrand
            ν A t hν U₀ hA hU₀ i s))
        =
      ∫ s in (0 : ℝ)..(t / 2),
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
      ∀ᵐ s ∂(volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (t / 2)),
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
      inner_indicatorConstLp_h3SelectedDuhamelHeadRawFourierL2Integrand_eq_setIntegral
        hν U₀ hA hU₀ ht i hs S hS hμS

  calc
    (∫ ξ in S,
      ((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
          hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ)
        =
      inner ℂ φ
        (h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
          hν U₀ hA hU₀ ht i) := by
      exact hActual.symm
    _ =
      ∫ s in (0 : ℝ)..(t / 2),
        inner ℂ φ
          (h3SelectedDuhamelTailRawFourierL2Integrand
            ν A t hν U₀ hA hU₀ i s) :=
      hPair
    _ =
      ∫ s in (0 : ℝ)..(t / 2),
        ∫ ξ in S,
          h3SelectedDuhamelTailComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) :=
      hOuter

/-- Restricting the globally integrable head product kernel to any measurable
frequency set preserves integrability, so Fubini swaps source time and
frequency on that set. -/
theorem h3SelectedDuhamelHeadComplexKernel_local_integral_swap
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S) :
    (∫ s in (0 : ℝ)..(t / 2),
        ∫ ξ in S,
          h3SelectedDuhamelTailComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ))
      =
    ∫ ξ in S,
      h3SelectedDuhamelHeadRawFourierAmplitude
        ν A t hν U₀ hA hU₀ i ξ := by
  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (t / 2))

  let f : ℝ → H3FourierPoint3 → ℂ :=
    fun s ξ =>
      h3SelectedDuhamelTailComplexKernel
        ν A t hν U₀ hA hU₀ i (s, ξ)

  have hGlobal :
      Integrable
        (Function.uncurry f)
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [Function.uncurry, f, μt]
    exact
      h3SelectedDuhamelHeadComplexKernel_fubini_integrable_global
        hν U₀ hA hU₀ ht i

  have hInt :
      Integrable
        (Function.uncurry f)
        (μt.prod
          ((volume : Measure H3FourierPoint3).restrict S)) := by
    exact
      Integrable.mono_measure
        hGlobal
        (Measure.prod_mono le_rfl Measure.restrict_le_self)

  have hSwap :=
    integral_integral_swap
      (μ := μt)
      (ν := ((volume : Measure H3FourierPoint3).restrict S))
      (f := f)
      hInt

  have hSwapExpanded :
      (∫ s in Set.Ioo (0 : ℝ) (t / 2),
          ∫ ξ in S,
            h3SelectedDuhamelTailComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ))
        =
      ∫ ξ in S,
        ∫ s in Set.Ioo (0 : ℝ) (t / 2),
          h3SelectedDuhamelTailComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) := by
    simpa only [f, μt] using hSwap

  have hhalf : 0 ≤ t / 2 := by
    linarith

  calc
    (∫ s in (0 : ℝ)..(t / 2),
        ∫ ξ in S,
          h3SelectedDuhamelTailComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ))
        =
      ∫ s in Set.Ioo (0 : ℝ) (t / 2),
        ∫ ξ in S,
          h3SelectedDuhamelTailComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) := by
      rw [intervalIntegral.integral_of_le hhalf]
      rw [← restrict_Ioo_eq_restrict_Ioc]
    _ =
      ∫ ξ in S,
        ∫ s in Set.Ioo (0 : ℝ) (t / 2),
          h3SelectedDuhamelTailComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) :=
      hSwapExpanded
    _ =
      ∫ ξ in S,
        h3SelectedDuhamelHeadRawFourierAmplitude
          ν A t hν U₀ hA hU₀ i ξ := by
      rfl

/-- On every finite-measure measurable frequency set, the actual named selected
head raw Fourier `L²` state and the explicit source-integrated head amplitude
have equal set integrals. -/
theorem setIntegral_h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_eq_rawAmplitude
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
      ((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
          hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ)
      =
    ∫ ξ in S,
      h3SelectedDuhamelHeadRawFourierAmplitude
        ν A t hν U₀ hA hU₀ i ξ := by
  calc
    (∫ ξ in S,
      ((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
          hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ)
        =
      ∫ s in (0 : ℝ)..(t / 2),
        ∫ ξ in S,
          h3SelectedDuhamelTailComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) :=
      setIntegral_h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_eq_intervalIntegral_longKernel
        hν U₀ hA hU₀ ht i S hS hμS
    _ =
      ∫ ξ in S,
        h3SelectedDuhamelHeadRawFourierAmplitude
          ν A t hν U₀ hA hU₀ i ξ :=
      h3SelectedDuhamelHeadComplexKernel_local_integral_swap
        hν U₀ hA hU₀ ht i S hS

/-- The explicit source-time-integrated midpoint-head raw Fourier amplitude is
an almost-everywhere representative of the actual named selected head raw
Fourier `L²` state. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_rawAmplitude
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
          hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ))
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SelectedDuhamelHeadRawFourierAmplitude
      ν A t hν U₀ hA hU₀ i := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite

  · intro S hS hμS
    exact
      integrableOn_Lp_of_measure_ne_top
        (h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
          hν U₀ hA hU₀ ht i)
        (by norm_num)
        hμS.ne

  · intro S hS hμS
    exact
      (h3SelectedDuhamelHeadRawFourierAmplitude_integrable_global
        hν U₀ hA hU₀ ht i).integrableOn

  · intro S hS hμS
    exact
      setIntegral_h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_eq_rawAmplitude
        hν U₀ hA hU₀ ht i S hS hμS.ne

end

end Euclidean
end Bridge
end PrimeTensor
