import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpectralFinHeatLerayDuhamelRawFourierLocalProduct
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Classicalization: a.e. raw Fourier representative of the general Duhamel state

The general Duhamel state has now been linked through four quotient-safe
layers:

* exact H³ deweighting of the actual Banach-valued Duhamel state;
* a Bochner source-time integral of Fourier `L²` kernels;
* explicit almost-everywhere raw Fourier representatives of each source slice;
* genuine product integrability of the open retarded kernel on
  `Ioo 0 t × S` for every measurable finite-measure frequency set `S`.

This file closes the representation bridge.

Define the explicit raw Fourier Duhamel amplitude by integrating the open
retarded kernel in source time:

    ξ ↦ ∫_{Ioo 0 t} H_{t-s}(ξ) N(U(s),V(s))(ξ) ds.

Local product integrability permits Fubini on every finite-measure frequency
set.  The endpoint-safe interval integral from the quotient-side pairing
checkpoint agrees with the open-interval kernel integral because the endpoints
are Lebesgue-null.  Hence the actual deweighted `L²` Duhamel state and the
explicit source-integrated amplitude have equal set integrals on every
measurable finite-measure set.

Sigma-finite uniqueness then identifies them almost everywhere.

No fixed-frequency evaluation of an `L²` equivalence class is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SpectralFinHeatLerayDuhamelRawFourierLocalFubini
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit source-integrated raw Fourier amplitude of the general heat--Leray
Duhamel term. -/
noncomputable def h3SpectralFinHeatLerayDuhamelRawFourierAmplitude
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  ∫ s in Set.Ioo (0 : ℝ) t,
    h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
      ν t U V i (s, ξ)

/-- Local Fubini swaps source time and frequency on every measurable
finite-measure frequency set.  The source-time inner integral is exactly the
explicit general raw Fourier Duhamel amplitude. -/
theorem h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel_local_integral_swap
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (i : Fin 3)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hμS : (volume : Measure H3FourierPoint3) S ≠ ∞) :
    (∫ s in (0 : ℝ)..t,
        ∫ ξ in S,
          h3SpectralFinHeatLerayDuhamelRawFourierIntegrand
            ν t U V i s ξ)
      =
    ∫ ξ in S,
      h3SpectralFinHeatLerayDuhamelRawFourierAmplitude
        ν t U V i ξ := by
  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) t)

  let f : ℝ → H3FourierPoint3 → ℂ :=
    fun s ξ =>
      h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
        ν t U V i (s, ξ)

  have hInt :
      Integrable
        (Function.uncurry f)
        (μt.prod
          ((volume : Measure H3FourierPoint3).restrict S)) := by
    dsimp only [Function.uncurry, f, μt]
    exact
      h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel_local_product_integrable
        (ν := ν) (t := t) (MU := MU) (MV := MV)
        hν ht hMU hMV U V
        hUcont hVcont hU hV i S hS hμS

  have hSwap :=
    integral_integral_swap
      (μ := μt)
      (ν := ((volume : Measure H3FourierPoint3).restrict S))
      (f := f)
      hInt

  have hSwapExpanded :
      (∫ s in Set.Ioo (0 : ℝ) t,
          ∫ ξ in S,
            h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
              ν t U V i (s, ξ))
        =
      ∫ ξ in S,
        ∫ s in Set.Ioo (0 : ℝ) t,
          h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
            ν t U V i (s, ξ) := by
    simpa only [f, μt] using hSwap

  calc
    (∫ s in (0 : ℝ)..t,
        ∫ ξ in S,
          h3SpectralFinHeatLerayDuhamelRawFourierIntegrand
            ν t U V i s ξ)
        =
      ∫ s in Set.Ioo (0 : ℝ) t,
        ∫ ξ in S,
          h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
            ν t U V i (s, ξ) := by
      rw [intervalIntegral.integral_of_le ht]
      rw [← restrict_Ioo_eq_restrict_Ioc]
      apply integral_congr_ae
      change
        ∀ᵐ s ∂(volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) t),
          (∫ ξ in S,
            h3SpectralFinHeatLerayDuhamelRawFourierIntegrand
              ν t U V i s ξ)
            =
          ∫ ξ in S,
            h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
              ν t U V i (s, ξ)
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards with s hs
      have hEq :=
        h3SpectralFinHeatLerayDuhamelRawFourierIntegrand_eq_openKernel_of_mem_Ioo
          (ν := ν) (t := t) U V i hs
      apply setIntegral_congr_ae hS
      exact
        Filter.Eventually.of_forall
          (fun ξ _ => congrFun hEq ξ)
    _ =
      ∫ ξ in S,
        ∫ s in Set.Ioo (0 : ℝ) t,
          h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
            ν t U V i (s, ξ) :=
      hSwapExpanded
    _ =
      ∫ ξ in S,
        h3SpectralFinHeatLerayDuhamelRawFourierAmplitude
          ν t U V i ξ := by
      rfl

/-- The explicit general raw Fourier Duhamel amplitude is integrable on every
measurable finite-measure frequency set. -/
theorem h3SpectralFinHeatLerayDuhamelRawFourierAmplitude_integrableOn_finite
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (i : Fin 3)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hμS : (volume : Measure H3FourierPoint3) S ≠ ∞) :
    IntegrableOn
      (h3SpectralFinHeatLerayDuhamelRawFourierAmplitude
        ν t U V i)
      S
      (volume : Measure H3FourierPoint3) := by
  have hProd :=
    h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel_local_product_integrable
      (ν := ν) (t := t) (MU := MU) (MV := MV)
      hν ht hMU hMV U V
      hUcont hVcont hU hV i S hS hμS

  have hOuter := hProd.integral_prod_right

  unfold h3SpectralFinHeatLerayDuhamelRawFourierAmplitude
  exact hOuter

/-- The actual deweighted general Duhamel Fourier `L²` state is integrable on
every measurable finite-measure frequency set. -/
theorem h3SpectralFinHeatLerayDuhamel_rawFourierL2_integrableOn_finite
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hμS : (volume : Measure H3FourierPoint3) S ≠ ∞) :
    IntegrableOn
      (fun ξ : H3FourierPoint3 =>
        ((h3SpectralScalarRawFourierL2
            (h3SpectralFinHeatLerayDuhamel
              ν t hν U V i) : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)
      S
      (volume : Measure H3FourierPoint3) := by
  exact
    integrableOn_Lp_of_measure_ne_top
      (h3SpectralScalarRawFourierL2
        (h3SpectralFinHeatLerayDuhamel
          ν t hν U V i))
      (by norm_num)
      hμS

/-- On every measurable finite-measure frequency set, the actual deweighted
general Duhamel `L²` state and the explicit source-integrated raw Fourier
amplitude have the same set integral. -/
theorem setIntegral_h3SpectralFinHeatLerayDuhamel_rawFourierL2_eq_rawAmplitude
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (i : Fin 3)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hμS : (volume : Measure H3FourierPoint3) S ≠ ∞) :
    (∫ ξ in S,
      ((h3SpectralScalarRawFourierL2
          (h3SpectralFinHeatLerayDuhamel
            ν t hν U V i) : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ)
      =
    ∫ ξ in S,
      h3SpectralFinHeatLerayDuhamelRawFourierAmplitude
        ν t U V i ξ := by
  calc
    (∫ ξ in S,
      ((h3SpectralScalarRawFourierL2
          (h3SpectralFinHeatLerayDuhamel
            ν t hν U V i) : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ)
        =
      ∫ s in (0 : ℝ)..t,
        ∫ ξ in S,
          h3SpectralFinHeatLerayDuhamelRawFourierIntegrand
            ν t U V i s ξ :=
      setIntegral_h3SpectralFinHeatLerayDuhamel_rawFourierL2_eq_intervalIntegral
        hν ht hMU hMV U V
        hUcont hVcont hU hV i S hS hμS
    _ =
      ∫ ξ in S,
        h3SpectralFinHeatLerayDuhamelRawFourierAmplitude
          ν t U V i ξ :=
      h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel_local_integral_swap
        hν ht hMU hMV U V
        hUcont hVcont hU hV i S hS hμS

/-- The explicit source-integrated raw Fourier amplitude is an
almost-everywhere representative of exact H³ deweighting of the actual general
heat--Leray Duhamel state. -/
theorem h3SpectralFinHeatLerayDuhamel_rawFourierL2_ae_eq_rawAmplitude
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (i : Fin 3) :
    (((h3SpectralScalarRawFourierL2
          (h3SpectralFinHeatLerayDuhamel
            ν t hν U V i) : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ))
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SpectralFinHeatLerayDuhamelRawFourierAmplitude
      ν t U V i := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite

  · intro S hS hμS
    exact
      h3SpectralFinHeatLerayDuhamel_rawFourierL2_integrableOn_finite
        hν U V i S hS hμS.ne

  · intro S hS hμS
    exact
      h3SpectralFinHeatLerayDuhamelRawFourierAmplitude_integrableOn_finite
        hν ht hMU hMV U V
        hUcont hVcont hU hV i S hS hμS.ne

  · intro S hS hμS
    exact
      setIntegral_h3SpectralFinHeatLerayDuhamel_rawFourierL2_eq_rawAmplitude
        hν ht hMU hMV U V
        hUcont hVcont hU hV i S hS hμS.ne

end

end Euclidean
end Bridge
end PrimeTensor
