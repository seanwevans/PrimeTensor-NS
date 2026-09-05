import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Fin.Heat.Leray.Duhamel.Raw.Fourier.Joint.Measurable
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.LocalProduct

/-!
# Classicalization: finite-measure raw Fourier Duhamel slices

The general raw Fourier Duhamel kernel is now jointly measurable, and its
quotient-safe Fourier `L²` source slices are interval-integrable.

This file supplies the local-in-frequency bridge needed for product
integrability.  On every measurable frequency set `S` of finite measure:

* each quotient-safe Fourier `L²` source slice belongs to `L¹(S)`;
* its explicit endpoint-safe raw representative is therefore integrable on
  `S`;
* on the strict source-time interval, the jointly measurable open retarded
  kernel is integrable on `S`;
* the frequency integral of its pointwise norm agrees with the corresponding
  quotient-safe `L²` representative; and
* finite-measure `L² -> L¹` bounds that norm integral by a fixed indicator norm
  times the `L²` norm of the source slice.

The next checkpoint can integrate this bound in source time to obtain genuine
product integrability on `Ioo 0 t × S`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SpectralFinHeatLerayDuhamelRawFourierLocalSlice
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Every quotient-safe general Duhamel Fourier `L²` source slice is `L¹` on
an arbitrary measurable finite-measure frequency set. -/
theorem h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand_integrableOn_finite
    {ν t s : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hμS : (volume : Measure H3FourierPoint3) S ≠ ∞) :
    IntegrableOn
      (fun ξ : H3FourierPoint3 =>
        ((h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
            ν t hν U V i s : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ)
      S
      (volume : Measure H3FourierPoint3) := by
  exact
    integrableOn_Lp_of_measure_ne_top
      (h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
        ν t hν U V i s)
      (by norm_num)
      hμS

/-- The explicit endpoint-safe raw Fourier representative of every general
Duhamel source slice is integrable on each finite-measure frequency set. -/
theorem h3SpectralFinHeatLerayDuhamelRawFourierIntegrand_integrableOn_finite
    {ν t s : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hμS : (volume : Measure H3FourierPoint3) S ≠ ∞) :
    IntegrableOn
      (fun ξ : H3FourierPoint3 =>
        h3SpectralFinHeatLerayDuhamelRawFourierIntegrand
          ν t U V i s ξ)
      S
      (volume : Measure H3FourierPoint3) := by
  have hL2 :=
    h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand_integrableOn_finite
      (t := t) (s := s) hν U V i S hS hμS

  have hRep :=
    h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand_ae
      (ν := ν) (t := t) hν U V i s

  exact hL2.congr_fun_ae hRep.restrict

/-- On the strict Duhamel source-time interval, the jointly measurable open
retarded raw Fourier kernel is integrable on each finite-measure frequency
set. -/
theorem h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel_integrableOn_of_mem_Ioo
    {ν t s : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo (0 : ℝ) t)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hμS : (volume : Measure H3FourierPoint3) S ≠ ∞) :
    IntegrableOn
      (fun ξ : H3FourierPoint3 =>
        h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
          ν t U V i (s, ξ))
      S
      (volume : Measure H3FourierPoint3) := by
  have hEndpoint :=
    h3SpectralFinHeatLerayDuhamelRawFourierIntegrand_integrableOn_finite
      (t := t) (s := s) hν U V i S hS hμS

  have hEq :=
    h3SpectralFinHeatLerayDuhamelRawFourierIntegrand_eq_openKernel_of_mem_Ioo
      (ν := ν) (t := t) U V i hs

  have hEqAE :
      (fun ξ : H3FourierPoint3 =>
        h3SpectralFinHeatLerayDuhamelRawFourierIntegrand
          ν t U V i s ξ)
        =ᵐ[((volume : Measure H3FourierPoint3).restrict S)]
      (fun ξ : H3FourierPoint3 =>
        h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
          ν t U V i (s, ξ)) :=
    Filter.Eventually.of_forall
      (fun ξ => congrFun hEq ξ)

  exact hEndpoint.congr_fun_ae hEqAE

/-- On a strict source-time slice, the finite-set norm integral of the open
raw kernel is exactly the finite-set norm integral of the quotient-safe
Fourier `L²` representative. -/
theorem integral_norm_h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel_eq_rawFourierL2
    {ν t s : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo (0 : ℝ) t)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S) :
    (∫ ξ in S,
      ‖h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
        ν t U V i (s, ξ)‖)
      =
    ∫ ξ in S,
      ‖((h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
          ν t hν U V i s : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ‖ := by
  have hEq :=
    h3SpectralFinHeatLerayDuhamelRawFourierIntegrand_eq_openKernel_of_mem_Ioo
      (ν := ν) (t := t) U V i hs

  have hRep :=
    h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand_ae
      (ν := ν) (t := t) hν U V i s

  apply setIntegral_congr_ae hS
  exact
    hRep.symm.mono
      (fun ξ hξ _ => by
        rw [← congrFun hEq ξ]
        exact congrArg norm hξ)

/-- Finite-measure `L² -> L¹` control of every strict source-time slice of the
general open raw Fourier Duhamel kernel. -/
theorem integral_norm_h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel_le_indicator_norm_mul_rawFourierL2
    {ν t s : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo (0 : ℝ) t)
    (S : Set H3FourierPoint3)
    (hS : MeasurableSet S)
    (hμS : (volume : Measure H3FourierPoint3) S ≠ ∞) :
    (∫ ξ in S,
      ‖h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
        ν t U V i (s, ξ)‖)
      ≤
    ‖indicatorConstLp
        (μ := (volume : Measure H3FourierPoint3))
        2 hS hμS (1 : ℝ)‖ *
      ‖h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
        ν t hν U V i s‖ := by
  rw [
    integral_norm_h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel_eq_rawFourierL2
      hν U V i hs S hS
  ]

  exact
    setIntegral_norm_fourierL2_le_indicator_norm_mul_norm
      (h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
        ν t hν U V i s)
      S hS hμS

end

end Euclidean
end Bridge
end PrimeTensor
