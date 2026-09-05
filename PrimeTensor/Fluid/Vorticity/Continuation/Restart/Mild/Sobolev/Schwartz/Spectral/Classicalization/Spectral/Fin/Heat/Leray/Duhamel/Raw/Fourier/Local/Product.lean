import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Fin.Heat.Leray.Duhamel.Raw.Fourier.Local.Slice
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Classicalization: local product integrability of the general raw Fourier Duhamel kernel

`SpectralFinHeatLerayDuhamelRawFourierLocalSlice` proves the exact
finite-measure `L² -> L¹` estimate for every strict source-time slice of the
general jointly measurable retarded kernel.

This file integrates that estimate in source time.

For a measurable frequency set `S` of finite measure, let

    G(s) = raw Fourier `L²` Duhamel source slice.

The already-proved Bochner interval integrability of `G` implies integrability
of `s ↦ ‖G(s)‖` on `Ioo 0 t`.  The finite-set slice estimate gives

    ∫_S ‖K(s,ξ)‖ dξ
      ≤ ‖1_S‖₂ ‖G(s)‖₂.

Joint measurability supplies the remaining hypothesis of the product
integrability criterion.  Consequently the explicit general raw Fourier
Duhamel kernel is genuinely integrable on

    Ioo 0 t × S.

This is the precise Fubini hypothesis needed to swap source time and frequency
locally in the next checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SpectralFinHeatLerayDuhamelRawFourierLocalProduct
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The explicit general raw Fourier Duhamel kernel is genuinely integrable on
the restricted source-time/frequency product over every measurable
finite-measure frequency set. -/
theorem h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel_local_product_integrable
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
    Integrable
      (h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
        ν t U V i)
      (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) t)).prod
        ((volume : Measure H3FourierPoint3).restrict S)) := by
  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) t)

  let μS : Measure H3FourierPoint3 :=
    (volume : Measure H3FourierPoint3).restrict S

  let G : ℝ → H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand
      ν t hν U V i

  let C : ℝ :=
    ‖indicatorConstLp
        (μ := (volume : Measure H3FourierPoint3))
        2 hS hμS (1 : ℝ)‖

  have hKMeas :
      AEStronglyMeasurable
        (h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
          ν t U V i)
        (μt.prod μS) := by
    exact
      (measurable_h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
        ν t U V hUcont hVcont i).aestronglyMeasurable

  have hSlices :
      ∀ᵐ s ∂μt,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
              ν t U V i (s, ξ))
          μS := by
    dsimp only [μt, μS]
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    exact
      h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel_integrableOn_of_mem_Ioo
        (t := t) (s := s) hν U V i hs S hS hμS

  have hGInterval :
      IntervalIntegrable
        G
        volume
        0
        t := by
    dsimp only [G]
    exact
      h3SpectralFinHeatLerayDuhamelRawFourierL2Integrand_intervalIntegrable
        (ν := ν) (t := t) (MU := MU) (MV := MV)
        hν ht hMU hMV U V
        hUcont hVcont hU hV i

  have hGOpen :
      Integrable G μt := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht] at hGInterval
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
            ‖h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
              ν t U V i (s, ξ)‖
            ∂μS)
        μt := by
    exact hKMeas.norm.integral_prod_right'

  have hOuter :
      Integrable
        (fun s : ℝ =>
          ∫ ξ : H3FourierPoint3,
            ‖h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
              ν t U V i (s, ξ)‖
            ∂μS)
        μt := by
    refine hMajor.mono' hOuterMeas ?_

    dsimp only [μt] at *
    rw [ae_restrict_iff' measurableSet_Ioo]

    filter_upwards with s hs

    have hBound :=
      integral_norm_h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel_le_indicator_norm_mul_rawFourierL2
        (t := t) (s := s) hν U V i hs S hS hμS

    have hOuterNonneg :
        0 ≤
          ∫ ξ : H3FourierPoint3,
            ‖h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
              ν t U V i (s, ξ)‖
            ∂((volume : Measure H3FourierPoint3).restrict S) :=
      integral_nonneg_of_ae
        (Eventually.of_forall
          (fun ξ =>
            norm_nonneg
              (h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
                ν t U V i (s, ξ))))

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
