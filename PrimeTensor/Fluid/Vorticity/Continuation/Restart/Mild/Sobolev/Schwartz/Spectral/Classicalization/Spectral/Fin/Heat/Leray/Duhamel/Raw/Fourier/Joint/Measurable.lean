import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Fin.Heat.Leray.Duhamel.Raw.Fourier.Pairing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.KernelMeasurable

/-!
# Classicalization: joint measurability of the general raw Fourier Duhamel kernel

The quotient-safe pairing checkpoint reduces the remaining representative
problem to a source-time/frequency Fubini argument.  That argument needs the
explicit raw retarded kernel to be jointly measurable for arbitrary continuous
spectral input paths, not only for the previously selected restart path.

The raw finite divergence is already jointly continuous in both H³ velocity
inputs and frequency.  The Leray multiplier is measurable in frequency, so
composing the continuous input paths with source time gives joint
measurability of the full raw Leray forcing.  Multiplication by the jointly
continuous retarded heat symbol then gives the general open Duhamel kernel.

On the strict source-time interval `Ioo 0 t`, this open kernel is exactly the
endpoint-safe raw Fourier integrand introduced by the representative
checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SpectralFinHeatLerayDuhamelRawFourierJointMeasurable
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Along arbitrary continuous spectral paths, the raw finite Leray forcing is
jointly measurable in source time and Fourier frequency. -/
theorem measurable_h3RawFinLerayOuterProductDivergence_continuousPaths_joint
    (U V : ℝ → H3SpectralFinVectorState)
    (hU : Continuous U)
    (hV : Continuous V)
    (i : Fin 3) :
    Measurable
      (fun p : ℝ × H3FourierPoint3 =>
        h3RawFinLerayOuterProductDivergence
          (U p.1) (V p.1) i p.2) := by
  have hUs :
      Continuous
        (fun p : ℝ × H3FourierPoint3 =>
          U p.1) :=
    hU.comp continuous_fst

  have hVs :
      Continuous
        (fun p : ℝ × H3FourierPoint3 =>
          V p.1) :=
    hV.comp continuous_fst

  have hInput :
      Continuous
        (fun p : ℝ × H3FourierPoint3 =>
          (U p.1, (V p.1, p.2))) := by
    exact
      Continuous.prodMk hUs
        (Continuous.prodMk hVs continuous_snd)

  unfold h3RawFinLerayOuterProductDivergence

  apply Finset.measurable_sum
  intro k hk

  have hLeray :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3LerayCoefficient p.2 i k) := by
    exact
      (measurable_h3LerayCoefficient i k).comp measurable_snd

  have hDiv :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3RawFinOuterProductDivergence
            (U p.1) (V p.1) k p.2) := by
    exact
      ((continuous_h3RawFinOuterProductDivergence_joint k).comp
        hInput).measurable

  exact hLeray.mul hDiv

/-- Raw retarded heat--Leray kernel for arbitrary spectral input paths, before
the endpoint-safe source-time convention is applied. -/
noncomputable def h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (p : ℝ × H3FourierPoint3) : ℂ :=
  h3HeatFourierSymbol ν (t - p.1) p.2 *
    h3RawFinLerayOuterProductDivergence
      (U p.1) (V p.1) i p.2

/-- The general raw retarded heat--Leray kernel is jointly measurable whenever
both spectral input paths are continuous. -/
theorem measurable_h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (hU : Continuous U)
    (hV : Continuous V)
    (i : Fin 3) :
    Measurable
      (h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
        ν t U V i) := by
  unfold h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel

  have hHeat :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3HeatFourierSymbol ν (t - p.1) p.2) :=
    (continuous_h3HeatFourierSymbol_retarded ν t).measurable

  have hForcing :=
    measurable_h3RawFinLerayOuterProductDivergence_continuousPaths_joint
      U V hU hV i

  exact hHeat.mul hForcing

/-- On the strict Duhamel source-time interval, the endpoint-safe raw Fourier
integrand is literally the jointly measurable open retarded kernel. -/
theorem h3SpectralFinHeatLerayDuhamelRawFourierIntegrand_eq_openKernel_of_mem_Ioo
    {ν t s : ℝ}
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (hs : s ∈ Set.Ioo (0 : ℝ) t) :
    (fun ξ : H3FourierPoint3 =>
      h3SpectralFinHeatLerayDuhamelRawFourierIntegrand
        ν t U V i s ξ)
      =
    (fun ξ : H3FourierPoint3 =>
      h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
        ν t U V i (s, ξ)) := by
  have hlag : 0 < t - s := sub_pos.mpr hs.2

  funext ξ

  unfold h3SpectralFinHeatLerayDuhamelRawFourierIntegrand
  rw [dif_pos hlag]
  unfold h3SpectralFinHeatLerayDuhamelRawFourierOpenKernel
  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
  rfl

end

end Euclidean
end Bridge
end PrimeTensor
