import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpectralFinHeatLerayDuhamelRawFourierLocalFubini
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpectralFinHeatLerayVariationOfConstants

/-!
# Classicalization: variation of constants with the actual raw Fourier Duhamel amplitude

The general Duhamel representation bridge now identifies exact H³ deweighting
of the Banach-valued Duhamel state with the explicit source-integrated raw
Fourier amplitude almost everywhere.

The fixed-frequency variation-of-constants theorem already contains the same
retarded scalar source integral, but written as an oriented interval integral.

This file aligns those two interfaces.

First, the scalar retarded interval integral is identified exactly with
`h3SpectralFinHeatLerayDuhamelRawFourierAmplitude`; the only difference is the
Lebesgue-null source-time endpoints.

Then the all-frequency heat--Leray variation-of-constants theorem is rewritten
so that its nonlinear term is literally the named raw Fourier Duhamel
amplitude.

This produces the pointwise Fourier identity needed for the subsequent
quotient-safe state reconstruction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

/-- The ordinary retarded scalar interval integral is exactly the explicit raw
Fourier Duhamel amplitude. -/
theorem h3SpectralFinHeatLerayDuhamel_rawIntervalIntegral_eq_rawAmplitude
    {ν t : ℝ}
    (ht : 0 ≤ t)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    (∫ s in (0 : ℝ)..t,
      h3HeatFourierSymbol ν (t - s) ξ *
        h3RawFinLerayOuterProductDivergence
          (U s) (V s) i ξ)
      =
    h3SpectralFinHeatLerayDuhamelRawFourierAmplitude
      ν t U V i ξ := by
  rw [intervalIntegral.integral_of_le ht]
  rw [← restrict_Ioo_eq_restrict_Ioc]
  rfl

/-- All-frequency heat--Leray variation of constants with the nonlinear term
written as the named explicit raw Fourier Duhamel amplitude. -/
theorem h3FinHeatLerayVariationOfConstants_retarded_rawAmplitude
    {ν t : ℝ}
    (ht : 0 ≤ t)
    (W : ℝ → H3SpectralFinVectorState)
    (hFContinuous :
      ∀ ξ : H3FourierPoint3, ∀ i : Fin 3,
        ContinuousOn
          (fun s : ℝ =>
            h3SpectralScalarRawFourier (W s i) ξ)
          (Set.Icc (0 : ℝ) t))
    (hODE :
      ∀ ξ : H3FourierPoint3,
        ∀ s ∈ Set.Ioo (0 : ℝ) t,
          H3FinHeatLerayModeODEAt ν ξ W s)
    (hWeightedForcing :
      ∀ ξ : H3FourierPoint3, ∀ i : Fin 3,
        IntervalIntegrable
          (fun s : ℝ =>
            Real.exp
                (ν * h3FourierGradientSquare ξ * s)
              •
            h3RawFinLerayOuterProductDivergence
              (W s) (W s) i ξ)
          volume
          0
          t) :
    (fun i : Fin 3 =>
      fun ξ : H3FourierPoint3 =>
        h3SpectralScalarRawFourier (W t i) ξ)
      =
    (fun i : Fin 3 =>
      fun ξ : H3FourierPoint3 =>
        h3HeatFourierSymbol ν t ξ *
            h3SpectralScalarRawFourier (W 0 i) ξ
          -
        h3SpectralFinHeatLerayDuhamelRawFourierAmplitude
          ν t W W i ξ) := by
  funext i ξ

  have h :=
    congrFun
      (congrFun
        (h3FinHeatLerayVariationOfConstants_retarded
          ht W hFContinuous hODE hWeightedForcing)
        i)
      ξ

  rw [
    h3SpectralFinHeatLerayDuhamel_rawIntervalIntegral_eq_rawAmplitude
      ht W W i ξ
  ] at h

  exact h

/-- The same all-frequency raw-amplitude identity with the heat term minus the
Duhamel amplitude displayed on the left. -/
theorem h3FinHeatLerayVariationOfConstants_retarded_rawAmplitude_sub
    {ν t : ℝ}
    (ht : 0 ≤ t)
    (W : ℝ → H3SpectralFinVectorState)
    (hFContinuous :
      ∀ ξ : H3FourierPoint3, ∀ i : Fin 3,
        ContinuousOn
          (fun s : ℝ =>
            h3SpectralScalarRawFourier (W s i) ξ)
          (Set.Icc (0 : ℝ) t))
    (hODE :
      ∀ ξ : H3FourierPoint3,
        ∀ s ∈ Set.Ioo (0 : ℝ) t,
          H3FinHeatLerayModeODEAt ν ξ W s)
    (hWeightedForcing :
      ∀ ξ : H3FourierPoint3, ∀ i : Fin 3,
        IntervalIntegrable
          (fun s : ℝ =>
            Real.exp
                (ν * h3FourierGradientSquare ξ * s)
              •
            h3RawFinLerayOuterProductDivergence
              (W s) (W s) i ξ)
          volume
          0
          t) :
    (fun i : Fin 3 =>
      fun ξ : H3FourierPoint3 =>
        h3HeatFourierSymbol ν t ξ *
            h3SpectralScalarRawFourier (W 0 i) ξ
          -
        h3SpectralFinHeatLerayDuhamelRawFourierAmplitude
          ν t W W i ξ)
      =
    (fun i : Fin 3 =>
      fun ξ : H3FourierPoint3 =>
        h3SpectralScalarRawFourier (W t i) ξ) := by
  exact
    (h3FinHeatLerayVariationOfConstants_retarded_rawAmplitude
      ht W hFContinuous hODE hWeightedForcing).symm

end

end Euclidean
end Bridge
end PrimeTensor
