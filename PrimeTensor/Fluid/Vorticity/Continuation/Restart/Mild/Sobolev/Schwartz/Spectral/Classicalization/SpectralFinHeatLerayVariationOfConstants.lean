import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpectralFinHeatLerayModeVariationOfConstants

/-!
# Classicalization: all-frequency finite H³ heat-Leray variation of constants

`SpectralFinHeatLerayModeVariationOfConstants` gives the concrete retarded
formula at one fixed Fourier frequency, with the nonlinear term already
identified as `h3RawFinLerayOuterProductDivergence`.

This file packages that theorem simultaneously over the whole H³ Fourier
frequency space and all three velocity coordinates.

No new analytic hypothesis is introduced.  The result is now an equality of
raw Fourier-amplitude functions

    Fin 3 → H3FourierPoint3 → ℂ,

which is the interface needed by the next Duhamel-representative bridge.
That next bridge can identify the retarded scalar integral with the deweighted
representative of `h3SpectralFinHeatLerayDuhamel`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

/-- Concrete heat-Leray variation of constants simultaneously over every
Fourier frequency and every finite velocity coordinate. -/
theorem h3FinHeatLerayVariationOfConstants_retarded
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
        ∫ s in (0 : ℝ)..t,
          h3HeatFourierSymbol ν (t - s) ξ *
            h3RawFinLerayOuterProductDivergence
              (W s) (W s) i ξ) := by
  funext i ξ

  have h :=
    h3FinHeatLerayModeVariationOfConstants_retarded
      ht
      ξ
      W
      (hFContinuous ξ)
      (hODE ξ)
      (hWeightedForcing ξ)

  simpa using congrFun h i

/-- The same all-frequency identity with the retarded heat term and nonlinear
Duhamel term displayed on the left. -/
theorem h3FinHeatLerayVariationOfConstants_retarded_sub
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
        ∫ s in (0 : ℝ)..t,
          h3HeatFourierSymbol ν (t - s) ξ *
            h3RawFinLerayOuterProductDivergence
              (W s) (W s) i ξ)
      =
    (fun i : Fin 3 =>
      fun ξ : H3FourierPoint3 =>
        h3SpectralScalarRawFourier (W t i) ξ) := by
  funext i ξ

  have h :=
    h3FinHeatLerayModeVariationOfConstants_retarded_sub
      ht
      ξ
      W
      (hFContinuous ξ)
      (hODE ξ)
      (hWeightedForcing ξ)

  simpa using congrFun h i

end

end Euclidean
end Bridge
end PrimeTensor
