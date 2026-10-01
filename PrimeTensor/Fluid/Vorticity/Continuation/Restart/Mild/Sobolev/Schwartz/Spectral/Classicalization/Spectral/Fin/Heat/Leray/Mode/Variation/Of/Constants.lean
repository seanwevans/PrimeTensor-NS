import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Fin.Heat.Mode.Variation.Of.Constants
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.L1

/-!
# Classicalization: finite-vector H³ heat-Leray mode variation of constants

`SpectralFinHeatModeVariationOfConstants` isolates the finite-vector
variation-of-constants mechanism at one Fourier frequency, but leaves both the
evolving Fourier vector and the nonlinear forcing abstract.

This file performs the next exact specialization.  For a spectral path

    W : ℝ → H3SpectralFinVectorState

the evolving Fourier coordinate is the deweighted raw amplitude

    h3SpectralScalarRawFourier (W s i) ξ

and the nonlinear term is the actual finite Leray-projected outer-product
divergence

    h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ.

No new estimate is introduced.  The remaining work for a concrete selected
restart is now isolated to the three expected hypotheses: time continuity of
the raw Fourier coordinate, the projected Fourier-mode ODE, and weighted
time-integrability of the concrete nonlinear forcing.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

/-- The concrete H³ Navier--Stokes Fourier-mode ODE at one frequency, with the
state and Leray-projected quadratic forcing both read directly from a spectral
path. -/
def H3FinHeatLerayModeODEAt
    (ν : ℝ)
    (ξ : H3FourierPoint3)
    (W : ℝ → H3SpectralFinVectorState)
    (s : ℝ) : Prop :=
  H3FinHeatModeODEAt
    ν
    ξ
    (fun r i => h3SpectralScalarRawFourier (W r i) ξ)
    (fun r i =>
      h3RawFinLerayOuterProductDivergence
        (W r) (W r) i ξ)
    s

/-- Once the concrete projected Fourier ODE is available, the finite-vector
variation-of-constants theorem gives the retarded heat formula with the actual
Leray-divergence forcing. -/
theorem h3FinHeatLerayModeVariationOfConstants_retarded
    {ν t : ℝ}
    (ht : 0 ≤ t)
    (ξ : H3FourierPoint3)
    (W : ℝ → H3SpectralFinVectorState)
    (hFContinuous :
      ∀ i : Fin 3,
        ContinuousOn
          (fun s : ℝ =>
            h3SpectralScalarRawFourier (W s i) ξ)
          (Set.Icc (0 : ℝ) t))
    (hODE :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        H3FinHeatLerayModeODEAt ν ξ W s)
    (hWeightedForcing :
      ∀ i : Fin 3,
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
      h3SpectralScalarRawFourier (W t i) ξ)
      =
    fun i : Fin 3 =>
      h3HeatFourierSymbol ν t ξ *
          h3SpectralScalarRawFourier (W 0 i) ξ
        -
      ∫ s in (0 : ℝ)..t,
        h3HeatFourierSymbol ν (t - s) ξ *
          h3RawFinLerayOuterProductDivergence
            (W s) (W s) i ξ := by
  exact
    h3FinHeatModeVariationOfConstants_retarded
      ht
      ξ
      (fun s i =>
        h3SpectralScalarRawFourier (W s i) ξ)
      (fun s i =>
        h3RawFinLerayOuterProductDivergence
          (W s) (W s) i ξ)
      hFContinuous
      (by
        intro s hs
        simpa only [H3FinHeatLerayModeODEAt] using
          hODE s hs)
      hWeightedForcing

/-- The same concrete retarded identity with the heat part and nonlinear
Duhamel part displayed on the left. -/
theorem h3FinHeatLerayModeVariationOfConstants_retarded_sub
    {ν t : ℝ}
    (ht : 0 ≤ t)
    (ξ : H3FourierPoint3)
    (W : ℝ → H3SpectralFinVectorState)
    (hFContinuous :
      ∀ i : Fin 3,
        ContinuousOn
          (fun s : ℝ =>
            h3SpectralScalarRawFourier (W s i) ξ)
          (Set.Icc (0 : ℝ) t))
    (hODE :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        H3FinHeatLerayModeODEAt ν ξ W s)
    (hWeightedForcing :
      ∀ i : Fin 3,
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
      h3HeatFourierSymbol ν t ξ *
        h3SpectralScalarRawFourier (W 0 i) ξ)
      -
    (fun i : Fin 3 =>
      ∫ s in (0 : ℝ)..t,
        h3HeatFourierSymbol ν (t - s) ξ *
          h3RawFinLerayOuterProductDivergence
            (W s) (W s) i ξ)
      =
    fun i : Fin 3 =>
      h3SpectralScalarRawFourier (W t i) ξ := by
  have h :=
    h3FinHeatLerayModeVariationOfConstants_retarded
      ht ξ W hFContinuous hODE hWeightedForcing

  rw [h]

  funext i
  rfl

end

end Euclidean
end Bridge
end PrimeTensor
