import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Heat.Mode.Variation.Of.Constants

/-!
# Classicalization: finite-vector H³ heat-mode variation of constants

`SpectralHeatModeVariationOfConstants` gives the retarded heat formula for one
complex Fourier coordinate.  The Navier--Stokes Fourier ODE is naturally a
three-component finite vector at each frequency.

This file packages the scalar theorem simultaneously over `Fin 3`.

No new analytic estimate appears here.  The purpose is to expose the exact
finite-vector interface needed by the next projected-PDE bridge:

* one common heat rate `ν q(ξ)`;
* one coordinatewise time ODE;
* one coordinatewise weighted-forcing integrability hypothesis;
* one vector-valued retarded conclusion.

The nonlinear forcing remains abstract in this file.  The next rung can
identify it with `h3RawFinLerayOuterProductDivergence`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

/-- Coordinatewise H³ heat-mode ODE data at one fixed frequency. -/
def H3FinHeatModeODEAt
    (ν : ℝ)
    (ξ : H3FourierPoint3)
    (F G : ℝ → Fin 3 → ℂ)
    (s : ℝ) : Prop :=
  ∀ i : Fin 3,
    HasDerivAt
      (fun r : ℝ => F r i)
      ((-(ν * h3FourierGradientSquare ξ)) • F s i - G s i)
      s

/-- The abstract finite-vector Fourier ODE implies the full retarded heat
formula at one fixed frequency, coordinatewise and hence as a `Fin 3` vector. -/
theorem h3FinHeatModeVariationOfConstants_retarded
    {ν t : ℝ}
    (ht : 0 ≤ t)
    (ξ : H3FourierPoint3)
    (F G : ℝ → Fin 3 → ℂ)
    (hFContinuous :
      ∀ i : Fin 3,
        ContinuousOn
          (fun s : ℝ => F s i)
          (Set.Icc (0 : ℝ) t))
    (hODE :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        H3FinHeatModeODEAt ν ξ F G s)
    (hWeightedForcing :
      ∀ i : Fin 3,
        IntervalIntegrable
          (fun s : ℝ =>
            Real.exp
                (ν * h3FourierGradientSquare ξ * s)
              • G s i)
          volume
          0
          t) :
    F t
      =
    fun i : Fin 3 =>
      h3HeatFourierSymbol ν t ξ * F 0 i
        -
      ∫ s in (0 : ℝ)..t,
        h3HeatFourierSymbol ν (t - s) ξ * G s i := by
  funext i

  exact
    h3ComplexHeatVariationOfConstants_retarded_h3HeatFourierSymbol
      ht
      ξ
      (fun s : ℝ => F s i)
      (fun s : ℝ => G s i)
      (hFContinuous i)
      (by
        intro s hs
        exact hODE s hs i)
      (hWeightedForcing i)

/-- Equality form with the retarded nonlinear integral named separately.
This is convenient when a later theorem identifies that integral with the
pointwise representative of `h3SpectralFinHeatLerayDuhamel`. -/
theorem h3FinHeatModeVariationOfConstants_retarded_sub
    {ν t : ℝ}
    (ht : 0 ≤ t)
    (ξ : H3FourierPoint3)
    (F G : ℝ → Fin 3 → ℂ)
    (hFContinuous :
      ∀ i : Fin 3,
        ContinuousOn
          (fun s : ℝ => F s i)
          (Set.Icc (0 : ℝ) t))
    (hODE :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        H3FinHeatModeODEAt ν ξ F G s)
    (hWeightedForcing :
      ∀ i : Fin 3,
        IntervalIntegrable
          (fun s : ℝ =>
            Real.exp
                (ν * h3FourierGradientSquare ξ * s)
              • G s i)
          volume
          0
          t) :
    (fun i : Fin 3 =>
      h3HeatFourierSymbol ν t ξ * F 0 i)
      -
    (fun i : Fin 3 =>
      ∫ s in (0 : ℝ)..t,
        h3HeatFourierSymbol ν (t - s) ξ * G s i)
      =
    F t := by
  have h :=
    h3FinHeatModeVariationOfConstants_retarded
      ht ξ F G hFContinuous hODE hWeightedForcing

  rw [h]

  funext i
  rfl

end

end Euclidean
end Bridge
end PrimeTensor
