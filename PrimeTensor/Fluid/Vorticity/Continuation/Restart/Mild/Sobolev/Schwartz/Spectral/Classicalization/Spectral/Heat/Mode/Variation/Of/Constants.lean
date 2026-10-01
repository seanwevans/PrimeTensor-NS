import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Scalar.Retarded.Variation.Of.Constants
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.Heat.Generator

/-!
# Classicalization: variation of constants in the concrete H³ heat symbol

`SpectralScalarRetardedVariationOfConstants` proves the abstract scalar formula

    F(t)
      =
    exp (-a t) • F(0)
      -
    ∫₀ᵗ exp (-a (t-s)) • G(s) ds.

For one H³ Fourier frequency, the heat rate is

    a = ν q(ξ),
    q(ξ) = h3FourierGradientSquare ξ,

and the project heat multiplier is

    h3HeatFourierSymbol ν t ξ
      = exp (-ν t q(ξ)).

This file identifies those two presentations and specializes variation of
constants to the exact heat-symbol notation used by the heat--Leray solver.

The remaining old-branch mild bridge can therefore focus only on the concrete
Fourier ODE and nonlinear Leray forcing.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

attribute [local instance 1100] NormedSpace.complexToReal

/-- The project heat symbol is the abstract integrating-factor exponential
with rate `ν * q(ξ)`. -/
theorem h3HeatFourierSymbol_eq_exp_gradientSquare
    (ν t : ℝ)
    (ξ : H3FourierPoint3) :
    h3HeatFourierSymbol ν t ξ
      =
    (Real.exp
      (-(ν * h3FourierGradientSquare ξ * t)) : ℂ) := by
  unfold h3HeatFourierSymbol h3FourierGradientSquare
  norm_cast
  congr 1
  ring

/-- Multiplication by the project heat symbol is exactly real scalar
multiplication by the abstract retarded exponential. -/
theorem h3HeatFourierSymbol_mul_eq_exp_smul
    (ν t : ℝ)
    (ξ : H3FourierPoint3)
    (z : ℂ) :
    h3HeatFourierSymbol ν t ξ * z
      =
    Real.exp
        (-(ν * h3FourierGradientSquare ξ * t))
      • z := by
  rw [h3HeatFourierSymbol_eq_exp_gradientSquare]
  simpa only [Complex.real_smul]

/-- Scalar variation of constants written directly with PrimeTensor's H³ heat
multiplier.

This is the exact frequencywise retarded heat shape required before identifying
`G` with the Leray-projected nonlinear Fourier forcing. -/
theorem h3ComplexHeatVariationOfConstants_retarded_h3HeatFourierSymbol
    {ν t : ℝ}
    (ht : 0 ≤ t)
    (ξ : H3FourierPoint3)
    (F G : ℝ → ℂ)
    (hFContinuous :
      ContinuousOn F (Set.Icc (0 : ℝ) t))
    (hODE :
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        HasDerivAt
          F
          ((-(ν * h3FourierGradientSquare ξ)) • F s - G s)
          s)
    (hWeightedForcing :
      IntervalIntegrable
        (fun s : ℝ =>
          Real.exp
              (ν * h3FourierGradientSquare ξ * s)
            • G s)
        volume
        0
        t) :
    F t
      =
    h3HeatFourierSymbol ν t ξ * F 0
      -
    ∫ s in (0 : ℝ)..t,
      h3HeatFourierSymbol ν (t - s) ξ * G s := by
  have h :=
    h3ComplexHeatVariationOfConstants_retarded
      (a := ν * h3FourierGradientSquare ξ)
      ht
      F
      G
      hFContinuous
      hODE
      hWeightedForcing

  simpa only [
    h3HeatFourierSymbol_mul_eq_exp_smul
  ] using h

end

end Euclidean
end Bridge
end PrimeTensor
