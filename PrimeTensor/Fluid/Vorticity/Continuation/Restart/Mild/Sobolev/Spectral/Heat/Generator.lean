import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Heat.Derivative.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Time generator of the H³ spectral heat multiplier

For one frequency `ξ`, the heat multiplier is

    m(t,ξ) = exp (-ν t q(ξ)),
    q(ξ) = (2π)² ‖ξ‖².

This file proves its exact real-time derivative and then separately identifies
the derivative coefficient with the usual heat generator

    -ν q(ξ) m(t,ξ).

Keeping the calculus expression in the multiplication order produced by
Mathlib's derivative combinators avoids mixing differentiation with unrelated
commutative-ring normalization.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SpectralHeatGenerator
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/- Prefer Mathlib's existing restriction-of-scalars real normed-space
structure on `ℂ`.  `Complex.HasDerivAt.ofReal_comp` is elaborated against this
exact instance declaration; raising its local priority avoids manufacturing a
definitionally distinct alias. -/
attribute [local instance 1100] NormedSpace.complexToReal

/-- Fourier symbol of the heat time generator, written in the native order
produced by differentiating the exponential multiplier. -/
def h3HeatFourierTimeGeneratorSymbol
    (ν t : ℝ)
    (ξ : H3FourierPoint3) : ℂ :=
  h3HeatFourierSymbol ν t ξ *
    ((-((2 * Real.pi) ^ 2 * ν * ‖ξ‖ ^ 2) : ℝ) : ℂ)

/-- The native derivative coefficient is the usual `-ν q(ξ)` heat generator. -/
theorem h3HeatFourierTimeGeneratorSymbol_eq
    (ν t : ℝ)
    (ξ : H3FourierPoint3) :
    h3HeatFourierTimeGeneratorSymbol ν t ξ
      =
    ((-ν * h3FourierGradientSquare ξ : ℝ) : ℂ) *
      h3HeatFourierSymbol ν t ξ := by
  unfold
    h3HeatFourierTimeGeneratorSymbol
    h3FourierGradientSquare
  push_cast
  ring

/-- Exact time derivative of the scalar Fourier heat multiplier. -/
theorem h3HeatFourierSymbol_hasDerivAt_time
    (ν t : ℝ)
    (ξ : H3FourierPoint3) :
    HasDerivAt
      (fun s : ℝ => h3HeatFourierSymbol ν s ξ)
      (h3HeatFourierTimeGeneratorSymbol ν t ξ)
      t := by
  have hscale :=
    HasDerivAt.const_mul
      ((2 * Real.pi) ^ 2 * ν)
      (hasDerivAt_id t)

  have hquad :=
    hscale.mul_const (‖ξ‖ ^ 2)

  have hneg :=
    hquad.neg

  have hexp :=
    hneg.exp

  have hcomplex :
      HasDerivAt
        (fun s : ℝ =>
          (Real.exp
            (-((2 * Real.pi) ^ 2 * ν * s * ‖ξ‖ ^ 2)) : ℂ))
        (((Real.exp
            (-((2 * Real.pi) ^ 2 * ν * t * ‖ξ‖ ^ 2)) *
          (-((2 * Real.pi) ^ 2 * ν * ‖ξ‖ ^ 2)) : ℝ) : ℂ))
        t := by
    simpa only [
      Pi.neg_apply,
      id_eq,
      one_mul,
      mul_one
    ] using hexp.ofReal_comp

  have hfun :
      (fun s : ℝ =>
        (Real.exp
          (-((2 * Real.pi) ^ 2 * ν * s * ‖ξ‖ ^ 2)) : ℂ))
        =
      (fun s : ℝ =>
        h3HeatFourierSymbol ν s ξ) := by
    rfl

  have hcoef :
      (((Real.exp
          (-((2 * Real.pi) ^ 2 * ν * t * ‖ξ‖ ^ 2)) *
        (-((2 * Real.pi) ^ 2 * ν * ‖ξ‖ ^ 2)) : ℝ) : ℂ))
        =
      h3HeatFourierTimeGeneratorSymbol ν t ξ := by
    unfold
      h3HeatFourierTimeGeneratorSymbol
      h3HeatFourierSymbol
    rw [Complex.ofReal_mul]

  rw [← hfun, ← hcoef]
  exact hcomplex

/-- Equality form of the heat-symbol time derivative. -/
theorem deriv_h3HeatFourierSymbol_time
    (ν t : ℝ)
    (ξ : H3FourierPoint3) :
    deriv
      (fun s : ℝ => h3HeatFourierSymbol ν s ξ)
      t
      =
    h3HeatFourierTimeGeneratorSymbol ν t ξ := by
  exact
    (h3HeatFourierSymbol_hasDerivAt_time ν t ξ).deriv

/-- For fixed frequency, the heat-generator multiplier is continuous in time. -/
theorem continuous_h3HeatFourierTimeGeneratorSymbol_time
    (ν : ℝ)
    (ξ : H3FourierPoint3) :
    Continuous
      (fun t : ℝ =>
        h3HeatFourierTimeGeneratorSymbol ν t ξ) := by
  unfold
    h3HeatFourierTimeGeneratorSymbol
    h3HeatFourierSymbol
  fun_prop

/-- For each fixed frequency, the scalar heat multiplier is `C¹` in real time
with the generator above as its derivative. -/
theorem contDiff_one_h3HeatFourierSymbol_time
    (ν : ℝ)
    (ξ : H3FourierPoint3) :
    ContDiff ℝ 1
      (fun t : ℝ =>
        h3HeatFourierSymbol ν t ξ) := by
  rw [contDiff_one_iff_deriv]
  constructor

  · intro t
    exact
      (h3HeatFourierSymbol_hasDerivAt_time
        ν t ξ).differentiableAt

  · have hDeriv :
        deriv
          (fun s : ℝ =>
            h3HeatFourierSymbol ν s ξ)
          =
        fun t : ℝ =>
          h3HeatFourierTimeGeneratorSymbol ν t ξ := by
      funext t
      exact deriv_h3HeatFourierSymbol_time ν t ξ

    rw [hDeriv]
    exact
      continuous_h3HeatFourierTimeGeneratorSymbol_time
        ν ξ

end
end Euclidean
end Bridge
end PrimeTensor
