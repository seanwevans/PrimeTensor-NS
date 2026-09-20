import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Fourth.Coordinate.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Frechet.History.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Time.Laplacian

/-!
# Classicalization: second-Fréchet old-history generator raw trace

The literal second-Fréchet old-history quotient now converges to the
reconstruction of the twice-coordinate-multiplied zero-time heat generator

    d_a(ξ) d_b(ξ) G_t(ξ).

At zero elapsed heat time,

    G_t(ξ) = -ν q(ξ) A_t(ξ),

and the already-compiled coordinate-symbol trace identity gives

    Σ_k d_k(ξ) d_k(ξ) = -q(ξ).

Therefore

    d_a d_b G_t
      =
    ν Σ_k d_a d_b d_k d_k A_t.

This file records exactly that raw Fourier identity.  No new estimate or
inverse-Fourier argument is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelSecondFrechetHistoryGeneratorRawTrace
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The twice-coordinate-multiplied zero-time old-history heat generator is
exactly viscosity times the raw trace of the three selected-Duhamel
fourth-coordinate multipliers. -/
theorem h3SelectedDuhamelHistoryHeatSecondCoordinateGeneratorRawAmplitude_eq_viscosity_mul_fourthTrace
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a b : Fin 3)
    (ξ : H3FourierPoint3) :
    h3SelectedDuhamelHistoryHeatSecondCoordinateGeneratorRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a b ξ
      =
    (ν : ℂ) *
      (∑ k : Fin 3,
        h3SelectedDuhamelFourthCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a b k k ξ) := by
  unfold h3SelectedDuhamelHistoryHeatSecondCoordinateGeneratorRawAmplitude
  unfold h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
  rw [
    h3SelectedDuhamelHistoryHeatRawAmplitude_zero
      hν U₀ hA hU₀ ht i
  ]
  unfold h3SelectedDuhamelFourthCoordinateRawAmplitude

  have hTrace :=
    sum_h3FourierDerivativeSymbol_mul_self_eq_neg_gradientSquare ξ

  have hCoeff :
      (((-ν * h3FourierGradientSquare ξ : ℝ) : ℂ))
        =
      (ν : ℂ) * (-(h3FourierGradientSquare ξ : ℂ)) := by
    push_cast
    ring

  rw [hCoeff]
  rw [← hTrace]
  rw [Fin.sum_univ_three]
  rw [Fin.sum_univ_three]
  ring

end

end Euclidean
end Bridge
end PrimeTensor
