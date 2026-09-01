import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Time.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SecondCoordinate

/-!
# Nonlinear heat time generator as a spatial Laplacian multiplier

The positive-lag nonlinear heat time derivative has now been constructed
directly at the Fourier-integral level.  Its raw multiplier is

    -ν q(ξ),

where `q(ξ) = (2π)^2 ‖ξ‖^2`.

The selected Duhamel endpoint bootstrap independently constructed every mixed
second spatial Fourier amplitude.  On the diagonal, the three coordinate
symbols satisfy

    Σⱼ Dⱼ(ξ) Dⱼ(ξ) = -q(ξ).

This file records that algebraic bridge and nothing stronger.  In particular,
it does **not** claim that the uncancelled time-generator path is integrable
through zero heat lag.  That endpoint issue is exactly what the existing
quarter-Hölder second-derivative cancellation stack repairs.

The resulting identity lets the forthcoming diagonal Duhamel time derivative
reuse the already-integrable spatial Hessian/Laplacian machinery.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped ENNReal NNReal Topology RealInnerProductSpace BigOperators

noncomputable section

noncomputable local instance axisFintypeH3NonlinearHeatTimeLaplacian
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Squaring one Fourier coordinate derivative symbol gives minus its squared
norm. -/
theorem h3FourierDerivativeSymbol_mul_self_eq_neg_norm_sq
    (j : Fin 3)
    (ξ : H3FourierPoint3) :
    h3FourierDerivativeSymbol j ξ *
        h3FourierDerivativeSymbol j ξ
      =
    -((‖h3FourierDerivativeSymbol j ξ‖ ^ 2 : ℝ) : ℂ) := by
  let c : ℝ :=
    2 * Real.pi * ξ (h3AxisOfFin3 j)

  have hsym :
      h3FourierDerivativeSymbol j ξ
        =
      (c : ℂ) * Complex.I := by
    dsimp only [c]
    rw [h3FourierDerivativeSymbol_eq_inner]
    rw [inner_h3FourierAxisDirection]
    push_cast
    ring

  have hc :
      (c : ℂ) * (c : ℂ)
        =
      (((2 * Real.pi) ^ 2 *
          (ξ (h3AxisOfFin3 j)) ^ 2 : ℝ) : ℂ) := by
    dsimp only [c]
    push_cast
    ring

  rw [norm_h3FourierDerivativeSymbol_sq]
  rw [hsym]

  calc
    ((c : ℂ) * Complex.I) * ((c : ℂ) * Complex.I)
        =
      ((c : ℂ) * (c : ℂ)) * (Complex.I * Complex.I) := by
        ring
    _ =
      -((c : ℂ) * (c : ℂ)) := by
        rw [Complex.I_mul_I]
        ring
    _ =
      -((((2 * Real.pi) ^ 2 *
          (ξ (h3AxisOfFin3 j)) ^ 2 : ℝ) : ℂ)) := by
        rw [hc]

/-- The trace of the three coordinate second-derivative Fourier symbols is
exactly the negative radial square-gradient multiplier. -/
theorem sum_h3FourierDerivativeSymbol_mul_self_eq_neg_gradientSquare
    (ξ : H3FourierPoint3) :
    (∑ j : Fin 3,
      h3FourierDerivativeSymbol j ξ *
        h3FourierDerivativeSymbol j ξ)
      =
    -(h3FourierGradientSquare ξ : ℂ) := by
  have hsum :=
    sum_norm_h3FourierDerivativeSymbol_sq ξ

  rw [Fin.sum_univ_three] at hsum
  rw [Fin.sum_univ_three]
  rw [
    h3FourierDerivativeSymbol_mul_self_eq_neg_norm_sq (0 : Fin 3) ξ,
    h3FourierDerivativeSymbol_mul_self_eq_neg_norm_sq (1 : Fin 3) ξ,
    h3FourierDerivativeSymbol_mul_self_eq_neg_norm_sq (2 : Fin 3) ξ
  ]
  rw [← hsum]
  push_cast
  ring

/-- Raw Fourier amplitude of the spatial Laplacian of one positive-lag
nonlinear forcing coordinate, written as the trace of the three already
constructed diagonal second-coordinate amplitudes. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatLaplacianRawAmplitude
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  ∑ j : Fin 3,
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
      ν τ U V i j j ξ

/-- The diagonal second-coordinate sum is literally `-q(ξ)` times the
positive-lag nonlinear forcing amplitude. -/
theorem h3RawFinLerayOuterProductDivergenceHeatLaplacianRawAmplitude_eq
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatLaplacianRawAmplitude
        ν τ U V i ξ
      =
    -(h3FourierGradientSquare ξ : ℂ) *
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν τ U V i ξ := by
  unfold h3RawFinLerayOuterProductDivergenceHeatLaplacianRawAmplitude
  unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude

  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [sum_h3FourierDerivativeSymbol_mul_self_eq_neg_gradientSquare]

/-- The newly constructed nonlinear heat time-generator amplitude is exactly
viscosity times the spatial-Laplacian amplitude. -/
theorem h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative_eq_viscosity_mul_laplacian
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
        ν τ U V i ξ
      =
    (ν : ℂ) *
      h3RawFinLerayOuterProductDivergenceHeatLaplacianRawAmplitude
        ν τ U V i ξ := by
  unfold
    h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
  rw [
    h3RawFinLerayOuterProductDivergenceHeatLaplacianRawAmplitude_eq
  ]
  push_cast
  ring

end

end Euclidean
end Bridge
end PrimeTensor
