import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Time.Integrability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Classicalization: first-Fréchet fresh-tail affine rescaling

The old-history contribution to the selected Duhamel first-Fréchet right
quotient is now closed.  The remaining fresh contribution is the spatial
Fréchet derivative of the short Duhamel tail on `[t,t+h]`.

As in the scalar diagonal derivative pipeline, use the affine substitution

    s = t + h u,    u ∈ [0,1].

For one canonical spatial coordinate direction `e_a`, define the rescaled
first-Fréchet fresh integrand by evaluating the already-constructed retarded
Fréchet derivative path at `s = t + h u`.

Then

    ∫ₜ^{t+h} DₓK(t+h,s,x)[e_a] ds
      =
    h • ∫₀¹ freshFrechetRescaled(h,u) du.

For `h ≠ 0`, multiplication by `h⁻¹` cancels this factor exactly.

This checkpoint is purely algebraic.  The next file will prove convergence of
the fixed-domain rescaled derivative integral to the instantaneous forcing
gradient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFirstFrechetFreshRescaled
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The first-Fréchet fresh-tail integrand after the affine source-time
rescaling `s = t + h u`, evaluated on one canonical spatial direction. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
    (ν t h : ℝ)
    (W : ℝ → H3SpectralFinVectorState)
    (i a : Fin 3)
    (x : H3FourierPoint3)
    (u : ℝ) : ℂ :=
  h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
      ν (t + h) W W i x (t + h * u)
      (h3FourierAxisDirection (h3AxisOfFin3 a))

/-- The rescaled first-Fréchet integrand is exactly the corresponding scalar
first-coordinate retarded derivative path. -/
@[simp]
theorem h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand_eq_firstDerivativeRetardedPath
    (ν t h : ℝ)
    (W : ℝ → H3SpectralFinVectorState)
    (i a : Fin 3)
    (x : H3FourierPoint3)
    (u : ℝ) :
    h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
        ν t h W i a x u
      =
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
      ν (t + h) W W i a x (t + h * u) := by
  unfold
    h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
  exact
    h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_axis
      ν (t + h) W W i a x (t + h * u)

/-- Exact affine-rescaling identity for the coordinate evaluation of the
first-Fréchet fresh retarded path. -/
theorem intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechet_eq_smul_rescaled
    (ν t h : ℝ)
    (W : ℝ → H3SpectralFinVectorState)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    (∫ s in t..t + h,
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
          ν (t + h) W W i x s
          (h3FourierAxisDirection (h3AxisOfFin3 a)))
      =
    h •
      (∫ u in (0 : ℝ)..1,
        h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
          ν t h W i a x u) := by
  have hChange :=
    intervalIntegral.smul_integral_comp_add_mul
      (a := (0 : ℝ))
      (b := (1 : ℝ))
      (fun s : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
          ν (t + h) W W i x s
          (h3FourierAxisDirection (h3AxisOfFin3 a)))
      h
      t

  have hIntegrand :
      (fun u : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
          ν (t + h) W W i x (t + h * u)
          (h3FourierAxisDirection (h3AxisOfFin3 a)))
        =
      (fun u : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
          ν t h W i a x u) := by
    rfl

  rw [hIntegrand] at hChange

  simpa only [mul_zero, add_zero, mul_one] using hChange.symm

/-- For a nonzero increment, the normalized coordinate first-Fréchet fresh
tail is exactly its fixed-domain affine rescaling. -/
theorem inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechet_eq_rescaled
    {ν t h : ℝ}
    (hh : h ≠ 0)
    (W : ℝ → H3SpectralFinVectorState)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    h⁻¹ •
        (∫ s in t..t + h,
          h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
              ν (t + h) W W i x s
              (h3FourierAxisDirection (h3AxisOfFin3 a)))
      =
    ∫ u in (0 : ℝ)..1,
      h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
        ν t h W i a x u := by
  rw [
    intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechet_eq_smul_rescaled
      ν t h W i a x
  ]
  rw [smul_smul]
  simp [hh]

end

end Euclidean
end Bridge
end PrimeTensor
