import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Selected.Second.Frechet.Time.Integrability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Classicalization: second-Fréchet fresh-tail affine rescaling

The old-history contribution to the selected Duhamel second-Fréchet right
quotient is now closed.  The remaining fresh contribution is the second
spatial Fréchet derivative of the short Duhamel tail on `[t,t+h]`.

Use the same affine substitution as in the first-Fréchet branch,

    s = t + h u,    u ∈ [0,1].

For two canonical spatial coordinate directions `e_a,e_b`, define the
rescaled second-Fréchet fresh integrand by evaluating the already-constructed
retarded Hessian path at `s = t + h u`.

Then

    ∫ₜ^{t+h} D²ₓK(t+h,s,x)[e_a,e_b] ds
      =
    h • ∫₀¹ freshSecondFrechetRescaled(h,u) du.

For `h ≠ 0`, multiplication by `h⁻¹` cancels this factor exactly.

This checkpoint is purely algebraic.  No endpoint estimate or temporal limit
is introduced.

The proof is intentionally parallel to the first-Fréchet rescaling theorem;
the repeated affine-change-of-variables pattern is a candidate for later
order-generic extraction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelSecondFrechetFreshRescaled
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The second-Fréchet fresh-tail integrand after the affine source-time
rescaling `s = t + h u`, evaluated on two canonical spatial directions.

The assembled Hessian uses outer direction `b` and inner direction `a`, so
this scalar is the ordered coordinate coefficient `(a,b)`. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand
    (ν t h : ℝ)
    (W : ℝ → H3SpectralFinVectorState)
    (i a b : Fin 3)
    (x : H3FourierPoint3)
    (u : ℝ) : ℂ :=
  h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
      ν (t + h) W W i x (t + h * u)
      (h3FourierAxisDirection (h3AxisOfFin3 b))
      (h3FourierAxisDirection (h3AxisOfFin3 a))

/-- The rescaled second-Fréchet integrand is exactly the corresponding mixed
second-coordinate retarded path. -/
@[simp]
theorem h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand_eq_secondCoordinateRetardedPath
    (ν t h : ℝ)
    (W : ℝ → H3SpectralFinVectorState)
    (i a b : Fin 3)
    (x : H3FourierPoint3)
    (u : ℝ) :
    h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand
        ν t h W i a b x u
      =
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
      ν (t + h) W W i a b x (t + h * u) := by
  unfold
    h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand
  exact
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath_axis_axis
      ν (t + h) W W i a b x (t + h * u)

/-- Exact affine-rescaling identity for the `(a,b)` coordinate evaluation of
the fresh retarded Hessian path. -/
theorem intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechet_eq_smul_rescaled
    (ν t h : ℝ)
    (W : ℝ → H3SpectralFinVectorState)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    (∫ s in t..t + h,
      h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
          ν (t + h) W W i x s
          (h3FourierAxisDirection (h3AxisOfFin3 b))
          (h3FourierAxisDirection (h3AxisOfFin3 a)))
      =
    h •
      (∫ u in (0 : ℝ)..1,
        h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand
          ν t h W i a b x u) := by
  have hChange :=
    intervalIntegral.smul_integral_comp_add_mul
      (a := (0 : ℝ))
      (b := (1 : ℝ))
      (fun s : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
          ν (t + h) W W i x s
          (h3FourierAxisDirection (h3AxisOfFin3 b))
          (h3FourierAxisDirection (h3AxisOfFin3 a)))
      h
      t

  have hIntegrand :
      (fun u : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
          ν (t + h) W W i x (t + h * u)
          (h3FourierAxisDirection (h3AxisOfFin3 b))
          (h3FourierAxisDirection (h3AxisOfFin3 a)))
        =
      (fun u : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand
          ν t h W i a b x u) := by
    rfl

  rw [hIntegrand] at hChange

  simpa only [mul_zero, add_zero, mul_one] using hChange.symm

/-- For a nonzero increment, the normalized `(a,b)` second-Fréchet fresh tail
is exactly its fixed-domain affine rescaling. -/
theorem inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechet_eq_rescaled
    {ν t h : ℝ}
    (hh : h ≠ 0)
    (W : ℝ → H3SpectralFinVectorState)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    h⁻¹ •
        (∫ s in t..t + h,
          h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
              ν (t + h) W W i x s
              (h3FourierAxisDirection (h3AxisOfFin3 b))
              (h3FourierAxisDirection (h3AxisOfFin3 a)))
      =
    ∫ u in (0 : ℝ)..1,
      h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand
        ν t h W i a b x u := by
  rw [
    intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechet_eq_smul_rescaled
      ν t h W i a b x
  ]
  rw [smul_smul]
  simp [hh]

end

end Euclidean
end Bridge
end PrimeTensor
