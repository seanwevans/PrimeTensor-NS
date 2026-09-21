import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Heat.Third.Derivative.Endpoint
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Classicalization: third-Fréchet fresh-tail affine rescaling

The order-three Duhamel cocycle and old-history quotient are closed.  The
remaining fresh contribution is the third spatial Fréchet derivative of the
short Duhamel tail on `[t,t+h]`.

For three canonical coordinate directions define the retarded third-coordinate
forcing path by

    s ↦ D_a D_b D_c H_{T-s} N(W(s),W(s))(x).

Then use the affine source-time substitution

    s = t + h u,    u ∈ [0,1].

The resulting exact identity is

    ∫ₜ^{t+h} thirdRetarded(t+h,s) ds
      =
    h • ∫₀¹ freshThirdRescaled(h,u) du,

and for `h ≠ 0` multiplication by `h⁻¹` cancels the affine Jacobian.

This checkpoint is purely definitional/algebraic.  No endpoint estimate or
temporal limit is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelThirdFrechetFreshRescaled
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Retarded ordered third-coordinate forcing path at terminal time `T`. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
    (ν T : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i a b c : Fin 3)
    (x : H3FourierPoint3)
    (s : ℝ) : ℂ :=
  h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
    ν (T - s) (U s) (V s) i a b c x

/-- The third-Fréchet fresh-tail integrand after the affine source-time
rescaling `s = t + h u`. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
    (ν t h : ℝ)
    (W : ℝ → H3SpectralFinVectorState)
    (i a b c : Fin 3)
    (x : H3FourierPoint3)
    (u : ℝ) : ℂ :=
  h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
    ν (t + h) W W i a b c x (t + h * u)

/-- Expanding the rescaled third-Fréchet fresh integrand exposes the heat lag
`h(1-u)` and source state `W(t+hu)`. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand_eq_thirdCoordinateRepresentative
    (ν t h : ℝ)
    (W : ℝ → H3SpectralFinVectorState)
    (i a b c : Fin 3)
    (x : H3FourierPoint3)
    (u : ℝ) :
    h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
        ν t h W i a b c x u
      =
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
      ν (h * (1 - u))
      (W (t + h * u))
      (W (t + h * u))
      i a b c x := by
  unfold
    h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
  congr 1
  ring

/-- Exact affine-rescaling identity for the `(a,b,c)` third-coordinate fresh
retarded path. -/
theorem intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechet_eq_smul_rescaled
    (ν t h : ℝ)
    (W : ℝ → H3SpectralFinVectorState)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    (∫ s in t..t + h,
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
        ν (t + h) W W i a b c x s)
      =
    h •
      (∫ u in (0 : ℝ)..1,
        h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
          ν t h W i a b c x u) := by
  have hChange :=
    intervalIntegral.smul_integral_comp_add_mul
      (a := (0 : ℝ))
      (b := (1 : ℝ))
      (fun s : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
          ν (t + h) W W i a b c x s)
      h
      t

  have hIntegrand :
      (fun u : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
          ν (t + h) W W i a b c x (t + h * u))
        =
      (fun u : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
          ν t h W i a b c x u) := by
    rfl

  rw [hIntegrand] at hChange

  simpa only [mul_zero, add_zero, mul_one] using hChange.symm

/-- For a nonzero increment, the normalized `(a,b,c)` third-Fréchet fresh
retarded tail is exactly its fixed-domain affine rescaling. -/
theorem inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechet_eq_rescaled
    {ν t h : ℝ}
    (hh : h ≠ 0)
    (W : ℝ → H3SpectralFinVectorState)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    h⁻¹ •
        (∫ s in t..t + h,
          h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRetardedPath
            ν (t + h) W W i a b c x s)
      =
    ∫ u in (0 : ℝ)..1,
      h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
        ν t h W i a b c x u := by
  rw [
    intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechet_eq_smul_rescaled
      ν t h W i a b c x
  ]
  rw [smul_smul]
  simp [hh]

end

end Euclidean
end Bridge
end PrimeTensor
