import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.FreshRescaledIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Fresh Duhamel tail quotient

The fixed-domain dominated-convergence limit is already closed.  This file
connects that unit-interval object back to the literal fresh Duhamel tail.

For every real increment `h`, the affine substitution `s = t + h u` gives

    ∫ₜ^{t+h} H_{t+h-s} F(W(s),W(s)) ds
      =
    h • ∫₀¹ H_{h(1-u)} F(W(t+hu),W(t+hu)) du.

Mathlib's `intervalIntegral.smul_integral_comp_add_mul` proves this identity
without any nonzero hypothesis on `h`.

For `h > 0`, inverse scalar multiplication cancels the factor `h`.  Hence the
already-compiled rescaled integral limit immediately becomes the literal
fresh-tail difference-quotient limit:

    h⁻¹ • ∫ₜ^{t+h} H_{t+h-s} F(W(s),W(s)) ds
      ⟶
    F(W(t),W(t))

as `h ↓ 0`.

This is precisely the moving-upper-endpoint contribution needed by the
right-hand diagonal Duhamel derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3DuhamelFreshTailQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact affine-rescaling identity for the literal fresh Duhamel tail. -/
theorem intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshTail_eq_smul_rescaled
    (ν t h : ℝ)
    (W : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    (∫ s in t..t + h,
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν (t + h) W W i x s)
      =
    h •
      (∫ u in (0 : ℝ)..1,
        h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
          ν t h W i x u) := by
  have hChange :=
    intervalIntegral.smul_integral_comp_add_mul
      (a := (0 : ℝ))
      (b := (1 : ℝ))
      (fun s : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν (t + h) W W i x s)
      h
      t

  have hIntegrand :
      (fun u : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν (t + h) W W i x (t + h * u))
        =
      (fun u : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
          ν t h W i x u) := by
    funext u
    unfold
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
      h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
    congr 1
    ring

  rw [hIntegrand] at hChange

  simpa only [mul_zero, add_zero, mul_one] using hChange.symm

/-- For a nonzero increment, the normalized literal fresh tail is exactly the
fixed-domain rescaled integral. -/
theorem inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshTail_eq_rescaled
    {ν t h : ℝ}
    (hh : h ≠ 0)
    (W : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    h⁻¹ •
        (∫ s in t..t + h,
          h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
            ν (t + h) W W i x s)
      =
    ∫ u in (0 : ℝ)..1,
      h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
        ν t h W i x u := by
  rw [
    intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshTail_eq_smul_rescaled
      ν t h W i x
  ]
  rw [smul_smul]
  simp [hh]

/-- Selected restart fresh-tail quotient converges from the right to the
instantaneous unheated nonlinear forcing. -/
theorem tendsto_inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshTail_selectedRestart_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hW :
      Continuous
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀))
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          (∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
              ν (t + h) W W i x s))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i x)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hRescaled :=
    tendsto_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand_selectedRestart_zero_right
      (t := t)
      hν U₀ hA hU₀ hW i x

  have hRescaledPos :
      Tendsto
        (fun h : ℝ =>
          ∫ u in (0 : ℝ)..1,
            h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
              ν t h W i x u)
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i x)) := by
    exact
      hRescaled.mono_left
        (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)

  have hEq :
      (fun h : ℝ =>
        h⁻¹ •
          (∫ s in t..t + h,
            h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
              ν (t + h) W W i x s))
        =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ =>
        ∫ u in (0 : ℝ)..1,
          h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
            ν t h W i x u) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact
      inv_smul_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshTail_eq_rescaled
        (ne_of_gt hh) W i x

  exact Tendsto.congr' hEq.symm hRescaledPos

end

end Euclidean
end Bridge
end PrimeTensor
