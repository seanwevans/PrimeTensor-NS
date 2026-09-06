import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Cutoff.L2
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Classicalization: derivative cutoff decomposition

`Schwartz.Cutoff.L2` proved the zeroth-order convergence

    χₙ φ → φ  in L².

For the first-derivative coordinates of the `W¹,²` graph, the product rule gives

    ∂ₐ(χₙ φ)
      =
    χₙ ∂ₐφ
      +
    (∂ₐχₙ) φ.

The first term is already covered by the zeroth-order theorem, applied to the
Schwartz derivative `∂ₐφ`.

This file formalizes that decomposition pointwise in Schwartz space, packages
the second term as a Schwartz remainder, proves convergence of the first term
in bundled `L²`, and isolates the only remaining analytic statement:

    ((∂ₐχₙ) φ) → 0  in L².

Thus after this checkpoint the `W¹,²` cutoff proof has exactly one live
estimate, namely decay of the derivative-of-cutoff remainder.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzCutoffDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## The scalar derivative of the expanding bump -/

/-- Coordinate directional derivative of the cutoff bump, written directly
through the Fréchet derivative. -/
noncomputable def h3W12CutoffBumpLineDerivative
    (n : ℕ)
    (a : PrimeTensor.Axis Depth.three)
    (x : H3FourierPoint3) :
    ℝ :=
  (fderiv ℝ
      (h3W12CutoffBump n :
        H3FourierPoint3 → ℝ)
      x)
    (h3FourierAxisDirection a)

/-! ## Product-rule decomposition -/

/-- Pointwise product rule for the cutoff Schwartz sequence. -/
theorem h3W12CutoffSchwartz_lineDeriv_apply
    (n : ℕ)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (a : PrimeTensor.Axis Depth.three)
    (x : H3FourierPoint3) :
    (∂_{h3FourierAxisDirection a}
        (h3W12CutoffSchwartz n φ)) x
      =
    h3W12CutoffSchwartz n
        (∂_{h3FourierAxisDirection a} φ) x
      +
    h3W12CutoffBumpLineDerivative n a x * φ x := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]

  change
    (fderiv ℝ
        (fun y : H3FourierPoint3 =>
          h3W12CutoffBump n y * φ y)
        x)
      (h3FourierAxisDirection a)
      =
    h3W12CutoffBump n x *
        (∂_{h3FourierAxisDirection a} φ) x
      +
    h3W12CutoffBumpLineDerivative n a x * φ x

  have hBumpDiff :
      DifferentiableAt ℝ
        (h3W12CutoffBump n :
          H3FourierPoint3 → ℝ)
        x :=
    ((h3W12CutoffBump_contDiff n).differentiable
      (by simp)).differentiableAt

  have hφDiff :
      DifferentiableAt ℝ
        (φ : H3FourierPoint3 → ℝ)
        x :=
    ((φ.smooth (⊤ : ℕ∞)).differentiable
      (by simp)).differentiableAt

  rw [fderiv_fun_mul hBumpDiff hφDiff]

  simp only [
    ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,
    smul_eq_mul,
    h3W12CutoffBumpLineDerivative
  ]

  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]

  ring

/-- The derivative-of-cutoff error as an intrinsic Schwartz function.

Defining it as the difference of two Schwartz functions means no extra
compact-support or `MemLp` bookkeeping is needed merely to package it. -/
noncomputable def h3W12CutoffDerivativeRemainder
    (n : ℕ)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (a : PrimeTensor.Axis Depth.three) :
    𝓢(H3FourierPoint3, ℝ) :=
  ∂_{h3FourierAxisDirection a}
      (h3W12CutoffSchwartz n φ)
    -
  h3W12CutoffSchwartz n
      (∂_{h3FourierAxisDirection a} φ)

@[simp]
theorem h3W12CutoffDerivativeRemainder_apply
    (n : ℕ)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (a : PrimeTensor.Axis Depth.three)
    (x : H3FourierPoint3) :
    h3W12CutoffDerivativeRemainder n φ a x
      =
    h3W12CutoffBumpLineDerivative n a x * φ x := by
  unfold h3W12CutoffDerivativeRemainder

  rw [SchwartzMap.sub_apply]
  rw [h3W12CutoffSchwartz_lineDeriv_apply]

  ring

/-- Schwartz-space decomposition of the cutoff derivative into the already
controlled main term plus the derivative-of-cutoff remainder. -/
theorem h3W12CutoffSchwartz_lineDeriv_eq_main_add_remainder
    (n : ℕ)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (a : PrimeTensor.Axis Depth.three) :
    ∂_{h3FourierAxisDirection a}
        (h3W12CutoffSchwartz n φ)
      =
    h3W12CutoffSchwartz n
        (∂_{h3FourierAxisDirection a} φ)
      +
    h3W12CutoffDerivativeRemainder n φ a := by
  unfold h3W12CutoffDerivativeRemainder
  abel

/-! ## The main derivative term already converges -/

/-- The product-rule main term `χₙ ∂ₐφ` converges to `∂ₐφ` in real `L²`.
This is exactly the zeroth-order cutoff theorem applied to the Schwartz
derivative. -/
theorem h3W12CutoffSchwartz_lineDeriv_main_toLp_tendsto
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (a : PrimeTensor.Axis Depth.three) :
    Tendsto
      (fun n : ℕ =>
        (h3W12CutoffSchwartz n
          (∂_{h3FourierAxisDirection a} φ)).toLp
            2
            (volume : Measure H3FourierPoint3))
      atTop
      (𝓝
        ((∂_{h3FourierAxisDirection a} φ :
          𝓢(H3FourierPoint3, ℝ)).toLp
            2
            (volume : Measure H3FourierPoint3))) := by
  exact
    h3W12CutoffSchwartz_toLp_tendsto
      (∂_{h3FourierAxisDirection a} φ)

/-! ## Exact remaining derivative frontier -/

/-- The only remaining analytic estimate in the first-derivative cutoff
argument: the derivative-of-cutoff remainder tends to zero in `L²`. -/
def H3W12CutoffDerivativeRemainderTendsToZero : Prop :=
  ∀ (φ : 𝓢(H3FourierPoint3, ℝ))
    (a : PrimeTensor.Axis Depth.three),
    Tendsto
      (fun n : ℕ =>
        (h3W12CutoffDerivativeRemainder n φ a).toLp
          2
          (volume : Measure H3FourierPoint3))
      atTop
      (𝓝 0)

/-- Pointwise form of the remaining remainder estimate.  This theorem exposes
that the live term is literally `(∂ₐχₙ) φ`, with no hidden Schwartz-space
bookkeeping. -/
theorem H3W12CutoffDerivativeRemainderTendsToZero_iff
    :
    H3W12CutoffDerivativeRemainderTendsToZero
      ↔
    ∀ (φ : 𝓢(H3FourierPoint3, ℝ))
      (a : PrimeTensor.Axis Depth.three),
      Tendsto
        (fun n : ℕ =>
          (h3W12CutoffDerivativeRemainder n φ a).toLp
            2
            (volume : Measure H3FourierPoint3))
        atTop
        (𝓝 0) := by
  rfl

end

end Euclidean
end Bridge
end PrimeTensor
