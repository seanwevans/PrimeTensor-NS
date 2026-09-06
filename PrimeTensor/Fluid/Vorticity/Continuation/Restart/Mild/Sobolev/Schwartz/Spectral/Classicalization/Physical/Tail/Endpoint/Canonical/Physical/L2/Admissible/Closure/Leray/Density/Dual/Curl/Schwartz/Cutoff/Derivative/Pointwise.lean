import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Cutoff.Derivative
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Classicalization: pointwise decay of the derivative cutoff remainder

`Schwartz.Cutoff.Derivative` reduced the remaining first-derivative error to

    (∂ₐ χₙ) φ.

For every fixed point `x`, the inner radius of `χₙ` tends to infinity.
Hence for all sufficiently large `n`, `x` lies strictly inside the region on
which `χₙ` is identically one in a neighborhood.  Its Fréchet derivative at
`x` is therefore exactly zero.

This file proves that eventual exact vanishing pointwise.  The final analytic
step will only need a uniform integrable domination in order to turn this
pointwise stabilization into `L²` convergence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzCutoffDerivativePointwise
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Eventual vanishing of the cutoff derivative -/

/-- At every fixed point, every coordinate directional derivative of the
expanding cutoff is eventually exactly zero. -/
theorem h3W12CutoffBumpLineDerivative_eventually_eq_zero
    (a : PrimeTensor.Axis Depth.three)
    (x : H3FourierPoint3) :
    ∀ᶠ n : ℕ in atTop,
      h3W12CutoffBumpLineDerivative n a x = 0 := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ‖x‖

  filter_upwards [eventually_ge_atTop N] with n hn

  have hx :
      x ∈
        Metric.ball
          (0 : H3FourierPoint3)
          (h3W12CutoffBump n).rIn := by
    rw [
      Metric.mem_ball,
      dist_zero_right,
      h3W12CutoffBump_rIn
    ]

    calc
      ‖x‖ < (N : ℝ) := hN
      _ ≤ (n : ℝ) := by
        exact_mod_cast hn
      _ < (n : ℝ) + 1 := by
        linarith

  have hLocal :
      (h3W12CutoffBump n :
          H3FourierPoint3 → ℝ)
        =ᶠ[𝓝 x]
      (fun _ : H3FourierPoint3 => (1 : ℝ)) :=
    (h3W12CutoffBump n).eventuallyEq_one_of_mem_ball hx

  have hFDeriv :
      fderiv ℝ
          (h3W12CutoffBump n :
            H3FourierPoint3 → ℝ)
          x
        =
      0 := by
    rw [hLocal.fderiv_eq]
    simp

  unfold h3W12CutoffBumpLineDerivative

  rw [hFDeriv]

  simp

/-! ## Eventual vanishing of the complete remainder -/

/-- For every fixed point, the complete derivative cutoff remainder is
eventually exactly zero. -/
theorem h3W12CutoffDerivativeRemainder_eventually_eq_zero
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (a : PrimeTensor.Axis Depth.three)
    (x : H3FourierPoint3) :
    ∀ᶠ n : ℕ in atTop,
      h3W12CutoffDerivativeRemainder n φ a x = 0 := by
  filter_upwards [
    h3W12CutoffBumpLineDerivative_eventually_eq_zero a x
  ] with n hn

  rw [
    h3W12CutoffDerivativeRemainder_apply,
    hn,
    zero_mul
  ]

/-- In particular, the derivative cutoff remainder converges pointwise to
zero. -/
theorem h3W12CutoffDerivativeRemainder_tendsto_pointwise_zero
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (a : PrimeTensor.Axis Depth.three)
    (x : H3FourierPoint3) :
    Tendsto
      (fun n : ℕ =>
        h3W12CutoffDerivativeRemainder n φ a x)
      atTop
      (𝓝 0) := by
  refine (tendsto_congr' ?_).2 tendsto_const_nhds

  exact
    h3W12CutoffDerivativeRemainder_eventually_eq_zero
      φ a x

/-- The squared `ENNReal` norm of the derivative cutoff remainder also tends
pointwise to zero.  This is the exact pointwise hypothesis needed by the same
dominated-convergence pattern used in `Schwartz.Cutoff.L2`. -/
theorem h3W12CutoffDerivativeRemainder_enorm_sq_tendsto_pointwise_zero
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (a : PrimeTensor.Axis Depth.three)
    (x : H3FourierPoint3) :
    Tendsto
      (fun n : ℕ =>
        ‖h3W12CutoffDerivativeRemainder n φ a x‖ₑ
          ^ (2 : ℝ≥0∞).toReal)
      atTop
      (𝓝 0) := by
  refine (tendsto_congr' ?_).2 tendsto_const_nhds

  filter_upwards [
    h3W12CutoffDerivativeRemainder_eventually_eq_zero
      φ a x
  ] with n hn

  rw [hn]

  simp

end

end Euclidean
end Bridge
end PrimeTensor
