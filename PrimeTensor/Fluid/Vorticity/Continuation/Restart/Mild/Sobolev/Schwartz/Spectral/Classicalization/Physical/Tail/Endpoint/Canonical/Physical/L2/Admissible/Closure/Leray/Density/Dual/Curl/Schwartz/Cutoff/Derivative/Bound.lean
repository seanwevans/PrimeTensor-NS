import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Cutoff.Derivative.Pointwise
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Classicalization: uniform domination of the derivative cutoff remainder

`Schwartz.Cutoff.Derivative.Pointwise` proved that for every fixed spatial
point the derivative cutoff remainder is eventually exactly zero.

For dominated convergence we only need one further fact: a uniform-in-`n`
pointwise bound.

The cutoff family is an outward rescaling of the fixed `n = 0` bump:

    χₙ(x) = χ₀(((n + 1)⁻¹) • x).

The scalar map `x ↦ ((n + 1)⁻¹) • x` is `1`-Lipschitz, while the fixed compact
smooth bump `χ₀` is globally Lipschitz.  Therefore every `χₙ` shares the same
Lipschitz constant.  Since a derivative of a Lipschitz function has operator
norm bounded by the Lipschitz constant, every coordinate derivative `∂ₐχₙ`
is uniformly bounded.

Multiplication by a Schwartz function then gives

    ‖(∂ₐχₙ)(x) φ(x)‖ ≤ Cₐ ‖φ(x)‖,

which is the exact domination needed for the final `L²` convergence step.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzCutoffDerivativeBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## The expanding cutoffs are rescalings of one fixed bump -/

/-- Every cutoff is the `n = 0` cutoff precomposed with the contraction
`x ↦ ((n + 1)⁻¹) • x`. -/
theorem h3W12CutoffBump_eq_base_scaled
    (n : ℕ)
    (x : H3FourierPoint3) :
    h3W12CutoffBump n x
      =
    h3W12CutoffBump 0
      (((n : ℝ) + 1)⁻¹ • x) := by
  rw [ContDiffBump.apply, ContDiffBump.apply]

  have hn :
      (n : ℝ) + 1 ≠ 0 := by
    positivity

  simp only [
    h3W12CutoffBump_rOut,
    h3W12CutoffBump_rIn,
    Nat.cast_zero,
    zero_add,
    sub_zero,
    inv_one,
    one_smul
  ]

  rw [mul_div_cancel_right₀ 2 hn]

  norm_num

/-- The radial contraction used in the preceding identity is `1`-Lipschitz. -/
theorem h3W12CutoffScale_lipschitz
    (n : ℕ) :
    LipschitzWith 1
      (fun x : H3FourierPoint3 =>
        ((n : ℝ) + 1)⁻¹ • x) := by
  apply LipschitzWith.of_dist_le_mul

  intro x y

  rw [
    NNReal.coe_one,
    one_mul,
    dist_eq_norm,
    dist_eq_norm,
    ← smul_sub,
    norm_smul
  ]

  have hnPos :
      0 < (n : ℝ) + 1 := by
    positivity

  have hnOne :
      1 ≤ (n : ℝ) + 1 := by
    have hnNonneg :
        0 ≤ (n : ℝ) := by
      positivity
    linarith

  have hScale :
      ‖((n : ℝ) + 1)⁻¹‖ ≤ 1 := by
    rw [
      Real.norm_eq_abs,
      abs_inv,
      abs_of_pos hnPos
    ]

    exact
      (inv_le_one₀ hnPos).2 hnOne

  calc
    ‖((n : ℝ) + 1)⁻¹‖ * ‖x - y‖
        ≤
      1 * ‖x - y‖ := by
        exact
          mul_le_mul_of_nonneg_right
            hScale
            (norm_nonneg _)
    _ = ‖x - y‖ := by
      ring

/-! ## One global Lipschitz constant controls the whole cutoff family -/

/-- The fixed base cutoff has some finite global Lipschitz constant. -/
theorem exists_h3W12CutoffBump_base_lipschitz :
    ∃ C : ℝ≥0,
      LipschitzWith C
        (h3W12CutoffBump 0 :
          H3FourierPoint3 → ℝ) := by
  exact
    ContDiff.lipschitzWith_of_hasCompactSupport
      (𝕂 := ℝ)
      (h3W12CutoffBump_hasCompactSupport 0)
      (h3W12CutoffBump_contDiff 0)
      (by simp)

/-- The same Lipschitz constant controls every expanding cutoff. -/
theorem exists_h3W12CutoffBump_uniform_lipschitz :
    ∃ C : ℝ≥0,
      ∀ n : ℕ,
        LipschitzWith C
          (h3W12CutoffBump n :
            H3FourierPoint3 → ℝ) := by
  obtain ⟨C, hC⟩ :=
    exists_h3W12CutoffBump_base_lipschitz

  refine ⟨C, ?_⟩

  intro n

  have hComp :=
    hC.comp
      (h3W12CutoffScale_lipschitz n)

  have hFun :
      (h3W12CutoffBump n :
          H3FourierPoint3 → ℝ)
        =
      (h3W12CutoffBump 0 :
          H3FourierPoint3 → ℝ) ∘
        (fun x : H3FourierPoint3 =>
          ((n : ℝ) + 1)⁻¹ • x) := by
    funext x
    exact
      h3W12CutoffBump_eq_base_scaled n x

  rw [hFun]

  simpa only [
    mul_one
  ] using hComp

/-! ## Uniform derivative bounds -/

/-- Every coordinate derivative of every cutoff is bounded by one finite
constant depending only on the chosen coordinate direction. -/
theorem exists_h3W12CutoffBumpLineDerivative_uniform_bound
    (a : PrimeTensor.Axis Depth.three) :
    ∃ C : ℝ,
      0 ≤ C
        ∧
      ∀ (n : ℕ) (x : H3FourierPoint3),
        ‖h3W12CutoffBumpLineDerivative n a x‖
          ≤
        C := by
  obtain ⟨K, hK⟩ :=
    exists_h3W12CutoffBump_uniform_lipschitz

  let C : ℝ :=
    (K : ℝ) * ‖h3FourierAxisDirection a‖

  refine
    ⟨C, ?_, ?_⟩

  · unfold C
    positivity

  · intro n x

    have hDiff :
        DifferentiableAt ℝ
          (h3W12CutoffBump n :
            H3FourierPoint3 → ℝ)
          x :=
      ((h3W12CutoffBump_contDiff n).differentiable
        (by simp)).differentiableAt

    have hOp :
        ‖fderiv ℝ
            (h3W12CutoffBump n :
              H3FourierPoint3 → ℝ)
            x‖
          ≤
        (K : ℝ) := by
      exact
        hDiff.hasFDerivAt.le_of_lipschitz
          (hK n)

    unfold h3W12CutoffBumpLineDerivative

    calc
      ‖(fderiv ℝ
          (h3W12CutoffBump n :
            H3FourierPoint3 → ℝ)
          x)
          (h3FourierAxisDirection a)‖
          ≤
        ‖fderiv ℝ
            (h3W12CutoffBump n :
              H3FourierPoint3 → ℝ)
            x‖
          *
        ‖h3FourierAxisDirection a‖ := by
          exact
            ContinuousLinearMap.le_opNorm _ _
      _ ≤
        (K : ℝ) *
          ‖h3FourierAxisDirection a‖ := by
            exact
              mul_le_mul_of_nonneg_right
                hOp
                (norm_nonneg _)
      _ = C := by
        rfl

/-! ## Domination of the complete derivative remainder -/

/-- The derivative cutoff remainder is uniformly dominated by a constant
multiple of the original Schwartz function. -/
theorem exists_h3W12CutoffDerivativeRemainder_uniform_bound
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (a : PrimeTensor.Axis Depth.three) :
    ∃ C : ℝ,
      0 ≤ C
        ∧
      ∀ (n : ℕ) (x : H3FourierPoint3),
        ‖h3W12CutoffDerivativeRemainder n φ a x‖
          ≤
        C * ‖φ x‖ := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_h3W12CutoffBumpLineDerivative_uniform_bound a

  refine
    ⟨C, hC0, ?_⟩

  intro n x

  rw [
    h3W12CutoffDerivativeRemainder_apply,
    norm_mul
  ]

  exact
    mul_le_mul_of_nonneg_right
      (hC n x)
      (norm_nonneg _)

end

end Euclidean
end Bridge
end PrimeTensor
