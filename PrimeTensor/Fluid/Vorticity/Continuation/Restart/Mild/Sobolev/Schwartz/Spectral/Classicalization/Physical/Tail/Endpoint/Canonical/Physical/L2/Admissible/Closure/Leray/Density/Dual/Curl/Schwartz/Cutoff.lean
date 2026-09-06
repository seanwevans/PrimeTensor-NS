import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Sobolev
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Classicalization: compact cutoff family for the W¹,² graph

`Schwartz.Sobolev` reduced the remaining curl extension to one precise
approximation statement: the first-derivative `L²` graph of every real Schwartz
test must lie in the closure of graphs coming from transported compact weak
tests.

This file constructs the approximating family.

For `n : ℕ`, let `χₙ` be the standard smooth bump centered at zero with

    inner radius  n + 1,
    outer radius  2 (n + 1).

Thus

* `0 ≤ χₙ ≤ 1`;
* `χₙ = 1` on the closed ball of radius `n + 1`;
* `χₙ` has compact support;
* `χₙ` is `C^∞`.

For a real Schwartz function `φ`, the product

    χₙ φ

is therefore smooth and compactly supported, hence again Schwartz.

We then pull this compact Schwartz function back through the inverse physical /
Euclidean carrier equivalence and package it as an actual
`H3WeakTestFunction`.  Transporting that weak test forward gives exactly
`χₙ φ`.

Consequently every cutoff graph is literally an element of

    range h3WeakTestFourierRealFirstDerivativeGraph.

The next checkpoint only has to prove that these graphs converge to the graph
of `φ` in `L² × (L²)^3`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlSchwartzCutoff
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Expanding smooth cutoffs on the Euclidean carrier -/

/-- Smooth cutoff centered at zero, equal to one on radius `n + 1` and
supported in radius `2 (n + 1)`. -/
noncomputable def h3W12CutoffBump
    (n : ℕ) :
    ContDiffBump (0 : H3FourierPoint3) where
  rIn := (n : ℝ) + 1
  rOut := 2 * ((n : ℝ) + 1)
  rIn_pos := by
    positivity
  rIn_lt_rOut := by
    have hn : 0 ≤ (n : ℝ) := by positivity
    nlinarith

@[simp]
theorem h3W12CutoffBump_rIn
    (n : ℕ) :
    (h3W12CutoffBump n).rIn = (n : ℝ) + 1 := by
  rfl

@[simp]
theorem h3W12CutoffBump_rOut
    (n : ℕ) :
    (h3W12CutoffBump n).rOut =
      2 * ((n : ℝ) + 1) := by
  rfl

theorem h3W12CutoffBump_nonneg
    (n : ℕ)
    (x : H3FourierPoint3) :
    0 ≤ h3W12CutoffBump n x := by
  exact (h3W12CutoffBump n).nonneg

theorem h3W12CutoffBump_le_one
    (n : ℕ)
    (x : H3FourierPoint3) :
    h3W12CutoffBump n x ≤ 1 := by
  exact (h3W12CutoffBump n).le_one

theorem h3W12CutoffBump_hasCompactSupport
    (n : ℕ) :
    HasCompactSupport
      (h3W12CutoffBump n :
        H3FourierPoint3 → ℝ) := by
  exact (h3W12CutoffBump n).hasCompactSupport

theorem h3W12CutoffBump_contDiff
    (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (h3W12CutoffBump n :
        H3FourierPoint3 → ℝ) := by
  simpa using
    ((h3W12CutoffBump n).contDiff
      (n := (⊤ : ℕ∞)))

/-- The cutoff is exactly one throughout the expanding inner ball. -/
theorem h3W12CutoffBump_eq_one_of_norm_le
    (n : ℕ)
    {x : H3FourierPoint3}
    (hx : ‖x‖ ≤ (n : ℝ) + 1) :
    h3W12CutoffBump n x = 1 := by
  apply (h3W12CutoffBump n).one_of_mem_closedBall
  simpa only [
    Metric.mem_closedBall,
    dist_zero_right,
    h3W12CutoffBump_rIn
  ] using hx

/-! ## Cut a real Schwartz function by the expanding bump -/

/-- Compactly supported Schwartz cutoff `χₙ φ`. -/
noncomputable def h3W12CutoffSchwartz
    (n : ℕ)
    (φ : 𝓢(H3FourierPoint3, ℝ)) :
    𝓢(H3FourierPoint3, ℝ) := by
  have hCompact :
      HasCompactSupport
        (fun x : H3FourierPoint3 =>
          h3W12CutoffBump n x * φ x) := by
    exact
      (h3W12CutoffBump_hasCompactSupport n).mul_right

  have hSmooth :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : H3FourierPoint3 =>
          h3W12CutoffBump n x * φ x) := by
    exact
      (h3W12CutoffBump_contDiff n).mul
        (φ.smooth (⊤ : ℕ∞))

  exact
    hCompact.toSchwartzMap hSmooth

@[simp]
theorem h3W12CutoffSchwartz_apply
    (n : ℕ)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    (x : H3FourierPoint3) :
    h3W12CutoffSchwartz n φ x
      =
    h3W12CutoffBump n x * φ x := by
  rfl

theorem h3W12CutoffSchwartz_hasCompactSupport
    (n : ℕ)
    (φ : 𝓢(H3FourierPoint3, ℝ)) :
    HasCompactSupport
      (h3W12CutoffSchwartz n φ :
        H3FourierPoint3 → ℝ) := by
  unfold h3W12CutoffSchwartz
  exact
    (h3W12CutoffBump_hasCompactSupport n).mul_right

/-- On the inner ball the cutoff Schwartz test agrees pointwise with the
original Schwartz function. -/
theorem h3W12CutoffSchwartz_eq_of_norm_le
    (n : ℕ)
    (φ : 𝓢(H3FourierPoint3, ℝ))
    {x : H3FourierPoint3}
    (hx : ‖x‖ ≤ (n : ℝ) + 1) :
    h3W12CutoffSchwartz n φ x = φ x := by
  rw [
    h3W12CutoffSchwartz_apply,
    h3W12CutoffBump_eq_one_of_norm_le n hx,
    one_mul
  ]

/-! ## Compact Euclidean Schwartz tests as physical weak tests -/

/-- Pull a compact real Schwartz function on the Euclidean carrier back to the
physical carrier and package it as an actual scalar weak test. -/
noncomputable def h3FourierCompactRealSchwartzToWeakTest
    (g : 𝓢(H3FourierPoint3, ℝ))
    (hg :
      HasCompactSupport
        (g : H3FourierPoint3 → ℝ)) :
    H3WeakTestFunction :=
  ⟨
    fun y : Point3 =>
      g (h3FourierPoint3EquivPoint3.symm y),
    (g.smooth (⊤ : ℕ∞)).comp
      h3FourierPoint3EquivPoint3.symm.contDiff,
    hg.comp_homeomorph
      h3FourierPoint3EquivPoint3.symm.toHomeomorph,
    Set.subset_univ _
  ⟩

@[simp]
theorem h3FourierCompactRealSchwartzToWeakTest_apply
    (g : 𝓢(H3FourierPoint3, ℝ))
    (hg :
      HasCompactSupport
        (g : H3FourierPoint3 → ℝ))
    (y : Point3) :
    h3FourierCompactRealSchwartzToWeakTest g hg y
      =
    g (h3FourierPoint3EquivPoint3.symm y) := by
  rfl

/-- Transporting the preceding physical weak test forward recovers the
original compact Euclidean Schwartz function exactly. -/
theorem h3WeakTestToFourierRealSchwartz_compactPullback
    (g : 𝓢(H3FourierPoint3, ℝ))
    (hg :
      HasCompactSupport
        (g : H3FourierPoint3 → ℝ)) :
    h3WeakTestToFourierRealSchwartz
        (h3FourierCompactRealSchwartzToWeakTest g hg)
      =
    g := by
  ext x
  change
    g
      (h3FourierPoint3EquivPoint3.symm
        (h3FourierPoint3EquivPoint3 x))
      =
    g x
  rw [h3FourierPoint3EquivPoint3.symm_apply_apply]

/-! ## The cutoff approximants are literally transported weak tests -/

/-- Physical weak test corresponding to the cutoff `χₙ φ`. -/
noncomputable def h3W12CutoffWeakTest
    (n : ℕ)
    (φ : 𝓢(H3FourierPoint3, ℝ)) :
    H3WeakTestFunction :=
  h3FourierCompactRealSchwartzToWeakTest
    (h3W12CutoffSchwartz n φ)
    (h3W12CutoffSchwartz_hasCompactSupport n φ)

theorem h3WeakTestToFourierRealSchwartz_cutoffWeakTest
    (n : ℕ)
    (φ : 𝓢(H3FourierPoint3, ℝ)) :
    h3WeakTestToFourierRealSchwartz
        (h3W12CutoffWeakTest n φ)
      =
    h3W12CutoffSchwartz n φ := by
  exact
    h3WeakTestToFourierRealSchwartz_compactPullback
      (h3W12CutoffSchwartz n φ)
      (h3W12CutoffSchwartz_hasCompactSupport n φ)

/-- Every cutoff first-derivative graph belongs to the exact range whose
closure appears in `H3TransportedWeakTestsDenseInRealW12Schwartz`. -/
theorem h3W12CutoffSchwartz_firstDerivativeGraph_mem_range
    (n : ℕ)
    (φ : 𝓢(H3FourierPoint3, ℝ)) :
    h3FourierRealSchwartzFirstDerivativeGraph
        (h3W12CutoffSchwartz n φ)
      ∈
    Set.range
      h3WeakTestFourierRealFirstDerivativeGraph := by
  refine
    ⟨h3W12CutoffWeakTest n φ, ?_⟩

  unfold h3WeakTestFourierRealFirstDerivativeGraph

  rw [
    h3WeakTestToFourierRealSchwartz_cutoffWeakTest
  ]

end

end Euclidean
end Bridge
end PrimeTensor
