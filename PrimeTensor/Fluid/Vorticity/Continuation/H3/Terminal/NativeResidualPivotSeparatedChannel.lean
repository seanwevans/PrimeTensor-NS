import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSpatialDecayPivot
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualDistinctClusters
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Pivot separation and a second native cluster channel

A cofinal spatial escape can, under the terminal decay frontier, produce a
native complementary residual cluster at the multiplicative pivot `1`.

If the full residual still has no canonical factor, that pivot cluster cannot
describe the whole asymptotic behavior.  This file makes the competing channel
explicit.

First, failure of the canonical factor alone forces a cofinal residual
refinement whose logarithmic coordinate stays a fixed positive distance from
zero, equivalently from the pivot `1`.

Second, if the residual logarithm is eventually bounded, properness of `ℝ`
extracts a convergent cofinal subrefinement of that pivot-separated branch.
Its limit is the logarithm of a finite native factor `q`, and the positive
separation forces `q ≠ 1`.

Therefore, in the bounded-residual case, a pivot cluster at spatial infinity
together with failure of the full canonical factor yields two incompatible
native asymptotic channels:

* a cofinal pivot cluster `1`;
* another cofinal finite native factor `q ≠ 1`.

This does not assert that the second channel is spatially bounded or escaping;
it classifies the residual asymptotics only.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## A cofinal branch separated from the pivot -/

/--
Some cofinal refinement of the exact residual logarithm stays a fixed positive
distance from zero, the logarithmic coordinate of the native pivot `1`.
-/
def H3TerminalNativeComplementHasCofinalPivotSeparatedBranch
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  ∃ ε : ℝ,
    0 < ε
      ∧
    ∃ k : ℕ → ℕ,
      Tendsto k atTop atTop
        ∧
      ∀ j : ℕ,
        ε
          ≤
        dist
          (
            h3TerminalNativeComplementResidualLogSequence
              u p τ x (k j)
          )
          0

/--
Failure of the full canonical native factor always produces a cofinal residual
branch separated from the pivot.

Indeed, a positive gap between two cofinal residual refinements forces at
least one endpoint of each pair to lie at distance at least half the gap from
zero.  A cofinal extraction selects one side persistently.
-/
theorem cofinalPivotSeparatedBranch_of_noCanonicalFactor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x) :
    H3TerminalNativeComplementHasCofinalPivotSeparatedBranch
      u p τ x := by

  obtain
    ⟨
      ε,
      hε,
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      hGap
    ⟩ :=
    (
      not_nativeComplementHasCanonicalFactor_iff_cofinalGap
        u p τ x
    ).1
      hNoFactor

  let R : ℕ → ℝ :=
    h3TerminalNativeComplementResidualLogSequence
      u p τ x

  let S : ℕ → Prop :=
    fun j : ℕ =>
      ε / 2
        ≤
      dist
        (R (k₁ j))
        0

  let Q : ℕ → Prop :=
    fun j : ℕ =>
      ε / 2
        ≤
      dist
        (R (k₂ j))
        0

  have hSQ :
      ∀ j : ℕ,
        S j ∨ Q j := by

    intro j

    by_cases hS :
        S j

    · exact
        Or.inl hS

    · right

      have hSlt :
          dist
              (R (k₁ j))
              0
            <
          ε / 2 :=
        lt_of_not_ge hS

      by_contra hQ

      have hQlt :
          dist
              (R (k₂ j))
              0
            <
          ε / 2 :=
        lt_of_not_ge hQ

      have hTriangle :
          dist
              (R (k₁ j))
              (R (k₂ j))
            ≤
          dist
              (R (k₁ j))
              0
            +
          dist
              0
              (R (k₂ j)) :=
        dist_triangle
          (R (k₁ j))
          0
          (R (k₂ j))

      have hQlt' :
          dist
              0
              (R (k₂ j))
            <
          ε / 2 := by

        simpa only [dist_comm] using
          hQlt

      have hLarge :
          ε
            ≤
          dist
            (R (k₁ j))
            (R (k₂ j)) := by

        dsimp only [R]

        exact
          hGap j

      linarith

  have hHalfPos :
      0 < ε / 2 :=
    half_pos hε

  by_cases hSFreq :
      ∃ᶠ j : ℕ in atTop,
        S j

  · obtain
      ⟨
        φ,
        hφStrict,
        hφS
      ⟩ :=
      extraction_of_frequently_atTop
        hSFreq

    let K : ℕ → ℕ :=
      fun j : ℕ =>
        k₁ (φ j)

    have hKTop :
        Tendsto K atTop atTop := by

      dsimp only [K]

      exact
        hk₁Top.comp
          hφStrict.tendsto_atTop

    refine
      ⟨
        ε / 2,
        hHalfPos,
        K,
        hKTop,
        ?_
      ⟩

    intro j

    have h :=
      hφS j

    simpa only [S, R, K] using
      h

  · have hEventuallyNotS :
        ∀ᶠ j : ℕ in atTop,
          ¬ S j :=
      (
        not_frequently
      ).1
        hSFreq

    have hEventuallyQ :
        ∀ᶠ j : ℕ in atTop,
          Q j := by

      filter_upwards
        [hEventuallyNotS]
        with j hj

      exact
        (hSQ j).resolve_left
          hj

    obtain
      ⟨
        φ,
        hφStrict,
        hφQ
      ⟩ :=
      extraction_of_eventually_atTop
        hEventuallyQ

    let K : ℕ → ℕ :=
      fun j : ℕ =>
        k₂ (φ j)

    have hKTop :
        Tendsto K atTop atTop := by

      dsimp only [K]

      exact
        hk₂Top.comp
          hφStrict.tendsto_atTop

    refine
      ⟨
        ε / 2,
        hHalfPos,
        K,
        hKTop,
        ?_
      ⟩

    intro j

    have h :=
      hφQ j

    simpa only [Q, R, K] using
      h

/-! ## Eventual residual boundedness -/

/--
The exact complementary residual logarithm is eventually bounded on the full
selected sequence.
-/
def H3TerminalNativeComplementResidualLogEventuallyBounded
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  ∃ N : ℕ,
    ∃ C : ℝ,
      ∀ n : ℕ,
        N ≤ n →
        abs
          (
            h3TerminalNativeComplementResidualLogSequence
              u p τ x n
          )
          ≤ C

/--
A finite native cluster factor different from the pivot `1`, realized on a
cofinal refinement of the original selected spacetime sequence.
-/
def H3TerminalNativeComplementHasDistinctCofinalFactorFromPivot
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  ∃ q : MulReal,
    q ≠ (1 : MulReal)
      ∧
    ∃ k : ℕ → ℕ,
      Tendsto k atTop atTop
        ∧
      H3TerminalNativeComplementProportionalityFactor
        u p
        (fun j : ℕ => τ (k j))
        (fun j : ℕ => x (k j))
        q

/-! ## Bounded pivot-separated branch gives a second finite factor -/

/--
If the full residual has no canonical factor but its logarithm is eventually
bounded, then there is a cofinal finite native cluster factor `q ≠ 1`.
-/
theorem distinctCofinalFactorFromPivot_of_noCanonicalFactor_of_eventuallyBounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x)
    (hBounded :
      H3TerminalNativeComplementResidualLogEventuallyBounded
        u p τ x) :
    H3TerminalNativeComplementHasDistinctCofinalFactorFromPivot
      u p τ x := by

  obtain
    ⟨
      ε,
      hε,
      k,
      hkTop,
      hSeparated
    ⟩ :=
    cofinalPivotSeparatedBranch_of_noCanonicalFactor
      hNoFactor

  obtain
    ⟨
      N,
      C,
      hBound
    ⟩ :=
    hBounded

  have hEventuallyN :
      ∀ᶠ j : ℕ in atTop,
        N ≤ k j :=
    (
      tendsto_atTop.1
        hkTop
    )
      N

  obtain
    ⟨
      φ,
      hφStrict,
      hφN
    ⟩ :=
    extraction_of_eventually_atTop
      hEventuallyN

  let R : ℕ → ℝ :=
    h3TerminalNativeComplementResidualLogSequence
      u p τ x

  let S : ℕ → ℝ :=
    fun j : ℕ =>
      R (k (φ j))

  let C₀ : ℝ :=
    max C 0

  have hSMem :
      ∀ j : ℕ,
        S j ∈ Set.Icc (-C₀) C₀ := by

    intro j

    have hAbs :
        abs (S j) ≤ C := by

      dsimp only [S, R]

      exact
        hBound
          (k (φ j))
          (hφN j)

    have hAbs₀ :
        abs (S j) ≤ C₀ :=
      le_trans
        hAbs
        (le_max_left C 0)

    exact
      abs_le.mp
        hAbs₀

  obtain
    ⟨
      r,
      _hrMem,
      ψ,
      hψStrict,
      hLimit
    ⟩ :=
    tendsto_subseq_of_bounded
      (Metric.isBounded_Icc (-C₀) C₀)
      hSMem

  have hDistance :
      Tendsto
        (
          fun j : ℕ =>
            dist
              (S (ψ j))
              0
        )
        atTop
        (𝓝 (dist r 0)) := by

    exact
      hLimit.dist
        tendsto_const_nhds

  have hLimitSeparated :
      ε ≤ dist r 0 := by

    apply
      ge_of_tendsto
        hDistance

    filter_upwards with j

    dsimp only [S, R]

    exact
      hSeparated
        (φ (ψ j))

  have hrNe :
      r ≠ 0 := by

    intro hr

    have hεZero :
        ε ≤ 0 := by

      simpa [hr] using
        hLimitSeparated

    linarith

  obtain
    ⟨
      q,
      hq
    ⟩ :=
    PrimeTensor.Bridge.MulReal.logValue_surjective
      r

  have hqNe :
      q ≠ (1 : MulReal) := by

    intro hqOne

    apply hrNe

    rw [
      ← hq,
      hqOne,
      PrimeTensor.Bridge.MulReal.logValue_one
    ]

  let K : ℕ → ℕ :=
    fun j : ℕ =>
      k (φ (ψ j))

  have hφψTop :
      Tendsto
        (fun j : ℕ => φ (ψ j))
        atTop
        atTop := by

    exact
      hφStrict.tendsto_atTop.comp
        hψStrict.tendsto_atTop

  have hKTop :
      Tendsto K atTop atTop := by

    dsimp only [K]

    exact
      hkTop.comp
        hφψTop

  have hFactor :
      H3TerminalNativeComplementProportionalityFactor
        u p
        (fun j : ℕ => τ (K j))
        (fun j : ℕ => x (K j))
        q := by

    unfold
      H3TerminalNativeComplementProportionalityFactor

    apply
      (
        terminalNativeNatConvergesTo_iff_logValue_tendsto
          (
            fun j : ℕ =>
              PrimeTensor.MulReal.ratio
                (
                  h3TerminalNativeGradientForPair
                    u p
                    (τ (K j))
                    (x (K j))
                )
                (
                  h3TerminalSelectedSignedNativeCurlForPair
                    u p
                    (τ (K j))
                    (x (K j))
                )
          )
          q
      ).2

    rw [hq]

    simpa [
      h3TerminalNativeComplementResidualLogSequence,
      S,
      R,
      K,
      Function.comp_def
    ] using
      hLimit

  exact
    ⟨
      q,
      hqNe,
      K,
      hKTop,
      hFactor
    ⟩

/-! ## Pivot cluster plus a distinct finite channel -/

/--
The residual has both

* a cofinal pivot cluster at spatial infinity; and
* another cofinal finite native factor different from the pivot.
-/
def H3TerminalNativeComplementHasPivotClusterAndDistinctFiniteChannel
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  H3TerminalNativeComplementHasCofinalPivotClusterAtSpatialInfinity
      u p τ x T
    ∧
  H3TerminalNativeComplementHasDistinctCofinalFactorFromPivot
      u p τ x

/--
In the eventually bounded residual regime, a pivot cluster at spatial infinity
and failure of the full canonical factor force a second finite native channel
`q ≠ 1`.
-/
theorem pivotClusterAndDistinctFiniteChannel_of_pivotCluster_of_noCanonicalFactor_of_eventuallyBounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hPivot :
      H3TerminalNativeComplementHasCofinalPivotClusterAtSpatialInfinity
        u p τ x T)
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x)
    (hBounded :
      H3TerminalNativeComplementResidualLogEventuallyBounded
        u p τ x) :
    H3TerminalNativeComplementHasPivotClusterAndDistinctFiniteChannel
      u p τ x T := by

  exact
    ⟨
      hPivot,
      distinctCofinalFactorFromPivot_of_noCanonicalFactor_of_eventuallyBounded
        hNoFactor
        hBounded
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
