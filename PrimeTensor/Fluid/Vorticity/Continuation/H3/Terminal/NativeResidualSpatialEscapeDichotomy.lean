import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSpatialClusterDichotomy
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Spatial escape-to-infinity alternative for the terminal residual

The geometric residual obstruction was previously classified as

    unbounded selected spatial sequence

or, in the bounded case,

    two distinct finite `Point3` cluster points.

This file sharpens the unbounded side to an actual cofinal escape.

For finite-dimensional `Point3`, an unbounded selected sequence admits a
strictly increasing refinement `k` such that

    dist 0 (x (k j)) → +∞.

Conversely, such an escaping refinement makes the full selected range
unbounded.

Combining this with terminal-time convergence gives the concrete alternative:

* one cofinal selected spacetime refinement approaches `T` while escaping
  spatially to infinity; or
* the selected points have two distinct finite spatial cluster points.

This remains a geometric classification.  No physical recentering or
translation-invariance argument is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualSpatialEscapeDichotomy
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Cofinal spatial escape -/

/--
The selected points have a cofinal refinement whose distance from the origin
tends to `+∞`.
-/
def H3TerminalSelectedPointEscapesToInfinity
    (x : ℕ → Point3) : Prop :=
  ∃ k : ℕ → ℕ,
    Tendsto k atTop atTop
      ∧
    Tendsto
      (
        fun j : ℕ =>
          dist
            (0 : Point3)
            (x (k j))
      )
      atTop
      atTop

/--
If the selected-point range is unbounded, then for every natural spatial
radius the sequence is frequently outside that radius.
-/
private theorem selectedPoint_frequently_far_of_unbounded
    {x : ℕ → Point3}
    (hUnbounded :
      ¬ Bornology.IsBounded (Set.range x)) :
    ∀ M : ℕ,
      ∃ᶠ n : ℕ in atTop,
        (M : ℝ)
          <
        dist
          (0 : Point3)
          (x n) := by

  intro M

  rw [frequently_atTop]

  intro N

  by_contra hNoFar

  push Not at hNoFar

  have hPrefixFinite :
      (x '' Set.Iio N).Finite :=
    (Set.finite_Iio N).image x

  have hPrefixBounded :
      Bornology.IsBounded
        (x '' Set.Iio N) :=
    hPrefixFinite.isBounded

  have hTailBallBounded :
      Bornology.IsBounded
        (
          Metric.closedBall
            (0 : Point3)
            (M : ℝ)
        ) :=
    Metric.isBounded_closedBall

  have hRangeSubset :
      Set.range x
        ⊆
      (
        (x '' Set.Iio N)
          ∪
        Metric.closedBall
          (0 : Point3)
          (M : ℝ)
      ) := by

    rintro y
      ⟨
        n,
        rfl
      ⟩

    by_cases hn :
        n < N

    · exact
        Or.inl
          ⟨
            n,
            hn,
            rfl
          ⟩

    · have hNn :
          N ≤ n :=
        Nat.le_of_not_gt
          hn

      have hLe :
          dist
              (x n)
              (0 : Point3)
            ≤
          (M : ℝ) := by

        simpa only [dist_comm] using
          hNoFar n hNn

      exact
        Or.inr
          (
            Metric.mem_closedBall.mpr
              hLe
          )

  have hRangeBounded :
      Bornology.IsBounded
        (Set.range x) :=
    (
      hPrefixBounded.union
        hTailBallBounded
    ).subset
      hRangeSubset

  exact
    hUnbounded
      hRangeBounded

/--
Every unbounded selected-point sequence has a cofinal refinement escaping to
spatial infinity.
-/
theorem selectedPointEscapesToInfinity_of_unbounded
    {x : ℕ → Point3}
    (hUnbounded :
      ¬ Bornology.IsBounded (Set.range x)) :
    H3TerminalSelectedPointEscapesToInfinity
      x := by

  have hFarFrequently :
      ∀ M : ℕ,
        ∃ᶠ n : ℕ in atTop,
          (M : ℝ)
            <
          dist
            (0 : Point3)
            (x n) :=
    selectedPoint_frequently_far_of_unbounded
      hUnbounded

  obtain
    ⟨
      k,
      hkStrict,
      hkFar
    ⟩ :=
    extraction_forall_of_frequently
      hFarFrequently

  have hkTop :
      Tendsto k atTop atTop :=
    hkStrict.tendsto_atTop

  have hDistanceTop :
      Tendsto
        (
          fun j : ℕ =>
            dist
              (0 : Point3)
              (x (k j))
        )
        atTop
        atTop := by

    exact
      Filter.tendsto_atTop_mono
        (
          fun j : ℕ =>
            le_of_lt
              (hkFar j)
        )
        (
          tendsto_natCast_atTop_atTop :
            Tendsto
              (fun j : ℕ => (j : ℝ))
              atTop
              atTop
        )

  exact
    ⟨
      k,
      hkTop,
      hDistanceTop
    ⟩

/--
A cofinal refinement escaping spatially to infinity forces the selected-point
range to be unbounded.
-/
theorem unbounded_of_selectedPointEscapesToInfinity
    {x : ℕ → Point3}
    (hEscape :
      H3TerminalSelectedPointEscapesToInfinity
        x) :
    ¬ Bornology.IsBounded (Set.range x) := by

  rintro hBounded

  obtain
    ⟨
      k,
      _hkTop,
      hDistanceTop
    ⟩ :=
    hEscape

  obtain
    ⟨
      R,
      hRangeBall
    ⟩ :=
    hBounded.subset_closedBall
      (0 : Point3)

  have hEventuallyFar :
      ∀ᶠ j : ℕ in atTop,
        R + 1
          ≤
        dist
          (0 : Point3)
          (x (k j)) :=
    (
      Filter.tendsto_atTop.1
        hDistanceTop
    )
      (R + 1)

  rw [eventually_atTop] at hEventuallyFar

  obtain
    ⟨
      J,
      hJ
    ⟩ :=
    hEventuallyFar

  have hFar :
      R + 1
        ≤
      dist
        (0 : Point3)
        (x (k J)) :=
    hJ J le_rfl

  have hInRange :
      x (k J) ∈ Set.range x :=
    ⟨
      k J,
      rfl
    ⟩

  have hNear :
      dist
          (0 : Point3)
          (x (k J))
        ≤
      R := by

    simpa only [dist_comm] using
      (
        Metric.mem_closedBall.mp
          (
            hRangeBall
              hInRange
          )
      )

  linarith

/--
Spatial unboundedness is exactly existence of a cofinal escape-to-infinity
refinement.
-/
theorem selectedPointEscapesToInfinity_iff_unbounded
    (x : ℕ → Point3) :
    H3TerminalSelectedPointEscapesToInfinity
        x
      ↔
    ¬ Bornology.IsBounded (Set.range x) := by

  constructor

  · exact
      unbounded_of_selectedPointEscapesToInfinity

  · exact
      selectedPointEscapesToInfinity_of_unbounded

/-! ## Terminal spacetime escape -/

/--
One cofinal refinement approaches the terminal time while its selected spatial
points escape to infinity.
-/
def H3TerminalSelectedPointSpatialEscapeAtTerminal
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  ∃ k : ℕ → ℕ,
    Tendsto k atTop atTop
      ∧
    Tendsto
      (fun j : ℕ => τ (k j))
      atTop
      (𝓝 T)
      ∧
    Tendsto
      (
        fun j : ℕ =>
          dist
            (0 : Point3)
            (x (k j))
      )
      atTop
      atTop

/--
Terminal-time convergence upgrades a spatial escape refinement to a spacetime
refinement that simultaneously approaches the terminal time.
-/
theorem selectedPointSpatialEscapeAtTerminal_of_tendsto_of_escape
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hEscape :
      H3TerminalSelectedPointEscapesToInfinity
        x) :
    H3TerminalSelectedPointSpatialEscapeAtTerminal
      τ x T := by

  obtain
    ⟨
      k,
      hkTop,
      hSpatial
    ⟩ :=
    hEscape

  exact
    ⟨
      k,
      hkTop,
      hTau.comp hkTop,
      hSpatial
    ⟩

/-! ## Refined geometric dichotomy -/

/--
Persistent cofinal point separation forces either an actual cofinal escape to
spatial infinity or two distinct finite spatial cluster points.
-/
theorem selectedPoint_escape_or_twoDistinctClusterPoints_of_persistentCofinalSeparation
    {x : ℕ → Point3}
    (hSeparated :
      H3TerminalSelectedPointPersistentCofinalSeparation
        x) :
    H3TerminalSelectedPointEscapesToInfinity
        x
      ∨
    H3TerminalSelectedPointHasTwoDistinctClusterPoints
        x := by

  rcases
    selectedPoint_unbounded_or_twoDistinctClusterPoints_of_persistentCofinalSeparation
      hSeparated
    with
    hUnbounded | hClusters

  · exact
      Or.inl
        (
          selectedPointEscapesToInfinity_of_unbounded
            hUnbounded
        )

  · exact
      Or.inr hClusters

/--
Under terminal-time convergence and both selected uniform moduli, failure of
the full canonical native residual factor forces either

* a cofinal spacetime refinement approaching `T` while escaping spatially to
  infinity; or
* two distinct finite spatial cluster points.
-/
theorem selectedPoint_terminalEscape_or_twoDistinctClusterPoints_of_noCanonicalFactor_of_uniformModuli
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hTemporalModulus :
      H3TerminalComplementGradientSelectedTemporalUniformModulus
        u p τ x)
    (hSpatialModulus :
      H3TerminalComplementGradientSelectedSpatialUniformModulus
        u p τ x)
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x) :
    H3TerminalSelectedPointSpatialEscapeAtTerminal
        τ x T
      ∨
    H3TerminalSelectedPointHasTwoDistinctClusterPoints
        x := by

  rcases
    selectedPoint_unbounded_or_twoDistinctClusterPoints_of_noCanonicalFactor_of_uniformModuli
      hTau
      hTemporalModulus
      hSpatialModulus
      hNoFactor
    with
    hUnbounded | hClusters

  · exact
      Or.inl
        (
          selectedPointSpatialEscapeAtTerminal_of_tendsto_of_escape
            hTau
            (
              selectedPointEscapesToInfinity_of_unbounded
                hUnbounded
            )
        )

  · exact
      Or.inr hClusters

end

end Euclidean
end Bridge
end PrimeTensor
