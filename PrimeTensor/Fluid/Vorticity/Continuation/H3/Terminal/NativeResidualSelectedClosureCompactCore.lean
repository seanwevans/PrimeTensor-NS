import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSelectedClosureTraceDecay
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Compact positive superlevels of the selected-closure terminal trace

The canonical terminal trace on the selected spatial closure is uniformly
continuous and vanishes along every closure-valued sequence escaping to
infinity.

This implies compact localization of every positive trace level.

For `δ > 0`, consider the closure superlevel

    { y | δ ≤ dist (trace y) 0 }.

It is closed by continuity of the trace.  It is bounded because otherwise one
could choose points in the superlevel escaping farther and farther from a fixed
selected basepoint.  That would produce a closure-valued spatial escape along
which the trace must tend to zero, contradicting the uniform lower bound `δ`.

The selected spatial closure is a closed subspace of the proper finite
dimensional space `Point3`, hence is proper.  Closed plus bounded therefore
gives compactness.

Since the previous nonzero-core theorem supplies a positive-radius
neighborhood on which the trace stays away from zero, at least one positive
superlevel is nonempty and compact.

Thus the escape-side obstruction now contains a genuinely compact nonzero
terminal core, while the closure trace still vanishes at spatial infinity.
No compact-support assertion is made.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualSelectedClosureCompactCore
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Positive superlevels -/

/--
The `δ`-superlevel of the magnitude of the canonical selected-closure terminal
trace.
-/
def H3TerminalComplementGradientSelectedClosureSuperlevel
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (δ : ℝ) :
    Set (H3TerminalSelectedSpatialClosure x) :=
  {
    y |
      δ
        ≤
      dist
        (
          h3TerminalComplementGradientSelectedClosureTraceValue
            hModulus
            y
        )
        0
  }

/--
Every selected-closure trace superlevel is closed.
-/
theorem selectedClosureSuperlevel_isClosed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (δ : ℝ) :
    IsClosed
      (
        H3TerminalComplementGradientSelectedClosureSuperlevel
          hModulus
          δ
      ) := by

  have hContinuousTrace :
      Continuous
        (
          h3TerminalComplementGradientSelectedClosureTraceValue
            hModulus
        ) :=
    selectedClosureTraceValue_continuous
      hModulus

  have hContinuousMagnitude :
      Continuous
        (
          fun y : H3TerminalSelectedSpatialClosure x =>
            dist
              (
                h3TerminalComplementGradientSelectedClosureTraceValue
                  hModulus
                  y
              )
              0
        ) :=
    hContinuousTrace.dist
      continuous_const

  unfold
    H3TerminalComplementGradientSelectedClosureSuperlevel

  exact
    isClosed_Ici.preimage
      hContinuousMagnitude

/-! ## Positive superlevels are bounded under closure decay -/

/--
If the canonical selected-closure trace vanishes along every spatial escape,
then every strictly positive superlevel is bounded.
-/
theorem selectedClosureSuperlevel_isBounded_of_vanishesAtInfinity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hVanish :
      H3TerminalComplementGradientSelectedClosureTraceVanishesAtInfinity
        hModulus)
    {δ : ℝ}
    (hδ :
      0 < δ) :
    Bornology.IsBounded
      (
        H3TerminalComplementGradientSelectedClosureSuperlevel
          hModulus
          δ
      ) := by

  let S :
      Set (H3TerminalSelectedSpatialClosure x) :=
    H3TerminalComplementGradientSelectedClosureSuperlevel
      hModulus
      δ

  let c :
      H3TerminalSelectedSpatialClosure x :=
    h3TerminalSelectedSpatialClosurePoint
      x
      0

  by_contra hNotBounded

  have hNoBall :
      ∀ r : ℝ,
        ¬
          S
            ⊆
          Metric.closedBall c r := by

    intro r hr

    apply hNotBounded

    exact
      (
        Metric.isBounded_iff_subset_closedBall
          c
      ).2
        ⟨
          r,
          hr
        ⟩

  have hFarChoice :
      ∀ n : ℕ,
        ∃ y : H3TerminalSelectedSpatialClosure x,
          y ∈ S
            ∧
          (n : ℝ) < dist y c := by

    intro n

    have hNotSubset :=
      hNoBall (n : ℝ)

    rw [Set.not_subset] at hNotSubset

    obtain
      ⟨
        y,
        hyS,
        hyNotBall
      ⟩ :=
      hNotSubset

    refine
      ⟨
        y,
        hyS,
        ?_
      ⟩

    rw [Metric.mem_closedBall] at hyNotBall

    exact
      lt_of_not_ge
        hyNotBall

  choose y hyS hyFar using
    hFarChoice

  have hEscape :
      Tendsto
        (
          fun n : ℕ =>
            dist
              (0 : Point3)
              (y n).1
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro R

    obtain
      ⟨
        N : ℕ,
        hN
      ⟩ :=
      exists_nat_gt
        (
          R
            +
          dist
            (0 : Point3)
            c.1
        )

    filter_upwards
      [eventually_ge_atTop N]
      with n hn

    have hNatLarge :
        R
            +
          dist
            (0 : Point3)
            c.1
          <
        (n : ℝ) :=
      lt_of_lt_of_le
        hN
        (
          by
            exact_mod_cast hn
        )

    have hFarSubtype :
        (n : ℝ) < dist (y n) c :=
      hyFar n

    have hFarAmbient :
        (n : ℝ)
          <
        dist
          (y n).1
          c.1 := by

      simpa only [
        Subtype.dist_eq
      ] using
        hFarSubtype

    have hTriangle :
        dist
            (y n).1
            c.1
          ≤
        dist
            (y n).1
            (0 : Point3)
          +
        dist
            (0 : Point3)
            c.1 :=
      dist_triangle
        (y n).1
        (0 : Point3)
        c.1

    have hR :
        R
          <
        dist
          (y n).1
          (0 : Point3) := by
      linarith

    simpa only [dist_comm] using
      le_of_lt hR

  have hTraceZero :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalComplementGradientSelectedClosureTraceValue
              hModulus
              (y n)
        )
        atTop
        (𝓝 0) :=
    hVanish
      y
      hEscape

  rw [Metric.tendsto_atTop] at hTraceZero

  obtain
    ⟨
      N,
      hN
    ⟩ :=
    hTraceZero
      δ
      hδ

  have hSmall :
      dist
          (
            h3TerminalComplementGradientSelectedClosureTraceValue
              hModulus
              (y N)
          )
          0
        <
      δ :=
    hN
      N
      le_rfl

  have hLarge :
      δ
        ≤
      dist
        (
          h3TerminalComplementGradientSelectedClosureTraceValue
            hModulus
            (y N)
        )
        0 := by

    have hySN :
        y N ∈
          H3TerminalComplementGradientSelectedClosureSuperlevel
            hModulus
            δ := by

      simpa only [S] using
        hyS N

    exact
      hySN

  exact
    (
      not_lt_of_ge
        hLarge
    )
      hSmall

/-! ## Compactness of positive superlevels -/

/--
Every strictly positive selected-closure trace superlevel is compact when the
closure trace vanishes at infinity.
-/
theorem selectedClosureSuperlevel_isCompact_of_vanishesAtInfinity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hVanish :
      H3TerminalComplementGradientSelectedClosureTraceVanishesAtInfinity
        hModulus)
    {δ : ℝ}
    (hδ :
      0 < δ) :
    IsCompact
      (
        H3TerminalComplementGradientSelectedClosureSuperlevel
          hModulus
          δ
      ) := by

  letI :
      ProperSpace
        (H3TerminalSelectedSpatialClosure x) :=
    ProperSpace.of_isClosed
      isClosed_closure

  exact
    (
      Metric.isCompact_iff_isClosed_bounded
    ).2
      ⟨
        selectedClosureSuperlevel_isClosed
          hModulus
          δ,
        selectedClosureSuperlevel_isBounded_of_vanishesAtInfinity
          hModulus
          hVanish
          hδ
      ⟩

/-! ## A nonempty compact positive terminal core -/

/--
The canonical selected-closure trace has a nonempty compact positive
superlevel.
-/
def H3TerminalComplementGradientHasNonemptyCompactSelectedClosureCore
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    (
      H3TerminalComplementGradientSelectedClosureSuperlevel
        hModulus
        δ
    ).Nonempty
      ∧
    IsCompact
      (
        H3TerminalComplementGradientSelectedClosureSuperlevel
          hModulus
          δ
      )

/--
A nonzero selected-closure neighborhood together with closure-level decay at
infinity produces a nonempty compact positive terminal core.
-/
theorem nonemptyCompactSelectedClosureCore_of_nonzeroNeighborhood_of_vanishesAtInfinity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hNeighborhood :
      H3TerminalComplementGradientHasNonzeroSelectedClosureNeighborhood
        hModulus)
    (hVanish :
      H3TerminalComplementGradientSelectedClosureTraceVanishesAtInfinity
        hModulus) :
    H3TerminalComplementGradientHasNonemptyCompactSelectedClosureCore
      hModulus := by

  obtain
    ⟨
      y,
      ρ,
      hρ,
      δ,
      hδ,
      hNeighborhood
    ⟩ :=
    hNeighborhood

  have hySuperlevel :
      y ∈
        H3TerminalComplementGradientSelectedClosureSuperlevel
          hModulus
          δ := by

    exact
      hNeighborhood
        y
        (
          by
            simpa using
              hρ
        )

  refine
    ⟨
      δ,
      hδ,
      ⟨
        y,
        hySuperlevel
      ⟩,
      ?_
    ⟩

  exact
    selectedClosureSuperlevel_isCompact_of_vanishesAtInfinity
      hModulus
      hVanish
      hδ

/-! ## Compact-core escape-side package -/

/--
The escape-side obstruction contains

* a native pivot cluster at spatial infinity;
* a nonempty compact positive terminal core in the canonical closure trace;
* closure-level vanishing of the trace at infinity;
* quantitative finite-core versus infinity contrast.
-/
def H3TerminalNativeComplementHasPivotInfinityAndCompactClosureCore
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (T : ℝ)
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T) : Prop :=
  H3TerminalNativeComplementHasCofinalPivotClusterAtSpatialInfinity
      u p τ x T
    ∧
  H3TerminalComplementGradientHasNonemptyCompactSelectedClosureCore
      hModulus
    ∧
  H3TerminalComplementGradientSelectedClosureTraceVanishesAtInfinity
      hModulus
    ∧
  H3TerminalComplementGradientHasFiniteCoreInfinityContrast
      u p x T

/--
Under endpoint temporal control, selected spatial equicontinuity, terminal
decay at infinity, and eventual boundedness of the residual logarithm, failure
of the canonical native factor forces either

* pivot behavior at infinity together with a nonempty compact positive
  terminal core in the selected-closure trace; or
* bounded selected range with positive terminal spatial contrast and positive
  witness separation.
-/
theorem nativeComplement_noCanonicalFactor_forces_pivotInfinityAndCompactClosureCore_or_boundedTerminalContrast
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hEndpoint :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u p τ x T)
    (hSpatialEquicontinuity :
      H3TerminalComplementGradientSelectedSpatialEquicontinuity
        u p τ x)
    (hDecay :
      H3TerminalComplementGradientSelectedTerminalDecayAtInfinity
        u p x T)
    (hResidualBounded :
      H3TerminalNativeComplementResidualLogEventuallyBounded
        u p τ x)
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x) :
    let hTerminalModulus :
        H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
          u p x T :=
      selectedTerminalSpatialUniformModulus_of_spatialEquicontinuity_of_endpointTemporalModulus
        hTau
        hSpatialEquicontinuity
        hEndpoint
    H3TerminalNativeComplementHasPivotInfinityAndCompactClosureCore
        u p τ x T hTerminalModulus
      ∨
    (
      Bornology.IsBounded (Set.range x)
        ∧
      H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrastSeparation
        u p x T
    ) := by

  dsimp only

  let hTerminalModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T :=
    selectedTerminalSpatialUniformModulus_of_spatialEquicontinuity_of_endpointTemporalModulus
      hTau
      hSpatialEquicontinuity
      hEndpoint

  rcases
    nativeComplement_noCanonicalFactor_forces_pivotInfinityAndC0ClosureCore_or_boundedTerminalContrast
      hTau
      hEndpoint
      hSpatialEquicontinuity
      hDecay
      hResidualBounded
      hNoFactor
    with
    hEscapeSide | hContrast

  · left

    have hCompactCore :
        H3TerminalComplementGradientHasNonemptyCompactSelectedClosureCore
          hTerminalModulus :=
      nonemptyCompactSelectedClosureCore_of_nonzeroNeighborhood_of_vanishesAtInfinity
        hTerminalModulus
        hEscapeSide.2.1
        hEscapeSide.2.2.1

    exact
      ⟨
        hEscapeSide.1,
        hCompactCore,
        hEscapeSide.2.2.1,
        hEscapeSide.2.2.2
      ⟩

  · exact
      Or.inr
        hContrast

end

end Euclidean
end Bridge
end PrimeTensor
