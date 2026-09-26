import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSelectedClosureTraceContinuity

/-!
# Decay at infinity of the canonical selected-closure trace

The terminal decay frontier was originally stated only on selected spatial
points.  The canonical trace function is now uniformly continuous on the
ordinary selected spatial closure.

These two facts extend the decay statement to the entire closure.

Given any closure-valued sequence escaping to spatial infinity, approximate
each of its points by an actually selected point within one fixed small radius.
The selected approximants still escape to infinity.  Their actual terminal
complementary-gradient values therefore tend to zero by the original decay
frontier, while uniform continuity makes the closure trace values uniformly
close to those selected values.

Hence the canonical closure trace vanishes along every sequence in the
selected closure escaping to infinity.

Together with the positive-radius nonzero core neighborhood proved previously,
the closure trace is now a genuine `C₀`-type terminal object on its closed
spatial domain:

* uniformly continuous on the selected closure;
* nonzero on a positive-radius closure neighborhood;
* vanishing along every closure sequence escaping to infinity.

No compact-support assertion is made.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualSelectedClosureTraceDecay
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Closure-level decay at infinity -/

/--
The canonical terminal trace on the selected spatial closure vanishes along
every closure-valued sequence escaping to spatial infinity.
-/
def H3TerminalComplementGradientSelectedClosureTraceVanishesAtInfinity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T) : Prop :=
  ∀ y : ℕ → H3TerminalSelectedSpatialClosure x,
    Tendsto
        (
          fun j : ℕ =>
            dist
              (0 : Point3)
              (y j).1
        )
        atTop
        atTop
      →
    Tendsto
      (
        fun j : ℕ =>
          h3TerminalComplementGradientSelectedClosureTraceValue
            hModulus
            (y j)
      )
      atTop
      (𝓝 0)

/--
Selected-point terminal decay at infinity extends to the canonical trace on the
entire selected spatial closure.
-/
theorem selectedClosureTraceVanishesAtInfinity_of_terminalDecay
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hDecay :
      H3TerminalComplementGradientSelectedTerminalDecayAtInfinity
        u p x T) :
    H3TerminalComplementGradientSelectedClosureTraceVanishesAtInfinity
      hModulus := by

  intro y hEscape

  rw [Metric.tendsto_atTop]

  intro ε hε

  have hHalfPos :
      0 < ε / 2 := by
    linarith

  have hUniformContinuous :
      UniformContinuous
        (
          h3TerminalComplementGradientSelectedClosureTraceValue
            hModulus
        ) :=
    selectedClosureTraceValue_uniformContinuous
      hModulus

  rw [Metric.uniformContinuous_iff] at hUniformContinuous

  obtain
    ⟨
      ρ,
      hρ,
      hρControl
    ⟩ :=
    hUniformContinuous
      (ε / 2)
      hHalfPos

  have hApprox :
      ∀ j : ℕ,
        ∃ n : ℕ,
          dist
              (y j).1
              (x n)
            <
          ρ := by

    intro j

    exact
      (
        Metric.mem_closure_range_iff
      ).1
        (y j).2
        ρ
        hρ

  choose n hn using
    hApprox

  have hSelectedEscape :
      Tendsto
        (
          fun j : ℕ =>
            dist
              (0 : Point3)
              (x (n j))
        )
        atTop
        atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro R

    have hFar :
        ∀ᶠ j : ℕ in atTop,
          R + ρ
            ≤
          dist
            (0 : Point3)
            (y j).1 :=
      (
        tendsto_atTop.1
          hEscape
      )
        (R + ρ)

    filter_upwards
      [hFar]
      with j hj

    have hNear :
        dist
            (x (n j))
            (y j).1
          <
        ρ := by

      simpa only [dist_comm] using
        hn j

    have hTriangle :
        dist
            (0 : Point3)
            (y j).1
          ≤
        dist
            (0 : Point3)
            (x (n j))
          +
        dist
            (x (n j))
            (y j).1 :=
      dist_triangle
        (0 : Point3)
        (x (n j))
        (y j).1

    linarith

  have hSelectedZero :
      Tendsto
        (
          fun j : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x (n j))
        )
        atTop
        (𝓝 0) :=
    hDecay
      n
      hSelectedEscape

  rw [Metric.tendsto_atTop] at hSelectedZero

  obtain
    ⟨
      N,
      hN
    ⟩ :=
    hSelectedZero
      (ε / 2)
      hHalfPos

  refine
    ⟨
      N,
      ?_
    ⟩

  intro j hj

  let Y : H3TerminalSelectedSpatialClosure x :=
    y j

  let X : H3TerminalSelectedSpatialClosure x :=
    h3TerminalSelectedSpatialClosurePoint
      x
      (n j)

  have hClosureNear :
      dist Y X < ρ := by

    rw [Subtype.dist_eq]

    dsimp only [Y, X]

    simpa only [
      h3TerminalSelectedSpatialClosurePoint
    ] using
      hn j

  have hTraceNearRaw :
      dist
          (
            h3TerminalComplementGradientSelectedClosureTraceValue
              hModulus
              Y
          )
          (
            h3TerminalComplementGradientSelectedClosureTraceValue
              hModulus
              X
          )
        <
      ε / 2 :=
    hρControl
      hClosureNear

  have hTraceNear :
      dist
          (
            h3TerminalComplementGradientSelectedClosureTraceValue
              hModulus
              (y j)
          )
          (
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x (n j))
          )
        <
      ε / 2 := by

    dsimp only [Y, X] at hTraceNearRaw

    rw [
      selectedClosureTraceValue_selectedPoint
        hModulus
        (n j)
    ] at hTraceNearRaw

    exact
      hTraceNearRaw

  have hSelectedSmall :
      dist
          (
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x (n j))
          )
          0
        <
      ε / 2 :=
    hN
      j
      hj

  have hTriangle :
      dist
          (
            h3TerminalComplementGradientSelectedClosureTraceValue
              hModulus
              (y j)
          )
          0
        ≤
      dist
          (
            h3TerminalComplementGradientSelectedClosureTraceValue
              hModulus
              (y j)
          )
          (
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x (n j))
          )
        +
      dist
          (
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x (n j))
          )
          0 :=
    dist_triangle
      (
        h3TerminalComplementGradientSelectedClosureTraceValue
          hModulus
          (y j)
      )
      (
        h3TerminalComplementGradientFieldForPair
          u p
          T
          (x (n j))
      )
      0

  linarith

/-! ## C₀-type closure core package -/

/--
The escape-side terminal trace geometry on the selected closure:

* pivot native behavior at spatial infinity;
* a quantitatively nonzero positive-radius core neighborhood;
* closure-level trace decay along every spatial escape;
* quantitative finite-core versus infinity contrast.
-/
def H3TerminalNativeComplementHasPivotInfinityAndC0ClosureCore
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
  H3TerminalComplementGradientHasNonzeroSelectedClosureNeighborhood
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
of the canonical factor forces either

* a pivot-at-infinity branch whose canonical selected-closure trace is a
  nontrivial uniformly continuous `C₀`-type object; or
* bounded selected range with positive terminal spatial contrast and positive
  witness separation.
-/
theorem nativeComplement_noCanonicalFactor_forces_pivotInfinityAndC0ClosureCore_or_boundedTerminalContrast
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
    H3TerminalNativeComplementHasPivotInfinityAndC0ClosureCore
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

  have hClosureDecay :
      H3TerminalComplementGradientSelectedClosureTraceVanishesAtInfinity
        hTerminalModulus :=
    selectedClosureTraceVanishesAtInfinity_of_terminalDecay
      hTerminalModulus
      hDecay

  rcases
    nativeComplement_noCanonicalFactor_forces_pivotInfinityAndNonzeroClosureNeighborhood_or_boundedTerminalContrast
      hTau
      hEndpoint
      hSpatialEquicontinuity
      hDecay
      hResidualBounded
      hNoFactor
    with
    hEscapeSide | hContrast

  · left

    exact
      ⟨
        hEscapeSide.1,
        hEscapeSide.2.1,
        hClosureDecay,
        hEscapeSide.2.2
      ⟩

  · exact
      Or.inr
        hContrast

end

end Euclidean
end Bridge
end PrimeTensor
