import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSelectedClosureCompactCore
import Mathlib.Topology.Order.Compact

/-!
# Global peak of the selected-closure terminal trace

The canonical selected-closure terminal trace is uniformly continuous,
nontrivial, and vanishes at spatial infinity.  Every strictly positive
superlevel is compact, and at least one such superlevel is nonempty.

This forces the trace magnitude to attain a strictly positive global maximum
on the selected closure.

The maximizing point need not be unique, so no canonical spatial point is
asserted.  The global peak *magnitude*, however, is intrinsic.

The proof is elementary:

* choose a positive nonempty compact superlevel `S_δ`;
* maximize the continuous trace magnitude on `S_δ`;
* points outside `S_δ` have magnitude `< δ`;
* the maximizer inside `S_δ` has magnitude `≥ δ`.

Therefore the compact-superlevel maximizer is automatically a global
maximizer on the whole selected closure.

This turns the escape-side compact core into a genuine terminal concentration
peak while retaining the neutral alternative with the bounded spatial
contrast branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualSelectedClosurePeak
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Global peak predicate -/

/--
The canonical selected-closure terminal trace has a strictly positive global
maximum magnitude.
-/
def H3TerminalComplementGradientHasPositiveSelectedClosureGlobalPeak
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T) : Prop :=
  ∃ y : H3TerminalSelectedSpatialClosure x,
    0
      <
    dist
      (
        h3TerminalComplementGradientSelectedClosureTraceValue
          hModulus
          y
      )
      0
      ∧
    ∀ z : H3TerminalSelectedSpatialClosure x,
      dist
          (
            h3TerminalComplementGradientSelectedClosureTraceValue
              hModulus
              z
          )
          0
        ≤
      dist
        (
          h3TerminalComplementGradientSelectedClosureTraceValue
            hModulus
            y
        )
        0

/-! ## Compact core produces a global peak -/

/--
A nonempty compact positive selected-closure core contains a global maximizer
of the terminal trace magnitude.
-/
theorem positiveSelectedClosureGlobalPeak_of_nonemptyCompactCore
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hCore :
      H3TerminalComplementGradientHasNonemptyCompactSelectedClosureCore
        hModulus) :
    H3TerminalComplementGradientHasPositiveSelectedClosureGlobalPeak
      hModulus := by

  obtain
    ⟨
      δ,
      hδ,
      hNonempty,
      hCompact
    ⟩ :=
    hCore

  let f :
      H3TerminalSelectedSpatialClosure x → ℝ :=
    fun y =>
      dist
        (
          h3TerminalComplementGradientSelectedClosureTraceValue
            hModulus
            y
        )
        0

  have hContinuousTrace :
      Continuous
        (
          h3TerminalComplementGradientSelectedClosureTraceValue
            hModulus
        ) :=
    selectedClosureTraceValue_continuous
      hModulus

  have hContinuousF :
      Continuous f := by

    dsimp only [f]

    exact
      hContinuousTrace.dist
        continuous_const

  obtain
    ⟨
      yPeak,
      hyPeak,
      hPeakMax
    ⟩ :=
    hCompact.exists_isMaxOn
      hNonempty
      hContinuousF.continuousOn

  have hPeakPositive :
      0 < f yPeak := by

    have hLevel :
        δ ≤ f yPeak := by

      exact
        hyPeak

    exact
      lt_of_lt_of_le
        hδ
        hLevel

  refine
    ⟨
      yPeak,
      ?_,
      ?_
    ⟩

  · simpa only [f] using
      hPeakPositive

  · intro z

    by_cases hz :
        z ∈
          H3TerminalComplementGradientSelectedClosureSuperlevel
            hModulus
            δ

    · have hMax :
          f z ≤ f yPeak :=
        hPeakMax
          hz

      simpa only [f] using
        hMax

    · have hzLt :
          f z < δ := by

        have hzNot :
            ¬
              δ ≤ f z := by

          change
            ¬
              δ ≤ f z
            at hz

          exact
            hz

        exact
          lt_of_not_ge
            hzNot

      have hPeakLevel :
          δ ≤ f yPeak := by

        exact
          hyPeak

      have hGlobal :
          f z ≤ f yPeak :=
        le_trans
          (le_of_lt hzLt)
          hPeakLevel

      simpa only [f] using
        hGlobal

/-! ## Peak magnitude -/

/--
The intrinsic global peak magnitude of the canonical selected-closure terminal
trace.  It is defined by choosing one global maximizer; all such choices have
the same magnitude.
-/
noncomputable def h3TerminalComplementGradientSelectedClosurePeakMagnitude
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hPeak :
      H3TerminalComplementGradientHasPositiveSelectedClosureGlobalPeak
        hModulus) : ℝ :=
  dist
    (
      h3TerminalComplementGradientSelectedClosureTraceValue
        hModulus
        (Classical.choose hPeak)
    )
    0

/--
The intrinsic peak magnitude is strictly positive.
-/
theorem selectedClosurePeakMagnitude_pos
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hPeak :
      H3TerminalComplementGradientHasPositiveSelectedClosureGlobalPeak
        hModulus) :
    0
      <
    h3TerminalComplementGradientSelectedClosurePeakMagnitude
      hModulus
      hPeak := by

  unfold
    h3TerminalComplementGradientSelectedClosurePeakMagnitude

  exact
    (Classical.choose_spec hPeak).1

/--
Every closure trace magnitude is bounded above by the intrinsic peak
magnitude.
-/
theorem selectedClosureTraceValue_le_peakMagnitude
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {x : ℕ → Point3}
    {T : ℝ}
    (hModulus :
      H3TerminalComplementGradientSelectedTerminalSpatialUniformModulus
        u p x T)
    (hPeak :
      H3TerminalComplementGradientHasPositiveSelectedClosureGlobalPeak
        hModulus)
    (z : H3TerminalSelectedSpatialClosure x) :
    dist
        (
          h3TerminalComplementGradientSelectedClosureTraceValue
            hModulus
            z
        )
        0
      ≤
    h3TerminalComplementGradientSelectedClosurePeakMagnitude
      hModulus
      hPeak := by

  unfold
    h3TerminalComplementGradientSelectedClosurePeakMagnitude

  exact
    (Classical.choose_spec hPeak).2
      z

/-! ## Escape-side package with a global terminal peak -/

/--
The escape-side obstruction contains

* a native pivot cluster at spatial infinity;
* a nonempty compact positive closure core;
* a strictly positive global terminal trace peak;
* closure-level vanishing at infinity;
* quantitative finite-core versus infinity contrast.
-/
def H3TerminalNativeComplementHasPivotInfinityAndGlobalClosurePeak
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
  H3TerminalComplementGradientHasPositiveSelectedClosureGlobalPeak
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

* pivot behavior at infinity together with a compact nonzero terminal core and
  a strictly positive global closure-trace peak; or
* bounded selected range with positive terminal spatial contrast and positive
  witness separation.
-/
theorem nativeComplement_noCanonicalFactor_forces_pivotInfinityAndGlobalClosurePeak_or_boundedTerminalContrast
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
    H3TerminalNativeComplementHasPivotInfinityAndGlobalClosurePeak
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
    nativeComplement_noCanonicalFactor_forces_pivotInfinityAndCompactClosureCore_or_boundedTerminalContrast
      hTau
      hEndpoint
      hSpatialEquicontinuity
      hDecay
      hResidualBounded
      hNoFactor
    with
    hEscapeSide | hContrast

  · left

    have hPeak :
        H3TerminalComplementGradientHasPositiveSelectedClosureGlobalPeak
          hTerminalModulus :=
      positiveSelectedClosureGlobalPeak_of_nonemptyCompactCore
        hTerminalModulus
        hEscapeSide.2.1

    exact
      ⟨
        hEscapeSide.1,
        hEscapeSide.2.1,
        hPeak,
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
