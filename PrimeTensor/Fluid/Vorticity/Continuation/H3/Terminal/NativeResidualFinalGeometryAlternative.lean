import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualTerminalSpatialContrastSeparation

/-!
# Final geometric obstruction alternative for the native terminal residual

The terminal residual analysis has isolated two independent endpoint control
frontiers:

* selected spatial equicontinuity over the preterminal family;
* a uniform selected endpoint temporal modulus at the terminal time.

Under those hypotheses, failure of the canonical native residual factor has a
clean geometric classification.

Either

1. one cofinal selected spacetime refinement approaches the terminal time while
   escaping to spatial infinity; or
2. the full selected spatial range is bounded and the actual terminal
   complementary-gradient field has a positive contrast across two selected
   points separated by a fixed positive spatial distance.

The two noncanonical geometric branches are mutually exclusive because the
first forces the selected range to be unbounded while the second carries
boundedness explicitly.

This file also packages the corresponding neutral exhaustive alternative:

    canonical native factor
      OR terminal spatial escape
      OR bounded positive terminal spatial contrast.

No claim is made that either geometric obstruction is impossible under the
present H³ hypotheses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualFinalGeometryAlternative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Escape implies unbounded selected range -/

/--
A terminal spatial escape refinement is, in particular, a spatial
escape-to-infinity refinement of the selected point sequence.
-/
theorem selectedPointEscapesToInfinity_of_spatialEscapeAtTerminal
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hEscape :
      H3TerminalSelectedPointSpatialEscapeAtTerminal
        τ x T) :
    H3TerminalSelectedPointEscapesToInfinity
      x := by

  obtain
    ⟨
      k,
      hkTop,
      _hTime,
      hSpatial
    ⟩ :=
    hEscape

  exact
    ⟨
      k,
      hkTop,
      hSpatial
    ⟩

/--
A bounded selected spatial range excludes terminal spatial escape.
-/
theorem not_selectedPointSpatialEscapeAtTerminal_of_bounded
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hBounded :
      Bornology.IsBounded (Set.range x)) :
    ¬
      H3TerminalSelectedPointSpatialEscapeAtTerminal
        τ x T := by

  intro hEscape

  have hUnbounded :
      ¬ Bornology.IsBounded (Set.range x) :=
    unbounded_of_selectedPointEscapesToInfinity
      (
        selectedPointEscapesToInfinity_of_spatialEscapeAtTerminal
          hEscape
      )

  exact
    hUnbounded
      hBounded

/-! ## Exact noncanonical geometric split -/

/--
Under the endpoint temporal modulus and selected spatial equicontinuity,
failure of the canonical native residual factor forces exactly the useful
bounded/unbounded geometric split:

* terminal spatial escape; or
* bounded selected range with positive terminal contrast and positive witness
  separation.
-/
theorem nativeComplement_noCanonicalFactor_forces_terminalEscape_or_boundedTerminalContrast
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
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x) :
    H3TerminalSelectedPointSpatialEscapeAtTerminal
        τ x T
      ∨
    (
      Bornology.IsBounded (Set.range x)
        ∧
      H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrastSeparation
        u p x T
    ) := by

  classical

  by_cases hBounded :
      Bornology.IsBounded (Set.range x)

  · exact
      Or.inr
        ⟨
          hBounded,
          positiveSelectedTerminalSpatialContrastSeparation_of_noCanonicalFactor_of_endpointModulus_of_spatialEquicontinuity_of_bounded
            hTau
            hEndpoint
            hSpatialEquicontinuity
            hBounded
            hNoFactor
        ⟩

  · exact
      Or.inl
        (
          selectedPointSpatialEscapeAtTerminal_of_tendsto_of_escape
            hTau
            (
              selectedPointEscapesToInfinity_of_unbounded
                hBounded
            )
        )

/--
The two geometric branches in the preceding noncanonical alternative are
mutually exclusive.
-/
theorem not_terminalEscape_and_boundedTerminalContrast
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ} :
    ¬
      (
        H3TerminalSelectedPointSpatialEscapeAtTerminal
            τ x T
          ∧
        (
          Bornology.IsBounded (Set.range x)
            ∧
          H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrastSeparation
            u p x T
        )
      ) := by

  rintro
    ⟨
      hEscape,
      hBounded,
      _hContrast
    ⟩

  exact
    (
      not_selectedPointSpatialEscapeAtTerminal_of_bounded
        hBounded
    )
      hEscape

/-! ## Neutral exhaustive terminal geometry alternative -/

/--
Under terminal-time convergence and the two endpoint control frontiers, the
native complementary residual satisfies the neutral exhaustive alternative:

1. the full canonical native factor exists; or
2. a cofinal selected spacetime refinement escapes spatially to infinity while
   approaching `T`; or
3. the selected spatial range is bounded and the actual terminal
   complementary-gradient field has a positive contrast across positively
   separated selected points.

The theorem does not rank these branches or assert that either obstruction
branch is impossible.
-/
theorem nativeComplement_canonicalFactor_or_terminalEscape_or_boundedTerminalContrast
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
        u p τ x) :
    H3TerminalNativeComplementHasCanonicalFactor
        u p τ x
      ∨
    H3TerminalSelectedPointSpatialEscapeAtTerminal
        τ x T
      ∨
    (
      Bornology.IsBounded (Set.range x)
        ∧
      H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrastSeparation
        u p x T
    ) := by

  classical

  by_cases hFactor :
      H3TerminalNativeComplementHasCanonicalFactor
        u p τ x

  · exact
      Or.inl
        hFactor

  · rcases
      nativeComplement_noCanonicalFactor_forces_terminalEscape_or_boundedTerminalContrast
        hTau
        hEndpoint
        hSpatialEquicontinuity
        hFactor
      with
      hEscape | hContrast

    · exact
        Or.inr
          (
            Or.inl
              hEscape
          )

    · exact
        Or.inr
          (
            Or.inr
              hContrast
          )

end

end Euclidean
end Bridge
end PrimeTensor
