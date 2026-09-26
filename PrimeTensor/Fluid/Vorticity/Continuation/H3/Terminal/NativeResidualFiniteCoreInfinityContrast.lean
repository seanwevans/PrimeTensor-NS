import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualDistinctFiniteTrace

/-!
# Quantitative contrast between a finite terminal core and spatial infinity

The distinct finite terminal trace channel converges to a nonzero real value

    L = logValue q ≠ 0

while the terminal decay frontier sends every selected spatial escape to zero.

Therefore the terminal complementary-gradient field exhibits a quantitative
core-versus-infinity separation.

More precisely, one cofinal selected channel converges to a finite spatial
cluster point `y`, and there is one fixed `δ > 0` such that, against *every*
selected channel escaping to spatial infinity, the synchronized terminal field
values are eventually separated by at least `δ`.

The same `δ` works for all escape channels because it is chosen from the
nonzero core limit alone.

This is stronger than merely selecting one nonzero terminal point: it records
a persistent asymptotic contrast between a finite spatial core and every
selected route to infinity.

No contradiction is asserted.  Such localized nonzero terminal structure is a
possible obstruction branch under the stated frontier hypotheses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualFiniteCoreInfinityContrast
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Finite core versus infinity -/

/--
There is a cofinal selected channel converging to a finite spatial point and a
fixed positive terminal complementary-gradient gap between that core channel
and every selected channel escaping to spatial infinity.
-/
def H3TerminalComplementGradientHasFiniteCoreInfinityContrast
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ y : Point3,
      ∃ k : ℕ → ℕ,
        Tendsto k atTop atTop
          ∧
        Tendsto
          (fun j : ℕ => x (k j))
          atTop
          (𝓝 y)
          ∧
        ∀ ell : ℕ → ℕ,
          Tendsto
              (
                fun j : ℕ =>
                  dist
                    (0 : Point3)
                    (x (ell j))
              )
              atTop
              atTop
            →
          ∀ᶠ j : ℕ in atTop,
            δ
              ≤
            dist
              (
                h3TerminalComplementGradientFieldForPair
                  u p
                  T
                  (x (k j))
              )
              (
                h3TerminalComplementGradientFieldForPair
                  u p
                  T
                  (x (ell j))
              )

/--
A nonzero finite terminal trace together with terminal decay at infinity yields
a quantitative finite-core-versus-infinity contrast.

If the finite trace tends to `L ≠ 0`, choose

    δ = dist L 0 / 2.

Every escaping terminal trace tends to zero, so its distance from the finite
core trace tends to `dist L 0`; hence it is eventually at least `δ`.
-/
theorem finiteCoreInfinityContrast_of_distinctFiniteTerminalTrace_of_terminalDecay
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTrace :
      H3TerminalNativeComplementHasDistinctFiniteTerminalTraceChannel
        u p τ x T)
    (hDecay :
      H3TerminalComplementGradientSelectedTerminalDecayAtInfinity
        u p x T) :
    H3TerminalComplementGradientHasFiniteCoreInfinityContrast
      u p x T := by

  obtain
    ⟨
      q,
      _hqNe,
      hqLogNe,
      y,
      k,
      hkTop,
      _hTime,
      hPoint,
      _hFactor,
      hTerminal
    ⟩ :=
    hTrace

  let L : ℝ :=
    PrimeTensor.Bridge.MulReal.logValue q

  let d : ℝ :=
    dist L 0

  have hLNe :
      L ≠ 0 := by

    simpa only [L] using
      hqLogNe

  have hdPos :
      0 < d := by

    dsimp only [d]

    exact
      dist_pos.mpr
        hLNe

  have hHalfPos :
      0 < d / 2 :=
    half_pos hdPos

  refine
    ⟨
      d / 2,
      hHalfPos,
      y,
      k,
      hkTop,
      hPoint,
      ?_
    ⟩

  intro ell hEllEscape

  have hInfinity :
      Tendsto
        (
          fun j : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x (ell j))
        )
        atTop
        (𝓝 0) :=
    hDecay
      ell
      hEllEscape

  have hDistance :
      Tendsto
        (
          fun j : ℕ =>
            dist
              (
                h3TerminalComplementGradientFieldForPair
                  u p
                  T
                  (x (k j))
              )
              (
                h3TerminalComplementGradientFieldForPair
                  u p
                  T
                  (x (ell j))
              )
        )
        atTop
        (𝓝 d) := by

    dsimp only [d, L]

    exact
      hTerminal.dist
        hInfinity

  rw [Metric.tendsto_atTop] at hDistance

  obtain
    ⟨
      N,
      hN
    ⟩ :=
    hDistance
      (d / 2)
      hHalfPos

  filter_upwards
    [eventually_ge_atTop N]
    with j hj

  have hNear :
      dist
          (
            dist
              (
                h3TerminalComplementGradientFieldForPair
                  u p
                  T
                  (x (k j))
              )
              (
                h3TerminalComplementGradientFieldForPair
                  u p
                  T
                  (x (ell j))
              )
          )
          d
        <
      d / 2 :=
    hN
      j
      hj

  rw [Real.dist_eq] at hNear

  have hLower :=
    (abs_lt.mp hNear).1

  linarith

/-! ## Escape-side package with quantitative terminal contrast -/

/--
The escape-side residual branch contains

* a native pivot cluster at spatial infinity;
* a distinct finite nonzero terminal trace channel; and
* a quantitative terminal contrast between that finite core and every selected
  route to spatial infinity.
-/
def H3TerminalNativeComplementHasPivotInfinityAndFiniteCoreContrast
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  H3TerminalNativeComplementHasCofinalPivotClusterAtSpatialInfinity
      u p τ x T
    ∧
  H3TerminalNativeComplementHasDistinctFiniteTerminalTraceChannel
      u p τ x T
    ∧
  H3TerminalComplementGradientHasFiniteCoreInfinityContrast
      u p x T

/--
Under endpoint temporal control, selected spatial equicontinuity, terminal
decay at infinity, and eventual boundedness of the residual logarithm, failure
of the canonical native factor forces either

* a pivot cluster at infinity together with a distinct nonzero finite terminal
  trace and a quantitative finite-core-versus-infinity contrast; or
* bounded selected range with positive terminal spatial contrast and positive
  witness separation.
-/
theorem nativeComplement_noCanonicalFactor_forces_pivotInfinityAndFiniteCoreContrast_or_boundedTerminalContrast
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
    H3TerminalNativeComplementHasPivotInfinityAndFiniteCoreContrast
        u p τ x T
      ∨
    (
      Bornology.IsBounded (Set.range x)
        ∧
      H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrastSeparation
        u p x T
    ) := by

  rcases
    nativeComplement_noCanonicalFactor_forces_pivotInfinityAndDistinctFiniteTerminalTrace_or_boundedTerminalContrast
      hTau
      hEndpoint
      hSpatialEquicontinuity
      hDecay
      hResidualBounded
      hNoFactor
    with
    hEscapeSide | hContrast

  · left

    have hCoreContrast :
        H3TerminalComplementGradientHasFiniteCoreInfinityContrast
          u p x T :=
      finiteCoreInfinityContrast_of_distinctFiniteTerminalTrace_of_terminalDecay
        hEscapeSide.2
        hDecay

    exact
      ⟨
        hEscapeSide.1,
        hEscapeSide.2,
        hCoreContrast
      ⟩

  · exact
      Or.inr
        hContrast

end

end Euclidean
end Bridge
end PrimeTensor
