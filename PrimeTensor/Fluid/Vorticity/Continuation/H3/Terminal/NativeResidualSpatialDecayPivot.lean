import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualFinalGeometryAlternative

/-!
# Spatial decay frontier and the native pivot cluster at infinity

The final geometric obstruction alternative contains a branch in which one
cofinal selected spacetime refinement approaches the terminal time while its
spatial points escape to infinity.

For an H³ field on `ℝ³`, the analytically natural next question is whether the
relevant first derivative vanishes at spatial infinity.  That Fourier /
Riemann--Lebesgue statement is not assumed to have been proved by the current
formal development, so this file isolates it explicitly as a frontier.

The selected terminal decay property says that the actual terminal
complementary-gradient field tends to zero along every selected spatial escape.

Combined with the uniform endpoint temporal modulus, this transfers zero
decay from the terminal field back to the moving preterminal values on the
escaping refinement.

The exact logarithmic bridge then gives the intrinsic multiplicative
conclusion:

    the native complementary residual converges to `1`

on that escaping cofinal refinement, because `logValue 1 = 0`.

Thus the escape branch acquires a canonical finite *cluster factor* at the
multiplicative pivot, without asserting convergence of the full residual
sequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualSpatialDecayPivot
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Terminal decay along selected spatial escape -/

/--
The actual terminal complementary-gradient field vanishes along every cofinal
selected spatial escape.
-/
def H3TerminalComplementGradientSelectedTerminalDecayAtInfinity
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  ∀ k : ℕ → ℕ,
    Tendsto
        (
          fun j : ℕ =>
            dist
              (0 : Point3)
              (x (k j))
        )
        atTop
        atTop
      →
    Tendsto
      (
        fun j : ℕ =>
          h3TerminalComplementGradientFieldForPair
            u p
            T
            (x (k j))
      )
      atTop
      (𝓝 0)

/-! ## Transfer terminal decay to moving preterminal values -/

/--
Uniform endpoint temporal control transfers terminal spatial decay to the
moving complementary-gradient values on any selected terminal escape.
-/
theorem complementGradient_tendsto_zero_of_terminalEscapeRefinement_of_endpointModulus_of_terminalDecay
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    {k : ℕ → ℕ}
    (hTime :
      Tendsto
        (fun j : ℕ => τ (k j))
        atTop
        (𝓝 T))
    (hSpatial :
      Tendsto
        (
          fun j : ℕ =>
            dist
              (0 : Point3)
              (x (k j))
        )
        atTop
        atTop)
    (hEndpoint :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u p τ x T)
    (hDecay :
      H3TerminalComplementGradientSelectedTerminalDecayAtInfinity
        u p x T) :
    Tendsto
      (
        fun j : ℕ =>
          h3TerminalComplementGradientFieldForPair
            u p
            (τ (k j))
            (x (k j))
      )
      atTop
      (𝓝 0) := by

  have hTerminal :
      Tendsto
        (
          fun j : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x (k j))
        )
        atTop
        (𝓝 0) :=
    hDecay
      k
      hSpatial

  rw [Metric.tendsto_atTop]

  intro ε hε

  have hHalfPos :
      0 < ε / 2 := by
    linarith

  obtain
    ⟨
      η,
      hη,
      hEndpointUniform
    ⟩ :=
    hEndpoint
      (ε / 2)
      hHalfPos

  rw [Metric.tendsto_atTop] at hTime
  rw [Metric.tendsto_atTop] at hTerminal

  obtain
    ⟨
      N₁,
      hN₁
    ⟩ :=
    hTime
      η
      hη

  obtain
    ⟨
      N₂,
      hN₂
    ⟩ :=
    hTerminal
      (ε / 2)
      hHalfPos

  refine
    ⟨
      max N₁ N₂,
      ?_
    ⟩

  intro j hj

  have hN₁j :
      N₁ ≤ j :=
    le_trans
      (le_max_left N₁ N₂)
      hj

  have hN₂j :
      N₂ ≤ j :=
    le_trans
      (le_max_right N₁ N₂)
      hj

  let A : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      (τ (k j))
      (x (k j))

  let B : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      T
      (x (k j))

  have hAB :
      dist A B < ε / 2 := by

    dsimp only [A, B]

    exact
      hEndpointUniform
        (k j)
        (k j)
        (hN₁ j hN₁j)

  have hB0 :
      dist B 0 < ε / 2 := by

    dsimp only [B]

    exact
      hN₂
        j
        hN₂j

  have hTriangle :
      dist A 0
        ≤
      dist A B + dist B 0 :=
    dist_triangle
      A B 0

  have hA0 :
      dist A 0 < ε := by
    linarith

  simpa only [A] using
    hA0

/-! ## Native pivot convergence on the escape refinement -/

/--
If the complementary-gradient values tend to zero on the escaping refinement,
then the native complementary gradient converges intrinsically to the
multiplicative pivot `1`.
-/
theorem nativeComplementGradient_terminalNativeNatConvergesTo_one_of_terminalEscapeRefinement_of_endpointModulus_of_terminalDecay
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    {k : ℕ → ℕ}
    (hTime :
      Tendsto
        (fun j : ℕ => τ (k j))
        atTop
        (𝓝 T))
    (hSpatial :
      Tendsto
        (
          fun j : ℕ =>
            dist
              (0 : Point3)
              (x (k j))
        )
        atTop
        atTop)
    (hEndpoint :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u p τ x T)
    (hDecay :
      H3TerminalComplementGradientSelectedTerminalDecayAtInfinity
        u p x T) :
    H3TerminalNativeNatConvergesTo
      (
        fun j : ℕ =>
          h3TerminalNativeComplementGradientForPair
            u p
            (τ (k j))
            (x (k j))
      )
      (1 : MulReal) := by

  have hZero :
      Tendsto
        (
          fun j : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u p
              (τ (k j))
              (x (k j))
        )
        atTop
        (𝓝 0) :=
    complementGradient_tendsto_zero_of_terminalEscapeRefinement_of_endpointModulus_of_terminalDecay
      hTime
      hSpatial
      hEndpoint
      hDecay

  apply
    (
      terminalNativeNatConvergesTo_iff_logValue_tendsto
        (
          fun j : ℕ =>
            h3TerminalNativeComplementGradientForPair
              u p
              (τ (k j))
              (x (k j))
        )
        (1 : MulReal)
    ).2

  simpa only [
    logValue_h3TerminalNativeComplementGradientForPair,
    PrimeTensor.Bridge.MulReal.logValue_one
  ] using
    hZero

/-! ## Packaged cofinal pivot cluster at spatial infinity -/

/--
The native complementary residual has a cofinal pivot cluster at spatial
infinity: along one cofinal refinement the times approach `T`, the points
escape to infinity, and the native complementary residual converges to `1`.
-/
def H3TerminalNativeComplementHasCofinalPivotClusterAtSpatialInfinity
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
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
      ∧
    H3TerminalNativeNatConvergesTo
      (
        fun j : ℕ =>
          h3TerminalNativeComplementGradientForPair
            u p
            (τ (k j))
            (x (k j))
      )
      (1 : MulReal)

/--
A geometric terminal spatial escape becomes a native pivot cluster at spatial
infinity under endpoint temporal control and terminal spatial decay.
-/
theorem nativeComplementHasCofinalPivotClusterAtSpatialInfinity_of_terminalEscape_of_endpointModulus_of_terminalDecay
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hEscape :
      H3TerminalSelectedPointSpatialEscapeAtTerminal
        τ x T)
    (hEndpoint :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u p τ x T)
    (hDecay :
      H3TerminalComplementGradientSelectedTerminalDecayAtInfinity
        u p x T) :
    H3TerminalNativeComplementHasCofinalPivotClusterAtSpatialInfinity
      u p τ x T := by

  obtain
    ⟨
      k,
      hkTop,
      hTime,
      hSpatial
    ⟩ :=
    hEscape

  exact
    ⟨
      k,
      hkTop,
      hTime,
      hSpatial,
      nativeComplementGradient_terminalNativeNatConvergesTo_one_of_terminalEscapeRefinement_of_endpointModulus_of_terminalDecay
        hTime
        hSpatial
        hEndpoint
        hDecay
    ⟩

/-! ## Refined noncanonical geometry with decay at infinity -/

/--
Under endpoint temporal control, selected spatial equicontinuity, and selected
terminal decay at infinity, failure of the canonical native residual factor
forces either

* a cofinal native pivot cluster at spatial infinity; or
* a bounded selected range with positive actual terminal spatial contrast and
  positive witness separation.

The first conclusion is only a cluster statement; it does not assert that the
full residual sequence converges to `1`.
-/
theorem nativeComplement_noCanonicalFactor_forces_pivotClusterAtInfinity_or_boundedTerminalContrast
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
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x) :
    H3TerminalNativeComplementHasCofinalPivotClusterAtSpatialInfinity
        u p τ x T
      ∨
    (
      Bornology.IsBounded (Set.range x)
        ∧
      H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrastSeparation
        u p x T
    ) := by

  rcases
    nativeComplement_noCanonicalFactor_forces_terminalEscape_or_boundedTerminalContrast
      hTau
      hEndpoint
      hSpatialEquicontinuity
      hNoFactor
    with
    hEscape | hContrast

  · exact
      Or.inl
        (
          nativeComplementHasCofinalPivotClusterAtSpatialInfinity_of_terminalEscape_of_endpointModulus_of_terminalDecay
            hEscape
            hEndpoint
            hDecay
        )

  · exact
      Or.inr
        hContrast

/-!
Neutral exhaustive form with the same decay hypothesis.
-/
theorem nativeComplement_canonicalFactor_or_pivotClusterAtInfinity_or_boundedTerminalContrast
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
        u p x T) :
    H3TerminalNativeComplementHasCanonicalFactor
        u p τ x
      ∨
    H3TerminalNativeComplementHasCofinalPivotClusterAtSpatialInfinity
        u p τ x T
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
      nativeComplement_noCanonicalFactor_forces_pivotClusterAtInfinity_or_boundedTerminalContrast
        hTau
        hEndpoint
        hSpatialEquicontinuity
        hDecay
        hFactor
      with
      hPivot | hContrast

    · exact
        Or.inr
          (
            Or.inl
              hPivot
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
