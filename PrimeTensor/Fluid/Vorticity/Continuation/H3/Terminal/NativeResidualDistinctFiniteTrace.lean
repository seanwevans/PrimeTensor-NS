import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualDistinctChannelSpatialLocalization

/-!
# Terminal trace of the distinct finite residual channel

The distinct finite native residual channel has now been localized at a finite
spatial cluster point.

The endpoint temporal modulus supplies one further identification without any
continuity assumption at the cluster point itself.

Along the cofinal channel,

    logValue(residual_j)
      =
    complementaryGradient(τ_j, x_j)

converges to `logValue q`.

Uniform endpoint temporal control says that

    complementaryGradient(τ_j, x_j)
      -
    complementaryGradient(T, x_j)

vanishes uniformly even though the selected spatial point `x_j` is moving.

Therefore the *actual terminal field evaluated at the moving selected points*
also converges to `logValue q`.

For `q ≠ 1`, injectivity of `logValue` and `logValue 1 = 0` imply

    logValue q ≠ 0.

Hence the distinct finite native channel becomes a genuinely nonzero terminal
trace concentrated near a finite spatial cluster point.

Combined with the pivot-at-infinity channel, this gives the neutral picture:

* zero/pivot behavior along a channel escaping to infinity;
* nonzero finite terminal trace near a finite spatial cluster;

or the already identified bounded terminal-contrast branch.

No continuity of the terminal field at the cluster point `y` is assumed here,
so the theorem does not identify the trace limit with the literal value
`F(T,y)`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Uniform endpoint transfer for a moving selected point -/

/--
If the moving preterminal complementary-gradient values converge to `L`, then
the actual terminal values at the same moving selected spatial points converge
to the same `L`, provided the selected endpoint temporal modulus holds.
-/
theorem movingSelected_terminalValue_tendsto_of_endpointTemporalModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T L : ℝ}
    {k : ℕ → ℕ}
    (hEndpoint :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u p τ x T)
    (hTime :
      Tendsto
        (fun j : ℕ => τ (k j))
        atTop
        (𝓝 T))
    (hPreterminal :
      Tendsto
        (
          fun j : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u p
              (τ (k j))
              (x (k j))
        )
        atTop
        (𝓝 L)) :
    Tendsto
      (
        fun j : ℕ =>
          h3TerminalComplementGradientFieldForPair
            u p
            T
            (x (k j))
      )
      atTop
      (𝓝 L) := by

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
  rw [Metric.tendsto_atTop] at hPreterminal

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
    hPreterminal
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
      T
      (x (k j))

  let B : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      (τ (k j))
      (x (k j))

  have hBA :
      dist B A < ε / 2 := by

    dsimp only [B, A]

    exact
      hEndpointUniform
        (k j)
        (k j)
        (hN₁ j hN₁j)

  have hAB :
      dist A B < ε / 2 := by

    simpa only [dist_comm] using
      hBA

  have hBL :
      dist B L < ε / 2 := by

    dsimp only [B]

    exact
      hN₂
        j
        hN₂j

  have hTriangle :
      dist A L
        ≤
      dist A B + dist B L :=
    dist_triangle
      A B L

  have hAL :
      dist A L < ε := by
    linarith

  simpa only [A] using
    hAL

/-! ## Distinct finite terminal trace channel -/

/--
A distinct finite native factor `q ≠ 1` is realized on a cofinal channel whose
selected points converge to a finite spatial cluster point and whose actual
terminal complementary-gradient values converge to the nonzero real trace
`logValue q`.
-/
def H3TerminalNativeComplementHasDistinctFiniteTerminalTraceChannel
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  ∃ q : MulReal,
    q ≠ (1 : MulReal)
      ∧
    PrimeTensor.Bridge.MulReal.logValue q ≠ 0
      ∧
    ∃ y : Point3,
      ∃ k : ℕ → ℕ,
        Tendsto k atTop atTop
          ∧
        Tendsto
          (fun j : ℕ => τ (k j))
          atTop
          (𝓝 T)
          ∧
        Tendsto
          (fun j : ℕ => x (k j))
          atTop
          (𝓝 y)
          ∧
        H3TerminalNativeComplementProportionalityFactor
          u p
          (fun j : ℕ => τ (k j))
          (fun j : ℕ => x (k j))
          q
          ∧
        Tendsto
          (
            fun j : ℕ =>
              h3TerminalComplementGradientFieldForPair
                u p
                T
                (x (k j))
          )
          atTop
          (
            𝓝
              (
                PrimeTensor.Bridge.MulReal.logValue q
              )
          )

/--
Endpoint temporal control upgrades a distinct finite spatial cluster channel
to a nonzero terminal trace channel.
-/
theorem distinctFiniteTerminalTraceChannel_of_distinctFiniteSpatialClusterChannel_of_endpointModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hEndpoint :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u p τ x T)
    (hChannel :
      H3TerminalNativeComplementHasDistinctFiniteSpatialClusterChannel
        u p τ x T) :
    H3TerminalNativeComplementHasDistinctFiniteTerminalTraceChannel
      u p τ x T := by

  obtain
    ⟨
      q,
      hqNe,
      y,
      k,
      hkTop,
      hTime,
      hPoint,
      hFactor
    ⟩ :=
    hChannel

  have hqLogNe :
      PrimeTensor.Bridge.MulReal.logValue q ≠ 0 := by

    intro hqZero

    apply hqNe

    apply
      PrimeTensor.Bridge.MulReal.logValue_injective

    simpa only [
      PrimeTensor.Bridge.MulReal.logValue_one
    ] using
      hqZero

  have hNative :
      H3TerminalNativeNatConvergesTo
        (
          fun j : ℕ =>
            PrimeTensor.MulReal.ratio
              (
                h3TerminalNativeGradientForPair
                  u p
                  (τ (k j))
                  (x (k j))
              )
              (
                h3TerminalSelectedSignedNativeCurlForPair
                  u p
                  (τ (k j))
                  (x (k j))
              )
        )
        q := by

    exact
      hFactor

  have hLog :
      Tendsto
        (
          fun j : ℕ =>
            PrimeTensor.Bridge.MulReal.logValue
              (
                PrimeTensor.MulReal.ratio
                  (
                    h3TerminalNativeGradientForPair
                      u p
                      (τ (k j))
                      (x (k j))
                  )
                  (
                    h3TerminalSelectedSignedNativeCurlForPair
                      u p
                      (τ (k j))
                      (x (k j))
                  )
              )
        )
        atTop
        (
          𝓝
            (
              PrimeTensor.Bridge.MulReal.logValue q
            )
        ) :=
    (
      terminalNativeNatConvergesTo_iff_logValue_tendsto
        (
          fun j : ℕ =>
            PrimeTensor.MulReal.ratio
              (
                h3TerminalNativeGradientForPair
                  u p
                  (τ (k j))
                  (x (k j))
              )
              (
                h3TerminalSelectedSignedNativeCurlForPair
                  u p
                  (τ (k j))
                  (x (k j))
              )
        )
        q
    ).1
      hNative

  have hPreterminal :
      Tendsto
        (
          fun j : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u p
              (τ (k j))
              (x (k j))
        )
        atTop
        (
          𝓝
            (
              PrimeTensor.Bridge.MulReal.logValue q
            )
        ) := by

    simpa only [
      ← h3TerminalNativeComplementGradientForPair_eq_residualRatio,
      logValue_h3TerminalNativeComplementGradientForPair
    ] using
      hLog

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
        (
          𝓝
            (
              PrimeTensor.Bridge.MulReal.logValue q
            )
        ) :=
    movingSelected_terminalValue_tendsto_of_endpointTemporalModulus
      hEndpoint
      hTime
      hPreterminal

  exact
    ⟨
      q,
      hqNe,
      hqLogNe,
      y,
      k,
      hkTop,
      hTime,
      hPoint,
      hFactor,
      hTerminal
    ⟩

/-! ## Pivot at infinity versus nonzero finite terminal trace -/

/--
The escape-side residual geometry consists of a native pivot cluster at spatial
infinity together with a distinct nonzero terminal trace concentrated near a
finite spatial cluster point.
-/
def H3TerminalNativeComplementHasPivotInfinityAndDistinctFiniteTerminalTrace
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

/--
Under endpoint temporal control, selected spatial equicontinuity, terminal
decay at infinity, and eventual boundedness of the residual logarithm, failure
of the canonical factor forces either

* a pivot native channel at spatial infinity together with a distinct nonzero
  terminal trace near a finite spatial cluster point; or
* bounded selected range with positive terminal spatial contrast and positive
  witness separation.
-/
theorem nativeComplement_noCanonicalFactor_forces_pivotInfinityAndDistinctFiniteTerminalTrace_or_boundedTerminalContrast
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
    H3TerminalNativeComplementHasPivotInfinityAndDistinctFiniteTerminalTrace
        u p τ x T
      ∨
    (
      Bornology.IsBounded (Set.range x)
        ∧
      H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrastSeparation
        u p x T
    ) := by

  rcases
    nativeComplement_noCanonicalFactor_forces_pivotInfinityAndDistinctFiniteSpatialChannel_or_boundedTerminalContrast
      hTau
      hEndpoint
      hSpatialEquicontinuity
      hDecay
      hResidualBounded
      hNoFactor
    with
    hEscapeSide | hContrast

  · left

    refine
      ⟨
        hEscapeSide.1,
        ?_
      ⟩

    exact
      distinctFiniteTerminalTraceChannel_of_distinctFiniteSpatialClusterChannel_of_endpointModulus
        hEndpoint
        hEscapeSide.2

  · exact
      Or.inr
        hContrast

end

end Euclidean
end Bridge
end PrimeTensor
