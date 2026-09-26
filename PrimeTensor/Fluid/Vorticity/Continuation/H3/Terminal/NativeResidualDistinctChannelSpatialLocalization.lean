import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualPivotSeparatedChannel
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Spatial localization of the distinct finite residual channel

Under terminal decay at spatial infinity, a cofinal native residual channel
with finite factor `q ≠ 1` cannot itself escape spatially.

Indeed, if its selected spatial range were unbounded, a further cofinal
subsequence would escape to infinity.  The endpoint temporal modulus and
terminal decay would force the native complementary gradient on that
subsequence to converge to the multiplicative pivot `1`.  But cofinal
refinement preserves the original native limit `q`.  Uniqueness of intrinsic
native limits would then force `q = 1`, a contradiction.

Therefore every distinct finite channel `q ≠ 1` produced in the eventually
bounded residual regime is spatially bounded.  Since `Point3` is a finite
product of proper real metric spaces, a further cofinal refinement converges
to a finite spatial point while preserving the same native factor.

Combining this with the pivot-at-infinity branch gives a concrete neutral
classification:

* pivot factor `1` on a cofinal channel escaping to spatial infinity, together
  with a distinct finite factor `q ≠ 1` on a cofinal channel converging to a
  finite spatial point; or
* bounded selected range with positive terminal spatial contrast and positive
  witness separation.

No impossibility claim is made for either branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualDistinctChannelSpatialLocalization
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Distinct finite channels are spatially bounded under decay -/

/--
Under terminal decay at infinity and endpoint temporal control, any cofinal
native complementary residual channel with finite factor `q ≠ 1` has bounded
selected spatial range.
-/
theorem distinctCofinalFactorFromPivot_spatialRange_bounded_of_endpointModulus_of_terminalDecay
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
    (hDecay :
      H3TerminalComplementGradientSelectedTerminalDecayAtInfinity
        u p x T)
    (hDistinct :
      H3TerminalNativeComplementHasDistinctCofinalFactorFromPivot
        u p τ x) :
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
          ∧
        Bornology.IsBounded
          (
            Set.range
              (fun j : ℕ => x (k j))
          ) := by

  obtain
    ⟨
      q,
      hqNe,
      k,
      hkTop,
      hFactor
    ⟩ :=
    hDistinct

  have hSpatialBounded :
      Bornology.IsBounded
        (
          Set.range
            (fun j : ℕ => x (k j))
        ) := by

    by_contra hUnbounded

    have hEscape :
        H3TerminalSelectedPointEscapesToInfinity
          (fun j : ℕ => x (k j)) :=
      selectedPointEscapesToInfinity_of_unbounded
        hUnbounded

    obtain
      ⟨
        ell,
        hEllTop,
        hSpatial
      ⟩ :=
      hEscape

    let K : ℕ → ℕ :=
      fun j : ℕ =>
        k (ell j)

    have hKTop :
        Tendsto K atTop atTop := by

      dsimp only [K]

      exact
        hkTop.comp
          hEllTop

    have hTime :
        Tendsto
          (fun j : ℕ => τ (K j))
          atTop
          (𝓝 T) :=
      hTau.comp
        hKTop

    have hSpatialK :
        Tendsto
          (
            fun j : ℕ =>
              dist
                (0 : Point3)
                (x (K j))
          )
          atTop
          atTop := by

      simpa only [K] using
        hSpatial

    have hNativeOne :
        H3TerminalNativeNatConvergesTo
          (
            fun j : ℕ =>
              h3TerminalNativeComplementGradientForPair
                u p
                (τ (K j))
                (x (K j))
          )
          (1 : MulReal) :=
      nativeComplementGradient_terminalNativeNatConvergesTo_one_of_terminalEscapeRefinement_of_endpointModulus_of_terminalDecay
        hTime
        hSpatialK
        hEndpoint
        hDecay

    have hFactorNative :
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

    have hFactorLog :
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
        hFactorNative

    have hNativeQ :
        H3TerminalNativeNatConvergesTo
          (
            fun j : ℕ =>
              h3TerminalNativeComplementGradientForPair
                u p
                (τ (K j))
                (x (K j))
          )
          q := by

      apply
        (
          terminalNativeNatConvergesTo_iff_logValue_tendsto
            (
              fun j : ℕ =>
                h3TerminalNativeComplementGradientForPair
                  u p
                  (τ (K j))
                  (x (K j))
            )
            q
        ).2

      have hSub :=
        hFactorLog.comp
          hEllTop

      simpa [
        Function.comp_def,
        K,
        h3TerminalNativeComplementGradientForPair_eq_residualRatio
      ] using
        hSub

    have hqOne :
        q = (1 : MulReal) :=
      terminalNativeNatConvergesTo_unique
        hNativeQ
        hNativeOne

    exact
      hqNe
        hqOne

  exact
    ⟨
      q,
      hqNe,
      k,
      hkTop,
      hFactor,
      hSpatialBounded
    ⟩

/-! ## A finite spatial cluster point for the distinct channel -/

/--
A distinct native residual factor `q ≠ 1` is realized by a cofinal terminal
channel converging to a finite spatial point.
-/
def H3TerminalNativeComplementHasDistinctFiniteSpatialClusterChannel
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  ∃ q : MulReal,
    q ≠ (1 : MulReal)
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

/--
Under endpoint temporal control and terminal spatial decay, every distinct
cofinal finite native factor has a further cofinal channel converging to a
finite spatial cluster point.
-/
theorem distinctFiniteSpatialClusterChannel_of_distinctCofinalFactorFromPivot_of_endpointModulus_of_terminalDecay
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
    (hDecay :
      H3TerminalComplementGradientSelectedTerminalDecayAtInfinity
        u p x T)
    (hDistinct :
      H3TerminalNativeComplementHasDistinctCofinalFactorFromPivot
        u p τ x) :
    H3TerminalNativeComplementHasDistinctFiniteSpatialClusterChannel
      u p τ x T := by

  obtain
    ⟨
      q,
      hqNe,
      k,
      hkTop,
      hFactor,
      hSpatialBounded
    ⟩ :=
    distinctCofinalFactorFromPivot_spatialRange_bounded_of_endpointModulus_of_terminalDecay
      hTau
      hEndpoint
      hDecay
      hDistinct

  let X : ℕ → Point3 :=
    fun j : ℕ =>
      x (k j)

  have hXMem :
      ∀ j : ℕ,
        X j ∈ Set.range X := by

    intro j

    exact
      ⟨
        j,
        rfl
      ⟩

  obtain
    ⟨
      y,
      _hyMem,
      phi,
      hPhiStrict,
      hSpatialLimit
    ⟩ :=
    tendsto_subseq_of_bounded
      hSpatialBounded
      hXMem

  let K : ℕ → ℕ :=
    fun j : ℕ =>
      k (phi j)

  have hKTop :
      Tendsto K atTop atTop := by

    dsimp only [K]

    exact
      hkTop.comp
        hPhiStrict.tendsto_atTop

  have hTime :
      Tendsto
        (fun j : ℕ => τ (K j))
        atTop
        (𝓝 T) :=
    hTau.comp
      hKTop

  have hPoint :
      Tendsto
        (fun j : ℕ => x (K j))
        atTop
        (𝓝 y) := by

    simpa [
      Function.comp_def,
      X,
      K
    ] using
      hSpatialLimit

  have hFactorNative :
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

  have hFactorLog :
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
      hFactorNative

  have hFactorK :
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

    have hSub :=
      hFactorLog.comp
        hPhiStrict.tendsto_atTop

    simpa [
      Function.comp_def,
      K
    ] using
      hSub

  exact
    ⟨
      q,
      hqNe,
      y,
      K,
      hKTop,
      hTime,
      hPoint,
      hFactorK
    ⟩

/--
In the eventually bounded residual regime, failure of the canonical factor,
endpoint temporal control, and terminal decay force a distinct finite native
factor `q ≠ 1` on a cofinal channel converging to a finite spatial point.
-/
theorem distinctFiniteSpatialClusterChannel_of_noCanonicalFactor_of_eventuallyBounded_of_endpointModulus_of_terminalDecay
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
    (hDecay :
      H3TerminalComplementGradientSelectedTerminalDecayAtInfinity
        u p x T)
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x)
    (hResidualBounded :
      H3TerminalNativeComplementResidualLogEventuallyBounded
        u p τ x) :
    H3TerminalNativeComplementHasDistinctFiniteSpatialClusterChannel
      u p τ x T := by

  have hDistinct :
      H3TerminalNativeComplementHasDistinctCofinalFactorFromPivot
        u p τ x :=
    distinctCofinalFactorFromPivot_of_noCanonicalFactor_of_eventuallyBounded
      hNoFactor
      hResidualBounded

  exact
    distinctFiniteSpatialClusterChannel_of_distinctCofinalFactorFromPivot_of_endpointModulus_of_terminalDecay
      hTau
      hEndpoint
      hDecay
      hDistinct

/-! ## Refined neutral geometry under bounded residual logs -/

/--
The escape branch contains a pivot cluster at spatial infinity and a distinct
finite native channel converging to a finite spatial point.
-/
def H3TerminalNativeComplementHasPivotInfinityAndDistinctFiniteSpatialChannel
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  H3TerminalNativeComplementHasCofinalPivotClusterAtSpatialInfinity
      u p τ x T
    ∧
  H3TerminalNativeComplementHasDistinctFiniteSpatialClusterChannel
      u p τ x T

/--
Under endpoint temporal control, selected spatial equicontinuity, terminal
decay at infinity, and eventual boundedness of the residual logarithm, failure
of the canonical factor forces exactly the following useful neutral
alternative:

* a pivot cluster at spatial infinity together with a distinct finite native
  channel converging to a finite spatial point; or
* bounded selected range with positive terminal spatial contrast and positive
  witness separation.
-/
theorem nativeComplement_noCanonicalFactor_forces_pivotInfinityAndDistinctFiniteSpatialChannel_or_boundedTerminalContrast
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
    H3TerminalNativeComplementHasPivotInfinityAndDistinctFiniteSpatialChannel
        u p τ x T
      ∨
    (
      Bornology.IsBounded (Set.range x)
        ∧
      H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrastSeparation
        u p x T
    ) := by

  rcases
    nativeComplement_noCanonicalFactor_forces_pivotClusterAtInfinity_or_boundedTerminalContrast
      hTau
      hEndpoint
      hSpatialEquicontinuity
      hDecay
      hNoFactor
    with
    hPivot | hContrast

  · left

    refine
      ⟨
        hPivot,
        ?_
      ⟩

    exact
      distinctFiniteSpatialClusterChannel_of_noCanonicalFactor_of_eventuallyBounded_of_endpointModulus_of_terminalDecay
        hTau
        hEndpoint
        hDecay
        hNoFactor
        hResidualBounded

  · exact
      Or.inr
        hContrast

end

end Euclidean
end Bridge
end PrimeTensor
