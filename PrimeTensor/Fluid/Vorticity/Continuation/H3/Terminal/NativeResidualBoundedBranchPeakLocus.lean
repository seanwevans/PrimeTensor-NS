import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSelectedClosurePeakLocus
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualBoundedFactorAlternative

/-!
# Thread bounded cancellation directly into the closure peak-locus alternative

The closure-geometry development used the helper predicate

    H3TerminalNativeComplementResidualLogEventuallyBounded u p τ x.

That predicate is not an additional analytic frontier in the bounded
cancellation branch.

The older bounded cancellation package already carries the stronger-looking
estimate

    |logValue (native complementary gradient)| ≤ C

eventually on the same selected spacetime sequence.

By the exact identity

    native complementary gradient
      = gradient / selected signed curl,

this is definitionally the same bounded residual logarithm after rewriting.

This file records that bridge explicitly and then removes
`H3TerminalNativeComplementResidualLogEventuallyBounded` from the hypotheses
of the final no-canonical-factor peak-locus theorem: the theorem now consumes
the raw complementary logarithm bound already produced upstream.

It also shows that every witness sequence extracted from
`H3TerminalNativeComplementBoundedFactorAlternative` automatically carries
the residual-log boundedness needed by the later geometry.

No new PDE regularity is assumed here.  The remaining genuine analytic
frontiers are endpoint temporal control, selected spatial equicontinuity, and
terminal spatial decay.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Raw complementary bound equals residual-log boundedness -/

/--
An eventual bound on the logarithm of the native complementary gradient gives
the exact eventual residual-log boundedness used by the later cluster and
closure geometry.
-/
theorem nativeComplementResidualLogEventuallyBounded_of_complementBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {N : ℕ}
    {C : ℝ}
    (hComplementBound :
      ∀ n : ℕ,
        N ≤ n →
        abs
          (
            PrimeTensor.Bridge.MulReal.logValue
              (
                h3TerminalNativeComplementGradientForPair
                  u p
                  (τ n)
                  (x n)
              )
          )
          ≤ C) :
    H3TerminalNativeComplementResidualLogEventuallyBounded
      u p τ x := by

  refine
    ⟨
      N,
      C,
      ?_
    ⟩

  intro n hn

  have h :=
    hComplementBound
      n
      hn

  simpa [
    h3TerminalNativeComplementResidualLogSequence,
    ← h3TerminalNativeComplementGradientForPair_eq_residualRatio
  ] using
    h

/-! ## Thread the old bounded-factor witnesses forward -/

/--
Every witness sequence in the old bounded-factor alternative automatically
has eventually bounded exact residual logarithm.

The conclusion retains the same terminal sequence and the same final
canonical-factor / two-cluster alternative, so later refinements can work on
those witnesses without introducing a second boundedness assumption.
-/
theorem boundedFactorAlternative_has_residualLogBounded_witnesses
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hBounded :
      H3TerminalNativeComplementBoundedFactorAlternative
        u a T p sCurl sGradient) :
    ∃ τ : ℕ → ℝ,
      ∃ x : ℕ → Point3,
        (
          ∀ n : ℕ,
            τ n ∈ Set.Ioo a T
              ∧
            τ n ∈
              Set.Ioo
                (T - (1 : ℝ) / ((n : ℝ) + 1))
                T
        )
          ∧
        Tendsto τ atTop (𝓝 T)
          ∧
        H3TerminalNativeComplementResidualLogEventuallyBounded
          u p τ x
          ∧
        (
          H3TerminalNativeComplementHasCanonicalFactor
              u p τ x
            ∨
          H3TerminalNativeComplementHasTwoDistinctClusterFactors
              u p τ x
        ) := by

  obtain
    ⟨
      τ,
      x,
      N,
      C,
      hτ,
      hTau,
      _hCancellation,
      _hCurlDirectional,
      _hGradientDirectional,
      hBound,
      _hRatio,
      _hRelativeCurl,
      _hRelativeGradient,
      hFactorAlternative
    ⟩ :=
    hBounded

  have hResidualBounded :
      H3TerminalNativeComplementResidualLogEventuallyBounded
        u p τ x :=
    nativeComplementResidualLogEventuallyBounded_of_complementBound
      (N := N)
      (C := C)
      (fun n hn => (hBound n hn).1)

  exact
    ⟨
      τ,
      x,
      hτ,
      hTau,
      hResidualBounded,
      hFactorAlternative
    ⟩

/-! ## Peak-locus theorem using the upstream raw bound directly -/

/--
The final no-canonical-factor closure-geometry alternative can consume the raw
eventual complementary logarithm bound produced by the original bounded
cancellation branch.

Thus residual-log boundedness is no longer a separate hypothesis at this
stage.
-/
theorem nativeComplement_noCanonicalFactor_forces_pivotInfinityAndCompactPeakLocus_or_boundedTerminalContrast_of_complementBound
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    {N : ℕ}
    {C : ℝ}
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
    (hComplementBound :
      ∀ n : ℕ,
        N ≤ n →
        abs
          (
            PrimeTensor.Bridge.MulReal.logValue
              (
                h3TerminalNativeComplementGradientForPair
                  u p
                  (τ n)
                  (x n)
              )
          )
          ≤ C)
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
    H3TerminalNativeComplementHasPivotInfinityAndCompactPeakLocus
        u p τ x T hTerminalModulus
      ∨
    (
      Bornology.IsBounded (Set.range x)
        ∧
      H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrastSeparation
        u p x T
    ) := by

  have hResidualBounded :
      H3TerminalNativeComplementResidualLogEventuallyBounded
        u p τ x :=
    nativeComplementResidualLogEventuallyBounded_of_complementBound
      (N := N)
      (C := C)
      hComplementBound

  exact
    nativeComplement_noCanonicalFactor_forces_pivotInfinityAndCompactPeakLocus_or_boundedTerminalContrast
      hTau
      hEndpoint
      hSpatialEquicontinuity
      hDecay
      hResidualBounded
      hNoFactor

end

end Euclidean
end Bridge
end PrimeTensor
