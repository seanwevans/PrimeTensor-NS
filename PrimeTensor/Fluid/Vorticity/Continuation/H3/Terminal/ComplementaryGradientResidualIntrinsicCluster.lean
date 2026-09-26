import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.ComplementaryGradientResidualCluster
import PrimeTensor.Bridge.MulReal.Scale.Semantics

/-!
# Intrinsic native cluster convergence of the bounded complementary residual

The preceding file extracts, in the bounded cancellation branch, a terminal
subsequence and a finite native state `q : MulReal` such that

    logValue complement_n -> logValue q.

`MulReal` does not use an ordinary ambient topological structure in the native
development.  Its intrinsic notion of nearness is `MulReal.ScaleNear`.

For an `ℕ`-indexed terminal sequence, the natural intrinsic convergence notion
is therefore:

    at every native scale, eventually the sequence is `ScaleNear` the target.

The logarithmic convergence theorem `scaleNear_of_logValue_lt` immediately
converts ordinary real log convergence into this intrinsic native convergence.

Because the complementary native derivative is pointwise exactly

    ratio selectedGradient selectedSignedCurl,

the multiplicative residual ratio itself converges intrinsically to the same
finite native cluster state.

Thus the bounded cancellation branch can now be stated entirely in the native
carrier:

* the curl and selected-gradient logarithmic scales diverge and match;
* their exact multiplicative residual remains lower order;
* along a terminal subsequence that residual converges to a finite native
  `MulReal` state at every intrinsic multiplicative scale.

This remains a conditional necessary terminal alternative, not evidence that a
nonextendible path exists.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Native convergence for terminal natural-number sequences -/

/--
Intrinsic convergence for an `ℕ`-indexed sequence of completed multiplicative
reals: at every native scale, the sequence is eventually `ScaleNear` the
target.
-/
def H3TerminalNativeNatConvergesTo
    (Ω : ℕ → MulReal)
    (q : MulReal) : Prop :=
  ∀ level : Depth,
    ∀ᶠ n : ℕ in atTop,
      PrimeTensor.MulReal.ScaleNear
        level
        (Ω n)
        q

/--
Ordinary convergence of canonical logarithmic coordinates implies intrinsic
native convergence at every multiplicative scale for an `ℕ`-indexed terminal
sequence.
-/
theorem terminalNativeNatConvergesTo_of_logValue_tendsto
    {Ω : ℕ → MulReal}
    {q : MulReal}
    (hLog :
      Tendsto
        (
          fun n : ℕ =>
            PrimeTensor.Bridge.MulReal.logValue
              (Ω n)
        )
        atTop
        (
          𝓝
            (
              PrimeTensor.Bridge.MulReal.logValue q
            )
        )) :
    H3TerminalNativeNatConvergesTo
      Ω q := by

  intro level

  have hRadiusPos :
      0 <
        PrimeTensor.Bridge.logScaleRadius
          level :=
    PrimeTensor.Bridge.logScaleRadius_pos
      level

  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        dist
          (
            PrimeTensor.Bridge.MulReal.logValue
              (Ω n)
          )
          (
            PrimeTensor.Bridge.MulReal.logValue q
          )
          <
        PrimeTensor.Bridge.logScaleRadius
          level :=
    (
      Metric.tendsto_nhds.mp
        hLog
    )
      (
        PrimeTensor.Bridge.logScaleRadius
          level
      )
      hRadiusPos

  filter_upwards
    [hEventually]
    with n hn

  rw [
    Real.dist_eq
  ] at hn

  exact
    PrimeTensor.Bridge.MulReal.scaleNear_of_logValue_lt
      hn

/-!
The pointwise residual identity transports intrinsic convergence from the
complementary derivative to the explicit multiplicative residual ratio.
-/
theorem residualRatio_terminalNativeNatConvergesTo_of_complement
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (q : MulReal)
    (hComplement :
      H3TerminalNativeNatConvergesTo
        (
          fun n : ℕ =>
            h3TerminalNativeComplementGradientForPair
              u p
              (τ n)
              (x n)
        )
        q) :
    H3TerminalNativeNatConvergesTo
      (
        fun n : ℕ =>
          PrimeTensor.MulReal.ratio
            (
              h3TerminalNativeGradientForPair
                u p
                (τ n)
                (x n)
            )
            (
              h3TerminalSelectedSignedNativeCurlForPair
                u p
                (τ n)
                (x n)
            )
      )
      q := by

  intro level

  have hEventually :=
    hComplement level

  filter_upwards
    [hEventually]
    with n hn

  rw [
    ←
    h3TerminalNativeComplementGradientForPair_eq_residualRatio
      u p
      (τ n)
      (x n)
  ]

  exact hn

/-! ## Intrinsic finite-cluster package -/

def H3TerminalNativeComplementIntrinsicClusterMatching
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation) : Prop :=
  ∃
    τ : ℕ → ℝ,
    ∃ x : ℕ → Point3,
      ∃ q : MulReal,
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
        H3TerminalComplementCancellationRegime
          p sCurl sGradient
          ∧
        H3TerminalNativeLogDirectionalEscape
          (
            fun n : ℕ =>
              h3TerminalNativeCurlForPair
                u p
                (τ n)
                (x n)
          )
          sCurl
          ∧
        H3TerminalNativeLogDirectionalEscape
          (
            fun n : ℕ =>
              h3TerminalNativeGradientForPair
                u p
                (τ n)
                (x n)
          )
          sGradient
          ∧
        H3TerminalNativeNatConvergesTo
          (
            fun n : ℕ =>
              h3TerminalNativeComplementGradientForPair
                u p
                (τ n)
                (x n)
          )
          q
          ∧
        H3TerminalNativeNatConvergesTo
          (
            fun n : ℕ =>
              PrimeTensor.MulReal.ratio
                (
                  h3TerminalNativeGradientForPair
                    u p
                    (τ n)
                    (x n)
                )
                (
                  h3TerminalSelectedSignedNativeCurlForPair
                    u p
                    (τ n)
                    (x n)
                )
          )
          q
          ∧
        Tendsto
          (
            fun n : ℕ =>
              PrimeTensor.Bridge.MulReal.logValue
                (
                  h3TerminalNativeComplementGradientForPair
                    u p
                    (τ n)
                    (x n)
                )
          )
          atTop
          (
            𝓝
              (
                PrimeTensor.Bridge.MulReal.logValue q
              )
          )
          ∧
        Tendsto
          (
            fun n : ℕ =>
              (
                h3TerminalOrientedValue
                  sGradient
                  (
                    PrimeTensor.Bridge.MulReal.logValue
                      (
                        h3TerminalNativeGradientForPair
                          u p
                          (τ n)
                          (x n)
                      )
                  )
              )
                /
              (
                h3TerminalOrientedValue
                  sGradient
                  (
                    h3TerminalSelectedSignedNativeCurlLog
                      u p
                      (τ n)
                      (x n)
                  )
              )
          )
          atTop
          (𝓝 1)
          ∧
        Tendsto
          (
            fun n : ℕ =>
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
                /
              h3TerminalOrientedValue
                sGradient
                (
                  h3TerminalSelectedSignedNativeCurlLog
                    u p
                    (τ n)
                    (x n)
                )
          )
          atTop
          (𝓝 0)
          ∧
        Tendsto
          (
            fun n : ℕ =>
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
                /
              h3TerminalOrientedValue
                sGradient
                (
                  PrimeTensor.Bridge.MulReal.logValue
                    (
                      h3TerminalNativeGradientForPair
                        u p
                        (τ n)
                        (x n)
                    )
                )
          )
          atTop
          (𝓝 0)

/--
Upgrade a finite log-coordinate residual cluster to intrinsic native
convergence at every multiplicative scale, both for the complementary
derivative and for its explicit residual-ratio representation.
-/
theorem nativeComplementIntrinsicClusterMatching_of_finiteClusterMatching
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hCluster :
      H3TerminalNativeComplementFiniteClusterMatching
        u a T p sCurl sGradient) :
    H3TerminalNativeComplementIntrinsicClusterMatching
      u a T p sCurl sGradient := by

  obtain
    ⟨
      τ,
      x,
      q,
      hτ,
      hTauTendsto,
      hCancellation,
      hCurlDirectional,
      hGradientDirectional,
      hResidualLogTendsto,
      hRatio,
      hRelativeCurl,
      hRelativeGradient
    ⟩ :=
    hCluster

  have hComplementNative :
      H3TerminalNativeNatConvergesTo
        (
          fun n : ℕ =>
            h3TerminalNativeComplementGradientForPair
              u p
              (τ n)
              (x n)
        )
        q :=
    terminalNativeNatConvergesTo_of_logValue_tendsto
      hResidualLogTendsto

  have hResidualNative :
      H3TerminalNativeNatConvergesTo
        (
          fun n : ℕ =>
            PrimeTensor.MulReal.ratio
              (
                h3TerminalNativeGradientForPair
                  u p
                  (τ n)
                  (x n)
              )
              (
                h3TerminalSelectedSignedNativeCurlForPair
                  u p
                  (τ n)
                  (x n)
              )
        )
        q :=
    residualRatio_terminalNativeNatConvergesTo_of_complement
      u p τ x q
      hComplementNative

  exact
    ⟨
      τ,
      x,
      q,
      hτ,
      hTauTendsto,
      hCancellation,
      hCurlDirectional,
      hGradientDirectional,
      hComplementNative,
      hResidualNative,
      hResidualLogTendsto,
      hRatio,
      hRelativeCurl,
      hRelativeGradient
    ⟩

/-! ## Exhaustive terminal alternative with intrinsic finite residual cluster -/

/--
Under hypothetical nonextension, one fixed structural pair satisfies one of:

1. reinforcing-sign complementary escape;
2. cancellation-compatible synchronized triple escape on a subsequence;
3. cancellation-compatible bounded residual whose exact native multiplicative
   residual converges, on a terminal subsequence, to a finite native state at
   every intrinsic `ScaleNear` scale.

The bounded branch still retains ratio-one dominant matching and logarithmic
relative negligibility.
-/
theorem fixed_nativeComplementGradient_threeBranchAlternative_withIntrinsicResidualCluster_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃
      p : H3TerminalCurlGradientPair,
      ∃
        sCurl sGradient : H3TerminalOrientation,
        H3TerminalNativeCurlGradientResidualLaw
          u p
          ∧
        (
          (
            H3TerminalComplementForcedRegime
              p sCurl sGradient
              ∧
            H3TerminalNativeComplementGradientForcedCascade
              u a T p sCurl sGradient
          )
            ∨
          (
            ∃ sComplement : H3TerminalOrientation,
              H3TerminalNativeCurlGradientComplementTripleEscape
                u a T p sCurl sGradient sComplement
          )
            ∨
          H3TerminalNativeComplementIntrinsicClusterMatching
            u a T p sCurl sGradient
        ) := by

  obtain
    ⟨
      p,
      sCurl,
      sGradient,
      hResidualLaw,
      hAlternative
    ⟩ :=
    fixed_nativeComplementGradient_threeBranchAlternative_withFiniteResidualCluster_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  rcases hAlternative with hForced | hRest

  · exact
      ⟨
        p,
        sCurl,
        sGradient,
        hResidualLaw,
        Or.inl hForced
      ⟩

  · rcases hRest with hTriple | hCluster

    · exact
        ⟨
          p,
          sCurl,
          sGradient,
          hResidualLaw,
          Or.inr
            (
              Or.inl hTriple
            )
        ⟩

    · exact
        ⟨
          p,
          sCurl,
          sGradient,
          hResidualLaw,
          Or.inr
            (
              Or.inr
                (
                  nativeComplementIntrinsicClusterMatching_of_finiteClusterMatching
                    hCluster
                )
            )
        ⟩

/-! ## Neutral package -/

/--
Neutral continuation alternative with an intrinsic finite native residual
cluster in the bounded cancellation branch.
-/
theorem smoothContinuationExtension_or_fixed_nativeComplementGradient_threeBranchAlternative_withIntrinsicResidualCluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      ∃
        p : H3TerminalCurlGradientPair,
        ∃
          sCurl sGradient : H3TerminalOrientation,
          H3TerminalNativeCurlGradientResidualLaw
            u p
            ∧
          (
            (
              H3TerminalComplementForcedRegime
                p sCurl sGradient
                ∧
              H3TerminalNativeComplementGradientForcedCascade
                u a T p sCurl sGradient
            )
              ∨
            (
              ∃ sComplement : H3TerminalOrientation,
                H3TerminalNativeCurlGradientComplementTripleEscape
                  u a T p sCurl sGradient sComplement
            )
              ∨
            H3TerminalNativeComplementIntrinsicClusterMatching
              u a T p sCurl sGradient
          )
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl hExtension

  · exact
      Or.inr
        (
          fixed_nativeComplementGradient_threeBranchAlternative_withIntrinsicResidualCluster_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
