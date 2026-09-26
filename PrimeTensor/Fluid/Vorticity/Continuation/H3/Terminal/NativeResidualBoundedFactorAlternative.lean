import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualDistinctClusters

/-!
# Exhaustive bounded-residual factor alternative

The bounded cancellation branch previously retained:

* terminal localization of one spacetime sequence `(τ,x)`;
* curl and selected-gradient directional escape;
* eventual boundedness of the complementary residual logarithm;
* ratio-one matching of the two dominant oriented logarithms;
* logarithmic negligibility of the residual relative to both dominant scales.

The residual Cauchy development now gives an exact refinement on that same
fixed sequence:

    full canonical native factor

or

    persistent residual-log tail separation.

Because the residual is already eventually bounded in this branch, the second
case yields two distinct finite native cluster factors on cofinal refinements.

This file packages that refinement without discarding any of the previously
proved bounded-branch information.

It remains deliberately neutral: the two-cluster branch is a genuine bounded
nonconvergence alternative, not a blowup conclusion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Refined bounded cancellation package -/

/--
Bounded cancellation on one fixed terminal sequence, together with the exact
full-factor alternative on that same sequence.
-/
def H3TerminalNativeComplementBoundedFactorAlternative
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation) : Prop :=
  ∃
    τ : ℕ → ℝ,
    ∃ x : ℕ → Point3,
      ∃ N : ℕ,
        ∃ C : ℝ,
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
          (
            ∀ n : ℕ,
              N ≤ n →
              (
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
                  ≤ C
              )
                ∧
              (
                abs
                  (
                    PrimeTensor.Bridge.MulReal.logValue
                      (
                        h3TerminalNativeGradientForPair
                          u p
                          (τ n)
                          (x n)
                      )
                      -
                    h3TerminalSelectedSignedNativeCurlLog
                      u p
                      (τ n)
                      (x n)
                  )
                  ≤ C
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
            ∧
          (
            H3TerminalNativeComplementHasCanonicalFactor
              u p τ x
              ∨
            H3TerminalNativeComplementHasTwoDistinctClusterFactors
              u p τ x
          )

/--
Upgrade the existing bounded-relative-negligible package by resolving the
remaining full-sequence topology on its original witnesses:

* Cauchy residual log gives a full canonical factor;
* non-Cauchy residual log gives persistent separation, and boundedness then
  extracts two distinct finite cluster factors.
-/
theorem nativeComplementBoundedFactorAlternative_of_boundedRelativeNegligible
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hBounded :
      H3TerminalNativeComplementBoundedRelativeNegligible
        u a T p sCurl sGradient) :
    H3TerminalNativeComplementBoundedFactorAlternative
      u a T p sCurl sGradient := by

  obtain
    ⟨
      τ,
      x,
      N,
      C,
      hτ,
      hTauTendsto,
      hCancellation,
      hCurlDirectional,
      hGradientDirectional,
      hBound,
      hRatio,
      hRelativeCurl,
      hRelativeGradient
    ⟩ :=
    hBounded

  have hFactorAlternative :
      H3TerminalNativeComplementHasCanonicalFactor
          u p τ x
        ∨
      H3TerminalNativeComplementHasTwoDistinctClusterFactors
          u p τ x := by

    rcases
      nativeComplementHasCanonicalFactor_or_persistentTailSeparation
        u p τ x
      with
      hFactor | hSeparated

    · exact
        Or.inl hFactor

    · exact
        Or.inr
          (
            nativeComplementHasTwoDistinctClusterFactors_of_complementBound_of_persistentTailSeparation
              u p τ x
              N C
              (fun n hn => (hBound n hn).1)
              hSeparated
          )

  exact
    ⟨
      τ,
      x,
      N,
      C,
      hτ,
      hTauTendsto,
      hCancellation,
      hCurlDirectional,
      hGradientDirectional,
      hBound,
      hRatio,
      hRelativeCurl,
      hRelativeGradient,
      hFactorAlternative
    ⟩

/-! ## Refined terminal alternative -/

/--
Under hypothetical nonextension, one fixed structural pair satisfies one of:

1. reinforcing-sign complementary escape;
2. cancellation-compatible synchronized triple escape;
3. bounded cancellation on one terminal sequence, retaining ratio-one matching
   and relative negligibility, and on that same sequence either
   a full canonical native factor exists or there are two distinct finite
   native cluster factors.

Thus the bounded branch no longer stops at existence of one extracted finite
cluster state: its remaining topology is split exhaustively into convergence
versus bounded nonconvergence.
-/
theorem fixed_nativeComplementGradient_threeBranchAlternative_withBoundedFactorAlternative_of_noH3PathExtension
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
          H3TerminalNativeComplementBoundedFactorAlternative
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
    fixed_nativeComplementGradient_threeBranchAlternative_withNegligibleResidual_of_noH3PathExtension
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

  · rcases hRest with hTriple | hBounded

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
                  nativeComplementBoundedFactorAlternative_of_boundedRelativeNegligible
                    hBounded
                )
            )
        ⟩

/-! ## Neutral continuation package -/

/--
Neutral continuation alternative with the bounded residual branch resolved into
full canonical convergence versus two distinct finite cluster factors.
-/
theorem smoothContinuationExtension_or_fixed_nativeComplementGradient_threeBranchAlternative_withBoundedFactorAlternative
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
            H3TerminalNativeComplementBoundedFactorAlternative
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
          fixed_nativeComplementGradient_threeBranchAlternative_withBoundedFactorAlternative_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
