import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.ComplementaryGradientResidualIntrinsicCluster

/-!
# Native asymptotic proportionality in the bounded cancellation branch

The intrinsic cluster theorem gives, on a terminal subsequence,

    complement -> q

at every native multiplicative scale, where

    complement = ratio selectedGradient selectedSignedCurl.

This file rewrites that convergence as an intrinsic asymptotic proportionality
law for the two dominant first-order native quantities themselves.

Pointwise,

    ratio selectedGradient (q * selectedSignedCurl)
      =
    ratio complement q.

Since the right-hand side approaches the multiplicative pivot `1`, so does the
left-hand side.

Thus in the bounded cancellation branch,

    selectedGradient ~ q * selectedSignedCurl

intrinsically, at every native scale, along the same terminal subsequence.

The finite native state `q` is the asymptotic multiplicative proportionality
factor.  This is stronger than the already-proved ratio-one statement for the
ordinary real logarithmic magnitudes: it identifies the native multiplicative
normalization itself.

All statements remain conditional necessary alternatives under hypothetical
failure of smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Pointwise native normalization identity -/

/--
Normalizing the selected native gradient by `q` times the correctly signed
native curl is exactly the same native ratio as normalizing the complementary
residual by `q`.
-/
theorem h3TerminalSelectedGradient_normalizedBy_signedCurl_eq_complement_normalized
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (q : MulReal)
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.MulReal.ratio
        (
          h3TerminalNativeGradientForPair
            u p t x
        )
        (
          q *
            h3TerminalSelectedSignedNativeCurlForPair
              u p t x
        )
      =
    PrimeTensor.MulReal.ratio
        (
          h3TerminalNativeComplementGradientForPair
            u p t x
        )
        q := by

  apply
    PrimeTensor.Bridge.MulReal.logValue_injective

  calc
    PrimeTensor.Bridge.MulReal.logValue
        (
          PrimeTensor.MulReal.ratio
            (
              h3TerminalNativeGradientForPair
                u p t x
            )
            (
              q *
                h3TerminalSelectedSignedNativeCurlForPair
                  u p t x
            )
        )
        =
      PrimeTensor.Bridge.MulReal.logValue
          (
            h3TerminalNativeGradientForPair
              u p t x
          )
        -
      PrimeTensor.Bridge.MulReal.logValue
        (
          q *
            h3TerminalSelectedSignedNativeCurlForPair
              u p t x
        ) := by
          exact
            PrimeTensor.Bridge.MulReal.logValue_ratio
              (
                h3TerminalNativeGradientForPair
                  u p t x
              )
              (
                q *
                  h3TerminalSelectedSignedNativeCurlForPair
                    u p t x
              )

    _ =
      PrimeTensor.Bridge.MulReal.logValue
          (
            h3TerminalNativeGradientForPair
              u p t x
          )
        -
      (
        PrimeTensor.Bridge.MulReal.logValue q
          +
        PrimeTensor.Bridge.MulReal.logValue
          (
            h3TerminalSelectedSignedNativeCurlForPair
              u p t x
          )
      ) := by

        rw [
          PrimeTensor.Bridge.MulReal.logValue_mul
        ]

    _ =
      (
        PrimeTensor.Bridge.MulReal.logValue
            (
              h3TerminalNativeGradientForPair
                u p t x
            )
          -
        h3TerminalSelectedSignedNativeCurlLog
          u p t x
      )
        -
      PrimeTensor.Bridge.MulReal.logValue q := by

        rw [
          logValue_h3TerminalSelectedSignedNativeCurlForPair
        ]

        ring

    _ =
      PrimeTensor.Bridge.MulReal.logValue
          (
            h3TerminalNativeComplementGradientForPair
              u p t x
          )
        -
      PrimeTensor.Bridge.MulReal.logValue q := by

        rw [
          ←
          logValue_nativeComplement_eq_gradient_sub_signedCurl
            u p t x
        ]

    _ =
      PrimeTensor.Bridge.MulReal.logValue
        (
          PrimeTensor.MulReal.ratio
            (
              h3TerminalNativeComplementGradientForPair
                u p t x
            )
            q
        ) := by

        symm

        exact
          PrimeTensor.Bridge.MulReal.logValue_ratio
            (
              h3TerminalNativeComplementGradientForPair
                u p t x
            )
            q

/-! ## Native normalization approaches the pivot -/

/--
If the complementary residual logarithm converges to `logValue q`, then its
native ratio with `q` converges intrinsically to the multiplicative pivot.
-/
theorem normalizedComplement_terminalNativeNatConvergesTo_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {q : MulReal}
    (hResidualLog :
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
        )) :
    H3TerminalNativeNatConvergesTo
      (
        fun n : ℕ =>
          PrimeTensor.MulReal.ratio
            (
              h3TerminalNativeComplementGradientForPair
                u p
                (τ n)
                (x n)
            )
            q
      )
      (1 : MulReal) := by

  apply
    terminalNativeNatConvergesTo_of_logValue_tendsto

  have hSub :
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
              -
            PrimeTensor.Bridge.MulReal.logValue q
        )
        atTop
        (
          𝓝
            (
              PrimeTensor.Bridge.MulReal.logValue q
                -
              PrimeTensor.Bridge.MulReal.logValue q
            )
        ) :=
    hResidualLog.sub
      tendsto_const_nhds

  simpa only [
    PrimeTensor.Bridge.MulReal.logValue_ratio,
    PrimeTensor.Bridge.MulReal.logValue_one,
    sub_self
  ] using hSub

/--
The same normalized convergence may be written directly as asymptotic native
proportionality between the selected gradient and `q` times the signed curl.
-/
theorem selectedGradient_normalizedBy_signedCurl_terminalNativeNatConvergesTo_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {q : MulReal}
    (hResidualLog :
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
        )) :
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
              q *
                h3TerminalSelectedSignedNativeCurlForPair
                  u p
                  (τ n)
                  (x n)
            )
      )
      (1 : MulReal) := by

  have hNormalizedComplement :
      H3TerminalNativeNatConvergesTo
        (
          fun n : ℕ =>
            PrimeTensor.MulReal.ratio
              (
                h3TerminalNativeComplementGradientForPair
                  u p
                  (τ n)
                  (x n)
              )
              q
        )
        (1 : MulReal) :=
    normalizedComplement_terminalNativeNatConvergesTo_one
      hResidualLog

  intro level

  have hEventually :=
    hNormalizedComplement level

  filter_upwards
    [hEventually]
    with n hn

  rw [
    h3TerminalSelectedGradient_normalizedBy_signedCurl_eq_complement_normalized
      u p q
      (τ n)
      (x n)
  ]

  exact hn

/-! ## Asymptotic proportionality package -/

def H3TerminalNativeComplementAsymptoticProportionality
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
                  q *
                    h3TerminalSelectedSignedNativeCurlForPair
                      u p
                      (τ n)
                      (x n)
                )
          )
          (1 : MulReal)
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
Upgrade intrinsic finite-cluster matching to the native asymptotic
proportionality law

    selectedGradient ~ q * selectedSignedCurl.
-/
theorem nativeComplementAsymptoticProportionality_of_intrinsicClusterMatching
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hCluster :
      H3TerminalNativeComplementIntrinsicClusterMatching
        u a T p sCurl sGradient) :
    H3TerminalNativeComplementAsymptoticProportionality
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
      hComplementNative,
      hResidualNative,
      hResidualLogTendsto,
      hRatio,
      hRelativeCurl,
      hRelativeGradient
    ⟩ :=
    hCluster

  have hProportional :
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
                q *
                  h3TerminalSelectedSignedNativeCurlForPair
                    u p
                    (τ n)
                    (x n)
              )
        )
        (1 : MulReal) :=
    selectedGradient_normalizedBy_signedCurl_terminalNativeNatConvergesTo_one
      hResidualLogTendsto

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
      hProportional,
      hResidualLogTendsto,
      hRatio,
      hRelativeCurl,
      hRelativeGradient
    ⟩

/-! ## Exhaustive terminal alternative with native proportionality -/

/--
Under hypothetical nonextension, one fixed structural pair satisfies one of:

1. reinforcing-sign complementary escape;
2. cancellation-compatible synchronized triple escape on a subsequence;
3. cancellation-compatible bounded residual for which there is a finite native
   state `q` such that

       selectedGradient ~ q * selectedSignedCurl

   intrinsically at every native scale along a terminal subsequence.

The exact residual law and all previous ratio-one / lower-order conclusions
remain available.
-/
theorem fixed_nativeComplementGradient_threeBranchAlternative_withAsymptoticProportionality_of_noH3PathExtension
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
          H3TerminalNativeComplementAsymptoticProportionality
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
    fixed_nativeComplementGradient_threeBranchAlternative_withIntrinsicResidualCluster_of_noH3PathExtension
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
                  nativeComplementAsymptoticProportionality_of_intrinsicClusterMatching
                    hCluster
                )
            )
        ⟩

/-! ## Neutral package -/

/--
Neutral continuation alternative with native asymptotic proportionality in the
bounded cancellation branch.
-/
theorem smoothContinuationExtension_or_fixed_nativeComplementGradient_threeBranchAlternative_withAsymptoticProportionality
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
            H3TerminalNativeComplementAsymptoticProportionality
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
          fixed_nativeComplementGradient_threeBranchAlternative_withAsymptoticProportionality_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
