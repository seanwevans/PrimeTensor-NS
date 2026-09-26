import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.ComplementaryGradientNativeResidual

/-!
# Relative negligibility of the bounded complementary native residual

The exact native residual identity is

    complement
      =
    ratio selected signedCurl.

In the bounded cancellation branch, the logarithm of this residual is
eventually bounded while both correctly oriented dominant logarithms tend to
`+∞`.

Consequently the residual logarithm is lower order relative to either dominant
scale:

    |log complement| / oriented signedCurlLog -> 0,

and

    |log complement| / oriented selectedGradientLog -> 0.

Together with the previously proved ratio-one law

    oriented selectedGradientLog / oriented signedCurlLog -> 1,

this gives a quantitative asymptotic description of the bounded cancellation
branch: the two large terms match to leading order and their exact native
multiplicative residual is logarithmically negligible relative to both.

All terminal statements remain necessary consequences conditional on
hypothetical failure of smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Generic bounded-over-divergent lemma -/

/--
If `|Rₙ|` is eventually bounded and `Bₙ -> +∞`, then `|Rₙ| / Bₙ -> 0`.
-/
private theorem bounded_abs_div_tendsto_zero_of_atTop
    {R B : ℕ → ℝ}
    (hBTendsto :
      Tendsto B atTop atTop)
    {N : ℕ}
    {C : ℝ}
    (hBound :
      ∀ n : ℕ,
        N ≤ n →
        abs (R n) ≤ C) :
    Tendsto
      (fun n : ℕ => abs (R n) / B n)
      atTop
      (𝓝 0) := by

  apply
    Metric.tendsto_nhds.mpr

  intro ε hε

  let C₀ : ℝ :=
    max C 0

  let K : ℝ :=
    max
      1
      (C₀ / ε + 1)

  have hEventuallyB :
      ∀ᶠ n : ℕ in atTop,
        K ≤ B n :=
    (tendsto_atTop.1 hBTendsto)
      K

  have hEventuallyN :
      ∀ᶠ n : ℕ in atTop,
        N ≤ n :=
    eventually_ge_atTop N

  filter_upwards
    [hEventuallyB, hEventuallyN]
    with n hnB hnN

  rw [
    Real.dist_eq,
    sub_zero
  ]

  have hOneLeB :
      1 ≤ B n := by

    exact
      le_trans
        (le_max_left
          (1 : ℝ)
          (C₀ / ε + 1))
        hnB

  have hBPos :
      0 < B n :=
    lt_of_lt_of_le
      zero_lt_one
      hOneLeB

  have hBound₀ :
      abs (R n)
        ≤
      C₀ := by

    exact
      le_trans
        (hBound n hnN)
        (le_max_left C 0)

  have hThreshold :
      C₀ / ε + 1
        ≤
      B n := by

    exact
      le_trans
        (le_max_right
          (1 : ℝ)
          (C₀ / ε + 1))
        hnB

  have hDivLt :
      C₀ / ε
        <
      B n := by
    linarith

  have hCLt :
      C₀
        <
      ε * B n := by

    have hTmp :
        C₀ < B n * ε :=
      (div_lt_iff₀ hε).1
        hDivLt

    simpa only [mul_comm] using hTmp

  have hRatio :
      C₀ / B n
        <
      ε := by

    exact
      (div_lt_iff₀ hBPos).2
        hCLt

  have hNonneg :
      0
        ≤
      abs (R n) / B n :=
    div_nonneg
      (abs_nonneg _)
      (le_of_lt hBPos)

  rw [
    abs_of_nonneg hNonneg
  ]

  exact
    lt_of_le_of_lt
      (
        (
          div_le_div_iff_of_pos_right
            hBPos
        ).2
          hBound₀
      )
      hRatio

/-! ## Residual negligibility relative to the signed curl -/

/--
In the bounded cancellation branch, the complementary residual logarithm is
negligible relative to the correctly oriented signed-curl logarithm.
-/
theorem boundedComplementResidual_relativeTo_signedCurl_tendsto_zero
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hCancellation :
      H3TerminalComplementCancellationRegime
        p sCurl sGradient)
    (hCurlDirectional :
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeCurlForPair
              u p
              (τ n)
              (x n)
        )
        sCurl)
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
      (𝓝 0) := by

  have hDenTendsto :
      Tendsto
        (
          fun n : ℕ =>
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
        atTop :=
    oriented_selectedSignedNativeCurlLog_tendsto_atTop_of_cancellation
      hCancellation
      hCurlDirectional

  exact
    bounded_abs_div_tendsto_zero_of_atTop
      hDenTendsto
      hComplementBound

/-! ## Residual negligibility relative to the selected gradient -/

/--
In the bounded cancellation branch, the complementary residual logarithm is
also negligible relative to the correctly oriented selected-gradient
logarithm.
-/
theorem boundedComplementResidual_relativeTo_selectedGradient_tendsto_zero
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hGradientDirectional :
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeGradientForPair
              u p
              (τ n)
              (x n)
        )
        sGradient)
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
      (𝓝 0) := by

  have hDenTendsto :
      Tendsto
        (
          fun n : ℕ =>
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
        atTop :=
    orientedLog_tendsto_atTop_of_nativeDirectionalEscape
      hGradientDirectional

  exact
    bounded_abs_div_tendsto_zero_of_atTop
      hDenTendsto
      hComplementBound

/-! ## Strengthened bounded cancellation package -/

def H3TerminalNativeComplementBoundedRelativeNegligible
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

/--
Upgrade the bounded ratio-matching branch by adding logarithmic relative
negligibility of the exact native residual with respect to both dominant
scales.
-/
theorem nativeComplementBoundedRelativeNegligible_of_ratioMatching
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hMatching :
      H3TerminalNativeComplementBoundedRatioMatching
        u a T p sCurl sGradient) :
    H3TerminalNativeComplementBoundedRelativeNegligible
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
      hRatio
    ⟩ :=
    hMatching

  have hComplementBound :
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
          ≤ C :=
    fun n hn =>
      (hBound n hn).1

  have hRelativeCurl :
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
        (𝓝 0) :=
    boundedComplementResidual_relativeTo_signedCurl_tendsto_zero
      hCancellation
      hCurlDirectional
      hComplementBound

  have hRelativeGradient :
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
        (𝓝 0) :=
    boundedComplementResidual_relativeTo_selectedGradient_tendsto_zero
      hGradientDirectional
      hComplementBound

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
      hRelativeGradient
    ⟩

/-! ## Exhaustive terminal alternative with negligible bounded residual -/

/--
Under hypothetical nonextension, one fixed structural pair satisfies one of:

1. reinforcing-sign complementary escape;
2. cancellation-compatible synchronized triple escape on a subsequence;
3. cancellation-compatible bounded residual, with ratio-one dominant matching
   and residual logarithm negligible relative to both dominant logarithmic
   scales.

The exact native residual law

    complement = ratio selected signedCurl

holds pointwise for the selected pair in every branch.
-/
theorem fixed_nativeComplementGradient_threeBranchAlternative_withNegligibleResidual_of_noH3PathExtension
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
          H3TerminalNativeComplementBoundedRelativeNegligible
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
    fixed_nativeComplementGradient_threeBranchAlternative_withResidualLaw_of_noH3PathExtension
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
                  nativeComplementBoundedRelativeNegligible_of_ratioMatching
                    hBounded
                )
            )
        ⟩

/-! ## Neutral package -/

/--
Neutral continuation alternative with exact native residual law and logarithmic
relative negligibility in the bounded cancellation branch.
-/
theorem smoothContinuationExtension_or_fixed_nativeComplementGradient_threeBranchAlternative_withNegligibleResidual
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
            H3TerminalNativeComplementBoundedRelativeNegligible
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
          fixed_nativeComplementGradient_threeBranchAlternative_withNegligibleResidual_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
