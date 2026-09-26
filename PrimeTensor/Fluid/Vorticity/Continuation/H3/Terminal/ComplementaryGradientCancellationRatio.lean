import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.ComplementaryGradientCancellationRefinement

/-!
# Ratio-one matching in the bounded complementary-gradient cancellation branch

The refined complementary-gradient alternative gives, in the
cancellation-compatible branch, either

* tail-cofinal unboundedness of the complementary derivative, or
* eventual boundedness of the complementary logarithm and hence a uniformly
  bounded additive defect between two diverging cancelling terms.

The second branch has a sharper asymptotic consequence.

After applying the selected-gradient orientation, let

    Aₙ = oriented selected-gradient logarithm,
    Bₙ = oriented correctly-signed curl logarithm.

Cancellation compatibility makes `Bₙ` exactly the curl logarithm in the
orientation in which it tends to `+∞`.  The bounded complementary derivative
gives

    |Aₙ - Bₙ| ≤ C

eventually.  Therefore

    Aₙ / Bₙ → 1.

This file formalizes that ratio-one matching without imposing any extra
regularity or excluding the tail-unbounded complementary branch.

All terminal statements remain necessary consequences conditional on
hypothetical failure of smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Directional escape as positive escape after orientation -/

/--
A native logarithmic directional escape becomes an ordinary `atTop` limit after
applying its fixed orientation.
-/
theorem orientedLog_tendsto_atTop_of_nativeDirectionalEscape
    {Ω : ℕ → PrimeTensor.MulReal}
    {s : H3TerminalOrientation}
    (hDirectional :
      H3TerminalNativeLogDirectionalEscape
        Ω s) :
    Tendsto
      (
        fun n : ℕ =>
          h3TerminalOrientedValue
            s
            (
              PrimeTensor.Bridge.MulReal.logValue
                (Ω n)
            )
      )
      atTop
      atTop := by

  cases s with

  | positive =>

      unfold H3TerminalNativeLogDirectionalEscape at hDirectional

      simpa only [
        h3TerminalOrientedValue_positive
      ] using hDirectional

  | negative =>

      unfold H3TerminalNativeLogDirectionalEscape at hDirectional

      refine
        tendsto_atTop.2
          ?_

      intro M

      have hEventually :
          ∀ᶠ n : ℕ in atTop,
            PrimeTensor.Bridge.MulReal.logValue
                (Ω n)
              ≤
            -M :=
        (tendsto_atBot.1 hDirectional)
          (-M)

      filter_upwards
        [hEventually]
        with n hn

      simpa only [
        h3TerminalOrientedValue_negative
      ] using
        (show
          M
            ≤
          -
            PrimeTensor.Bridge.MulReal.logValue
              (Ω n)
        by
          linarith)

/-! ## The correctly signed curl has the selected-gradient orientation -/

/--
In a cancellation-compatible sign regime, orienting the correctly signed curl
by the selected-gradient orientation is exactly the same as orienting the raw
curl logarithm by its own fixed curl orientation.
-/
theorem oriented_selectedSignedNativeCurlLog_eq_oriented_nativeCurlLog_of_cancellation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation)
    (hCancellation :
      H3TerminalComplementCancellationRegime
        p sCurl sGradient)
    (t : ℝ)
    (x : Point3) :
    h3TerminalOrientedValue
        sGradient
        (
          h3TerminalSelectedSignedNativeCurlLog
            u p t x
        )
      =
    h3TerminalOrientedValue
        sCurl
        (
          PrimeTensor.Bridge.MulReal.logValue
            (
              h3TerminalNativeCurlForPair
                u p t x
            )
        ) := by

  cases p <;>
    cases sCurl <;>
    cases sGradient <;>
    simp [
      H3TerminalComplementCancellationRegime,
      H3TerminalComplementForcedRegime,
      h3TerminalSelectedCurlSignForPair,
      h3TerminalSelectedSignedNativeCurlLog,
      h3TerminalOrientedValue
    ] at hCancellation ⊢

/--
Hence the correctly signed curl, viewed in the selected-gradient orientation,
tends to `+∞` along the synchronized sequence.
-/
theorem oriented_selectedSignedNativeCurlLog_tendsto_atTop_of_cancellation
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
        sCurl) :
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
      atTop := by

  have hCurlOriented :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalOrientedValue
              sCurl
              (
                PrimeTensor.Bridge.MulReal.logValue
                  (
                    h3TerminalNativeCurlForPair
                      u p
                      (τ n)
                      (x n)
                  )
              )
        )
        atTop
        atTop :=
    orientedLog_tendsto_atTop_of_nativeDirectionalEscape
      hCurlDirectional

  have hEq :
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
        =
      (
        fun n : ℕ =>
          h3TerminalOrientedValue
            sCurl
            (
              PrimeTensor.Bridge.MulReal.logValue
                (
                  h3TerminalNativeCurlForPair
                    u p
                    (τ n)
                    (x n)
                )
            )
      ) := by

    funext n

    exact
      oriented_selectedSignedNativeCurlLog_eq_oriented_nativeCurlLog_of_cancellation
        u p
        sCurl sGradient
        hCancellation
        (τ n)
        (x n)

  rw [hEq]

  exact hCurlOriented

/-! ## Orientation preserves the absolute additive defect -/

theorem abs_oriented_sub_oriented_eq_abs_sub
    (s : H3TerminalOrientation)
    (a b : ℝ) :
    abs
        (
          h3TerminalOrientedValue s a
            -
          h3TerminalOrientedValue s b
        )
      =
    abs (a - b) := by

  cases s with

  | positive =>

      simp only [
        h3TerminalOrientedValue_positive
      ]

  | negative =>

      simp only [
        h3TerminalOrientedValue_negative
      ]

      rw [
        show -a - -b = -(a - b) by ring,
        abs_neg
      ]

/-! ## Generic bounded-difference ratio lemma -/

/--
If `Bₙ → +∞` and `|Aₙ - Bₙ|` is eventually bounded by one constant, then
`Aₙ / Bₙ → 1`.
-/
private theorem ratio_tendsto_one_of_bounded_difference_atTop
    {A B : ℕ → ℝ}
    (hBTendsto :
      Tendsto B atTop atTop)
    {N : ℕ}
    {C : ℝ}
    (hBound :
      ∀ n : ℕ,
        N ≤ n →
        abs (A n - B n) ≤ C) :
    Tendsto
      (fun n : ℕ => A n / B n)
      atTop
      (𝓝 1) := by

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

  rw [Real.dist_eq]

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

  have hBNe :
      B n ≠ 0 :=
    ne_of_gt hBPos

  have hBound₀ :
      abs (A n - B n)
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

  calc
    abs (A n / B n - 1)
        =
      abs ((A n - B n) / B n) := by

        congr 1

        field_simp [hBNe]

    _ =
      abs (A n - B n) / abs (B n) := by

        rw [abs_div]

    _ =
      abs (A n - B n) / B n := by

        rw [abs_of_pos hBPos]

    _ ≤
      C₀ / B n := by

        exact
          (
            div_le_div_iff_of_pos_right
              hBPos
          ).2
            hBound₀

    _ < ε :=
      hRatio

/-! ## Ratio-one matching for the bounded cancellation branch -/

/--
In a cancellation-compatible regime, an eventual bound on the additive defect

    |gradient log - signed curl log| ≤ C

forces the ratio of the two correctly oriented diverging terms to tend to one.
-/
theorem cancellationMatchedRatio_tendsto_one
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
    (hDefect :
      ∀ n : ℕ,
        N ≤ n →
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
          ≤ C) :
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
      (𝓝 1) := by

  let A : ℕ → ℝ :=
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

  let B : ℕ → ℝ :=
    fun n : ℕ =>
      h3TerminalOrientedValue
        sGradient
        (
          h3TerminalSelectedSignedNativeCurlLog
            u p
            (τ n)
            (x n)
        )

  have hBTendsto :
      Tendsto B atTop atTop := by

    dsimp only [B]

    exact
      oriented_selectedSignedNativeCurlLog_tendsto_atTop_of_cancellation
        hCancellation
        hCurlDirectional

  have hOrientedBound :
      ∀ n : ℕ,
        N ≤ n →
        abs (A n - B n) ≤ C := by

    intro n hn

    dsimp only [A, B]

    rw [
      abs_oriented_sub_oriented_eq_abs_sub
    ]

    exact
      hDefect n hn

  exact
    ratio_tendsto_one_of_bounded_difference_atTop
      hBTendsto
      hOrientedBound

/-! ## Stronger cancellation refinement package -/

def H3TerminalNativeComplementCancellationRatioRefinement
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation) : Prop :=
  ∃
    τ : ℕ → ℝ,
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
      H3TerminalComplementCancellationRegime
        p sCurl sGradient
        ∧
      (
        (
          ∃ sComplement : H3TerminalOrientation,
            H3TerminalScalarSeqOrientedTailCofinallyUnbounded
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
              sComplement
        )
          ∨
        (
          ∃ N : ℕ,
            ∃ C : ℝ,
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
        )
      )

/--
Upgrade the previous cancellation refinement: in its eventually bounded branch,
the correctly oriented selected-gradient / signed-curl ratio tends to one.
-/
theorem nativeComplementCancellationRatioRefinement_of_refinement
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hRefinement :
      H3TerminalNativeComplementCancellationRefinement
        u a T p sCurl sGradient) :
    H3TerminalNativeComplementCancellationRatioRefinement
      u a T p sCurl sGradient := by

  obtain
    ⟨
      τ,
      x,
      hτ,
      hTauTendsto,
      hCurlDirectional,
      hGradientDirectional,
      hCancellation,
      hAlternative
    ⟩ :=
    hRefinement

  rcases hAlternative with hUnbounded | hBounded

  · exact
      ⟨
        τ,
        x,
        hτ,
        hTauTendsto,
        hCurlDirectional,
        hGradientDirectional,
        hCancellation,
        Or.inl hUnbounded
      ⟩

  · obtain
      ⟨
        N,
        C,
        hBound
      ⟩ :=
      hBounded

    have hRatio :
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
          (𝓝 1) := by

      exact
        cancellationMatchedRatio_tendsto_one
          hCancellation
          hCurlDirectional
          (N := N)
          (C := C)
          (fun n hn =>
            (hBound n hn).2)

    exact
      ⟨
        τ,
        x,
        hτ,
        hTauTendsto,
        hCurlDirectional,
        hGradientDirectional,
        hCancellation,
        Or.inr
          ⟨
            N,
            C,
            hBound,
            hRatio
          ⟩
      ⟩

/-! ## Exhaustive ratio-refined terminal alternative -/

/--
Under hypothetical nonextension, the complementary-gradient structure has the
following exhaustive form.

* Reinforcing signs force the complementary native derivative to escape on the
  same sequence with the existing quantitative `2n` lower bound.

* Cancellation-compatible signs split into:
  - tail-cofinal one-sided complementary unboundedness, or
  - eventual bounded complementary logarithm, in which case the correctly
    oriented selected-gradient / signed-curl ratio tends to `1`.
-/
theorem fixed_nativeComplementGradient_ratioRefinedAlternative_of_noH3PathExtension
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
            H3TerminalComplementCancellationRegime
              p sCurl sGradient
              ∧
            H3TerminalNativeComplementCancellationRatioRefinement
              u a T p sCurl sGradient
          )
        ) := by

  obtain
    ⟨
      p,
      sCurl,
      sGradient,
      hAlternative
    ⟩ :=
    fixed_nativeComplementGradient_refinedAlternative_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  rcases hAlternative with hForced | hCancellation

  · exact
      ⟨
        p,
        sCurl,
        sGradient,
        Or.inl hForced
      ⟩

  · exact
      ⟨
        p,
        sCurl,
        sGradient,
        Or.inr
          ⟨
            hCancellation.1,
            nativeComplementCancellationRatioRefinement_of_refinement
              hCancellation.2
          ⟩
      ⟩

/-! ## Neutral package -/

/--
Neutral continuation alternative with ratio-one asymptotic matching in the
eventually bounded cancellation branch.
-/
theorem smoothContinuationExtension_or_fixed_nativeComplementGradient_ratioRefinedAlternative
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
              H3TerminalComplementCancellationRegime
                p sCurl sGradient
                ∧
              H3TerminalNativeComplementCancellationRatioRefinement
                u a T p sCurl sGradient
            )
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
          fixed_nativeComplementGradient_ratioRefinedAlternative_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
