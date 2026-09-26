import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.ComplementaryGradientCancellationRatio

/-!
# Synchronized complementary-gradient subsequence in the unbounded cancellation branch

The ratio-refined complementary-gradient alternative leaves two genuinely
different possibilities inside the cancellation-compatible sign regime.

* If the complementary logarithm is eventually bounded, the correctly oriented
  selected-gradient / signed-curl ratio tends to `1`.

* If one complementary orientation is tail-cofinally unbounded, this file
  extracts an actual terminal subsequence on which the curl, selected gradient,
  and complementary gradient all escape one-sidedly together.

The subsequence index `kₙ` is chosen with `n ≤ kₙ` and complementary oriented
logarithm larger than `n`.  Since `kₙ → ∞`, the already-established curl and
selected-gradient directional limits survive composition.  The inequality
`n ≤ kₙ` also preserves both their quantitative lower bounds and the terminal
localization

    T - 1/(n+1) < τ(kₙ) < T.

Thus the cancellation-compatible branch becomes a sharp alternative:

* three synchronized one-sided native escapes on a common subsequence; or
* bounded complementary logarithm with ratio-one asymptotic cancellation.

All terminal statements remain necessary consequences conditional on
hypothetical failure of smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Directional escape is preserved by an index map tending to infinity -/

theorem nativeLogDirectionalEscape_comp_atTop
    {Ω : ℕ → PrimeTensor.MulReal}
    {s : H3TerminalOrientation}
    {k : ℕ → ℕ}
    (hEscape :
      H3TerminalNativeLogDirectionalEscape
        Ω s)
    (hk :
      Tendsto k atTop atTop) :
    H3TerminalNativeLogDirectionalEscape
      (fun n : ℕ => Ω (k n))
      s := by

  cases s with

  | positive =>

      unfold H3TerminalNativeLogDirectionalEscape at hEscape ⊢

      exact
        hEscape.comp hk

  | negative =>

      unfold H3TerminalNativeLogDirectionalEscape at hEscape ⊢

      exact
        hEscape.comp hk

/-! ## Three-way synchronized native escape -/

def H3TerminalNativeCurlGradientComplementTripleEscape
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient sComplement : H3TerminalOrientation) : Prop :=
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
            ∧
          (n : ℝ)
            <
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
            ∧
          (n : ℝ)
            <
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
            ∧
          (n : ℝ)
            <
          h3TerminalOrientedValue
            sComplement
            (
              PrimeTensor.Bridge.MulReal.logValue
                (
                  h3TerminalNativeComplementGradientForPair
                    u p
                    (τ n)
                    (x n)
                )
            )
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
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeComplementGradientForPair
              u p
              (τ n)
              (x n)
        )
        sComplement

private theorem tendsto_atTop_of_nat_le_index
    {k : ℕ → ℕ}
    (hk :
      ∀ n : ℕ,
        n ≤ k n) :
    Tendsto k atTop atTop := by

  refine
    tendsto_atTop.2
      ?_

  intro N

  filter_upwards
    [eventually_ge_atTop N]
    with n hn

  exact
    le_trans
      hn
      (hk n)

private theorem tendsto_atTop_of_natCast_lt_complement
    {f : ℕ → ℝ}
    (hf :
      ∀ n : ℕ,
        (n : ℝ) < f n) :
    Tendsto f atTop atTop := by

  refine
    tendsto_atTop.2
      ?_

  intro M

  obtain
    ⟨N : ℕ, hN⟩ :=
    exists_nat_gt M

  filter_upwards
    [eventually_ge_atTop N]
    with n hn

  have hCast :
      (N : ℝ) ≤ n := by
    exact_mod_cast hn

  exact
    le_of_lt
      (
        lt_trans
          (lt_of_lt_of_le hN hCast)
          (hf n)
      )

/--
Extract a synchronized terminal subsequence from a complementary orientation
that is tail-cofinally unbounded along the original double-directional
sequence.
-/
theorem nativeCurlGradientComplementTripleEscape_of_tailCofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T
          ∧
        τ n ∈
          Set.Ioo
            (T - (1 : ℝ) / ((n : ℝ) + 1))
            T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
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
    (hComplementCofinal :
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
        sComplement) :
    H3TerminalNativeCurlGradientComplementTripleEscape
      u a T p sCurl sGradient sComplement := by

  have hCurlOrientedTendsto :
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

  have hGradientOrientedTendsto :
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

  have hChoice :
      ∀ n : ℕ,
        ∃ m : ℕ,
          n ≤ m
            ∧
          (n : ℝ)
            <
          h3TerminalOrientedValue
            sCurl
            (
              PrimeTensor.Bridge.MulReal.logValue
                (
                  h3TerminalNativeCurlForPair
                    u p
                    (τ m)
                    (x m)
                )
            )
            ∧
          (n : ℝ)
            <
          h3TerminalOrientedValue
            sGradient
            (
              PrimeTensor.Bridge.MulReal.logValue
                (
                  h3TerminalNativeGradientForPair
                    u p
                    (τ m)
                    (x m)
                )
            )
            ∧
          (n : ℝ)
            <
          h3TerminalOrientedValue
            sComplement
            (
              PrimeTensor.Bridge.MulReal.logValue
                (
                  h3TerminalNativeComplementGradientForPair
                    u p
                    (τ m)
                    (x m)
                )
            ) := by

    intro n

    have hCurlEventually :
        ∀ᶠ m : ℕ in atTop,
          (n : ℝ) + 1
            ≤
          h3TerminalOrientedValue
            sCurl
            (
              PrimeTensor.Bridge.MulReal.logValue
                (
                  h3TerminalNativeCurlForPair
                    u p
                    (τ m)
                    (x m)
                )
            ) :=
      (tendsto_atTop.1 hCurlOrientedTendsto)
        ((n : ℝ) + 1)

    have hGradientEventually :
        ∀ᶠ m : ℕ in atTop,
          (n : ℝ) + 1
            ≤
          h3TerminalOrientedValue
            sGradient
            (
              PrimeTensor.Bridge.MulReal.logValue
                (
                  h3TerminalNativeGradientForPair
                    u p
                    (τ m)
                    (x m)
                )
            ) :=
      (tendsto_atTop.1 hGradientOrientedTendsto)
        ((n : ℝ) + 1)

    obtain
      ⟨
        Ncurl,
        hNcurl
      ⟩ :=
      eventually_atTop.1
        hCurlEventually

    obtain
      ⟨
        Ngradient,
        hNgradient
      ⟩ :=
      eventually_atTop.1
        hGradientEventually

    let N : ℕ :=
      max n
        (max Ncurl Ngradient)

    obtain
      ⟨
        m,
        hmN,
        hComplement
      ⟩ :=
      hComplementCofinal
        N
        (n : ℝ)

    have hmn :
        n ≤ m := by

      exact
        le_trans
          (le_max_left n (max Ncurl Ngradient))
          hmN

    have hmCurl :
        Ncurl ≤ m := by

      exact
        le_trans
          (
            le_trans
              (le_max_left Ncurl Ngradient)
              (le_max_right n (max Ncurl Ngradient))
          )
          hmN

    have hmGradient :
        Ngradient ≤ m := by

      exact
        le_trans
          (
            le_trans
              (le_max_right Ncurl Ngradient)
              (le_max_right n (max Ncurl Ngradient))
          )
          hmN

    have hCurlLarge :
        (n : ℝ)
          <
        h3TerminalOrientedValue
          sCurl
          (
            PrimeTensor.Bridge.MulReal.logValue
              (
                h3TerminalNativeCurlForPair
                  u p
                  (τ m)
                  (x m)
              )
          ) := by

      have hAt :=
        hNcurl m hmCurl

      linarith

    have hGradientLarge :
        (n : ℝ)
          <
        h3TerminalOrientedValue
          sGradient
          (
            PrimeTensor.Bridge.MulReal.logValue
              (
                h3TerminalNativeGradientForPair
                  u p
                  (τ m)
                  (x m)
              )
          ) := by

      have hAt :=
        hNgradient m hmGradient

      linarith

    exact
      ⟨
        m,
        hmn,
        hCurlLarge,
        hGradientLarge,
        hComplement
      ⟩

  choose k hk using hChoice

  have hkTendsto :
      Tendsto k atTop atTop :=
    tendsto_atTop_of_nat_le_index
      (fun n => (hk n).1)

  have hSubTauTendsto :
      Tendsto
        (fun n : ℕ => τ (k n))
        atTop
        (𝓝 T) :=
    hTauTendsto.comp
      hkTendsto

  have hSubCurlDirectional :
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeCurlForPair
              u p
              (τ (k n))
              (x (k n))
        )
        sCurl := by

    exact
      nativeLogDirectionalEscape_comp_atTop
        hCurlDirectional
        hkTendsto

  have hSubGradientDirectional :
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeGradientForPair
              u p
              (τ (k n))
              (x (k n))
        )
        sGradient := by

    exact
      nativeLogDirectionalEscape_comp_atTop
        hGradientDirectional
        hkTendsto

  have hComplementOrientedTendsto :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalOrientedValue
              sComplement
              (
                PrimeTensor.Bridge.MulReal.logValue
                  (
                    h3TerminalNativeComplementGradientForPair
                      u p
                      (τ (k n))
                      (x (k n))
                  )
              )
        )
        atTop
        atTop :=
    tendsto_atTop_of_natCast_lt_complement
      (fun n => (hk n).2.2.2)

  have hSubComplementDirectional :
      H3TerminalNativeLogDirectionalEscape
        (
          fun n : ℕ =>
            h3TerminalNativeComplementGradientForPair
              u p
              (τ (k n))
              (x (k n))
        )
        sComplement := by

    exact
      nativeLogDirectionalEscape_of_oriented_log_bridge
        (Ω :=
          fun n : ℕ =>
            h3TerminalNativeComplementGradientForPair
              u p
              (τ (k n))
              (x (k n)))
        (H :=
          fun n : ℕ =>
            PrimeTensor.Bridge.MulReal.logValue
              (
                h3TerminalNativeComplementGradientForPair
                  u p
                  (τ (k n))
                  (x (k n))
              ))
        (s := sComplement)
        (fun n => rfl)
        hComplementOrientedTendsto

  refine
    ⟨
      (fun n : ℕ => τ (k n)),
      (fun n : ℕ => x (k n)),
      ?_,
      hSubTauTendsto,
      hCancellation,
      hSubCurlDirectional,
      hSubGradientDirectional,
      hSubComplementDirectional
    ⟩

  intro n

  have hOrig :=
    hτ (k n)

  have hDenPos :
      0 < (n : ℝ) + 1 := by
    positivity

  have hDenLe :
      (n : ℝ) + 1
        ≤
      (k n : ℝ) + 1 := by

    have hCast :
        (n : ℝ) ≤ (k n : ℝ) := by
      exact_mod_cast (hk n).1

    linarith

  have hInv :
      (1 : ℝ) / ((k n : ℝ) + 1)
        ≤
      1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le
      hDenPos
      hDenLe

  have hLocalized :
      τ (k n) ∈
        Set.Ioo
          (T - (1 : ℝ) / ((n : ℝ) + 1))
          T := by

    exact
      ⟨
        lt_of_le_of_lt
          (by linarith [hInv])
          hOrig.2.1,
        hOrig.2.2
      ⟩

  exact
    ⟨
      hOrig.1,
      hLocalized,
      (hk n).2.1,
      (hk n).2.2.1,
      (hk n).2.2.2
    ⟩

/-! ## The bounded ratio-one branch as a standalone package -/

def H3TerminalNativeComplementBoundedRatioMatching
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

/-! ## Resolve the cancellation-compatible ratio refinement -/

/--
The ratio-refined cancellation branch resolves into exactly one of:

* a three-way synchronized native escape on a terminal subsequence; or
* eventual bounded complementary logarithm with ratio-one dominant-term
  matching.
-/
theorem nativeComplementCancellation_resolved_of_ratioRefinement
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hRefinement :
      H3TerminalNativeComplementCancellationRatioRefinement
        u a T p sCurl sGradient) :
    (
      ∃ sComplement : H3TerminalOrientation,
        H3TerminalNativeCurlGradientComplementTripleEscape
          u a T p sCurl sGradient sComplement
    )
      ∨
    H3TerminalNativeComplementBoundedRatioMatching
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

  · obtain
      ⟨
        sComplement,
        hComplementCofinal
      ⟩ :=
      hUnbounded

    exact
      Or.inl
        ⟨
          sComplement,
          nativeCurlGradientComplementTripleEscape_of_tailCofinallyUnbounded
            hτ
            hTauTendsto
            hCancellation
            hCurlDirectional
            hGradientDirectional
            hComplementCofinal
        ⟩

  · obtain
      ⟨
        N,
        C,
        hBound,
        hRatio
      ⟩ :=
      hBounded

    exact
      Or.inr
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
        ⟩

/-! ## Exhaustive three-branch terminal structure -/

/--
Under hypothetical nonextension, one fixed structural curl pair and fixed curl
/ selected-gradient orientations satisfy one of three exhaustive alternatives.

1. Reinforcing signs force the complementary native derivative to escape on
   the original sequence with the quantitative `2n` lower bound.

2. Cancellation-compatible signs with an unbounded complement admit a
   subsequence on which the native curl, selected gradient, and complementary
   gradient all have fixed one-sided logarithmic escape, each with lower bound
   larger than `n`.

3. Cancellation-compatible signs with a bounded complement have bounded
   additive cancellation defect and ratio-one matching of the two dominant
   oriented logarithms.
-/
theorem fixed_nativeComplementGradient_threeBranchAlternative_of_noH3PathExtension
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
            ∃ sComplement : H3TerminalOrientation,
              H3TerminalNativeCurlGradientComplementTripleEscape
                u a T p sCurl sGradient sComplement
          )
            ∨
          H3TerminalNativeComplementBoundedRatioMatching
            u a T p sCurl sGradient
        ) := by

  obtain
    ⟨
      p,
      sCurl,
      sGradient,
      hAlternative
    ⟩ :=
    fixed_nativeComplementGradient_ratioRefinedAlternative_of_noH3PathExtension
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

  · rcases
      nativeComplementCancellation_resolved_of_ratioRefinement
        hCancellation.2
    with hTriple | hBounded

    · exact
        ⟨
          p,
          sCurl,
          sGradient,
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
          Or.inr
            (
              Or.inr hBounded
            )
        ⟩

/-! ## Neutral package -/

/--
Neutral continuation alternative exposing the complete fixed-pair terminal
three-branch structure.
-/
theorem smoothContinuationExtension_or_fixed_nativeComplementGradient_threeBranchAlternative
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
              ∃ sComplement : H3TerminalOrientation,
                H3TerminalNativeCurlGradientComplementTripleEscape
                  u a T p sCurl sGradient sComplement
            )
              ∨
            H3TerminalNativeComplementBoundedRatioMatching
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
          fixed_nativeComplementGradient_threeBranchAlternative_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
