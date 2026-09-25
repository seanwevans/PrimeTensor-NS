import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.ComplementaryGradientDichotomy

/-!
# Refining the cancellation-compatible complementary-gradient regime

The complementary-gradient dichotomy leaves one deliberately neutral branch:
the fixed curl and selected constituent gradient have orientations for which
their exact difference can cancel.

This file refines that branch without assuming cancellation actually occurs.

Along the already-selected terminal sequence, the complementary derivative
has an exhaustive alternative:

1. its logarithmic magnitude is cofinally unbounded arbitrarily far out in the
   sequence; then one fixed sign of the complementary derivative is itself
   cofinally unbounded;

2. its logarithmic magnitude is eventually bounded; then the exact curl
   identity gives a uniformly bounded cancellation defect between the selected
   gradient logarithm and the correctly signed curl logarithm.

The second branch is a precise bounded-error matching statement.  No ratio
limit is asserted here; that can be derived separately if desired.

All terminal statements remain necessary consequences conditional on
hypothetical failure of smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Generic tail alternatives for real sequences -/

def H3TerminalScalarSeqAbsTailCofinallyUnbounded
    (f : ℕ → ℝ) : Prop :=
  ∀ N : ℕ,
    ∀ M : ℝ,
      ∃ n : ℕ,
        N ≤ n
          ∧
        M < abs (f n)

def H3TerminalScalarSeqOrientedTailCofinallyUnbounded
    (f : ℕ → ℝ)
    (s : H3TerminalOrientation) : Prop :=
  ∀ N : ℕ,
    ∀ M : ℝ,
      ∃ n : ℕ,
        N ≤ n
          ∧
        M <
          h3TerminalOrientedValue
            s
            (f n)

def H3TerminalScalarSeqEventuallyAbsBounded
    (f : ℕ → ℝ) : Prop :=
  ∃ N : ℕ,
    ∃ B : ℝ,
      ∀ n : ℕ,
        N ≤ n →
        abs (f n) ≤ B

/--
Every real sequence is either tail-cofinally unbounded in magnitude or
eventually bounded in magnitude.
-/
theorem scalarSeq_absTailCofinallyUnbounded_or_eventuallyAbsBounded
    (f : ℕ → ℝ) :
    H3TerminalScalarSeqAbsTailCofinallyUnbounded f
      ∨
    H3TerminalScalarSeqEventuallyAbsBounded f := by

  classical

  by_cases hUnbounded :
      H3TerminalScalarSeqAbsTailCofinallyUnbounded f

  · exact
      Or.inl hUnbounded

  · right

    have hBound := hUnbounded

    unfold H3TerminalScalarSeqAbsTailCofinallyUnbounded at hBound

    push Not at hBound

    obtain
      ⟨
        N,
        B,
        hB
      ⟩ :=
      hBound

    exact
      ⟨
        N,
        B,
        hB
      ⟩

/--
If the magnitude of a real sequence is cofinally unbounded on every tail,
then one fixed orientation is cofinally unbounded on every tail.
-/
theorem exists_orientation_of_scalarSeq_absTailCofinallyUnbounded
    {f : ℕ → ℝ}
    (hAbs :
      H3TerminalScalarSeqAbsTailCofinallyUnbounded f) :
    ∃ s : H3TerminalOrientation,
      H3TerminalScalarSeqOrientedTailCofinallyUnbounded
        f s := by

  classical

  by_cases hPos :
      H3TerminalScalarSeqOrientedTailCofinallyUnbounded
        f
        H3TerminalOrientation.positive

  · exact
      ⟨
        H3TerminalOrientation.positive,
        hPos
      ⟩

  have hPosBound := hPos

  unfold H3TerminalScalarSeqOrientedTailCofinallyUnbounded at hPosBound

  push Not at hPosBound

  obtain
    ⟨
      N₀,
      M₀,
      hFailPos
    ⟩ :=
    hPosBound

  refine
    ⟨
      H3TerminalOrientation.negative,
      ?_
    ⟩

  unfold H3TerminalScalarSeqOrientedTailCofinallyUnbounded

  intro N M

  let K : ℝ :=
    max
      (max M M₀)
      0

  obtain
    ⟨
      n,
      hn,
      hAbsLarge
    ⟩ :=
    hAbs
      (max N N₀)
      K

  have hnN :
      N ≤ n :=
    le_trans
      (le_max_left N N₀)
      hn

  have hnN₀ :
      N₀ ≤ n :=
    le_trans
      (le_max_right N N₀)
      hn

  have hMleK :
      M ≤ K := by

    dsimp only [K]

    exact
      le_trans
        (le_max_left M M₀)
        (le_max_left _ _)

  have hM₀leK :
      M₀ ≤ K := by

    dsimp only [K]

    exact
      le_trans
        (le_max_right M M₀)
        (le_max_left _ _)

  have hFle :
      f n ≤ M₀ := by

    have hAt :=
      hFailPos n hnN₀

    simpa only [
      h3TerminalOrientedValue_positive
    ] using hAt

  have hFneg :
      f n < 0 := by

    by_contra hNotNeg

    have hFnonneg :
        0 ≤ f n :=
      le_of_not_gt hNotNeg

    have hAbsEq :
        abs (f n) = f n :=
      abs_of_nonneg hFnonneg

    have hAbsLe :
        abs (f n) ≤ K := by

      rw [hAbsEq]

      exact
        le_trans
          hFle
          hM₀leK

    exact
      (not_lt_of_ge hAbsLe)
        hAbsLarge

  have hNegLarge :
      K < - f n := by

    rw [abs_of_neg hFneg] at hAbsLarge

    exact hAbsLarge

  refine
    ⟨
      n,
      hnN,
      ?_
    ⟩

  simpa only [
    h3TerminalOrientedValue_negative
  ] using
    (
      lt_of_le_of_lt
        hMleK
        hNegLarge
    )

/-! ## Exact native cancellation defect -/

noncomputable def h3TerminalSelectedSignedNativeCurlLog
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (x : Point3) : ℝ :=
  h3TerminalOrientedValue
    (h3TerminalSelectedCurlSignForPair p)
    (
      PrimeTensor.Bridge.MulReal.logValue
        (
          h3TerminalNativeCurlForPair
            u p t x
        )
    )

/--
The complementary native gradient logarithm is exactly the selected native
gradient logarithm minus the correctly signed native curl logarithm.
-/
theorem logValue_nativeComplement_eq_gradient_sub_signedCurl
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (
          h3TerminalNativeComplementGradientForPair
            u p t x
        )
      =
    PrimeTensor.Bridge.MulReal.logValue
        (
          h3TerminalNativeGradientForPair
            u p t x
        )
      -
    h3TerminalSelectedSignedNativeCurlLog
      u p t x := by

  rw [
    logValue_h3TerminalNativeComplementGradientForPair,
    h3TerminalComplementGradientFieldForPair_eq,
    logValue_h3TerminalNativeGradientForPair
  ]

  unfold h3TerminalSelectedSignedNativeCurlLog

  rw [
    logValue_h3TerminalNativeCurlForPair
  ]

/-! ## Cancellation-compatible sequence refinement -/

def H3TerminalNativeComplementCancellationRefinement
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
            ∃ B : ℝ,
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
                    ≤ B
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
                    ≤ B
                )
        )
      )

/--
Refine a cancellation-compatible fixed native curl/gradient sequence.

Either the complementary native derivative has one fixed orientation that is
cofinally unbounded arbitrarily far out in the sequence, or its logarithmic
magnitude is eventually bounded.  In the bounded branch the exact curl
identity gives the same eventual bound on the cancellation defect between the
selected gradient log and the signed curl log.
-/
theorem nativeComplementCancellationRefinement_of_doubleDirectionalEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hCancellation :
      H3TerminalComplementCancellationRegime
        p sCurl sGradient)
    (hDirectional :
      H3TerminalNativeCurlGradientDoubleDirectionalEscape
        u a T p sCurl sGradient) :
    H3TerminalNativeComplementCancellationRefinement
      u a T p sCurl sGradient := by

  obtain
    ⟨
      τ,
      x,
      hτ,
      hTauTendsto,
      hCurlDirectional,
      hGradientDirectional
    ⟩ :=
    hDirectional

  let f : ℕ → ℝ :=
    fun n : ℕ =>
      PrimeTensor.Bridge.MulReal.logValue
        (
          h3TerminalNativeComplementGradientForPair
            u p
            (τ n)
            (x n)
        )

  rcases
      scalarSeq_absTailCofinallyUnbounded_or_eventuallyAbsBounded
        f
    with hUnbounded | hBounded

  · obtain
      ⟨
        sComplement,
        hComplementOriented
      ⟩ :=
      exists_orientation_of_scalarSeq_absTailCofinallyUnbounded
        hUnbounded

    exact
      ⟨
        τ,
        x,
        (fun n =>
          ⟨
            (hτ n).1,
            (hτ n).2.1
          ⟩),
        hTauTendsto,
        hCurlDirectional,
        hGradientDirectional,
        hCancellation,
        Or.inl
          ⟨
            sComplement,
            hComplementOriented
          ⟩
      ⟩

  · obtain
      ⟨
        N,
        B,
        hBound
      ⟩ :=
      hBounded

    refine
      ⟨
        τ,
        x,
        (fun n =>
          ⟨
            (hτ n).1,
            (hτ n).2.1
          ⟩),
        hTauTendsto,
        hCurlDirectional,
        hGradientDirectional,
        hCancellation,
        Or.inr
          ⟨
            N,
            B,
            ?_
          ⟩
      ⟩

    intro n hn

    have hComplementBound :
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
          ≤ B := by

      exact
        hBound n hn

    refine
      ⟨
        hComplementBound,
        ?_
      ⟩

    rw [
      ←
      logValue_nativeComplement_eq_gradient_sub_signedCurl
        u p
        (τ n)
        (x n)
    ]

    exact
      hComplementBound

/-! ## Exhaustive refined terminal alternative -/

/--
Under hypothetical nonextension, the complementary-gradient alternative is
exhaustive at the next level.

* In a reinforcing sign regime, the complementary native derivative is forced
  to escape on the same sequence with the existing quantitative `2n` bound.

* In a cancellation-compatible sign regime, either one fixed complementary
  orientation is tail-cofinally unbounded on that sequence, or the
  complementary logarithm is eventually bounded and hence the two large
  cancelling logarithmic terms remain within a fixed bounded additive defect.
-/
theorem fixed_nativeComplementGradient_refinedAlternative_of_noH3PathExtension
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
            H3TerminalNativeComplementCancellationRefinement
              u a T p sCurl sGradient
          )
        ) := by

  obtain
    ⟨
      p,
      sCurl,
      sGradient,
      hDirectional
    ⟩ :=
    fixed_nativeCurlGradient_doubleDirectionalEscape_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  by_cases hForced :
      H3TerminalComplementForcedRegime
        p sCurl sGradient

  · exact
      ⟨
        p,
        sCurl,
        sGradient,
        Or.inl
          ⟨
            hForced,
            nativeComplementGradientForcedCascade_of_doubleDirectionalEscape
              hForced
              hDirectional
          ⟩
      ⟩

  · have hCancellation :
        H3TerminalComplementCancellationRegime
          p sCurl sGradient :=
      hForced

    exact
      ⟨
        p,
        sCurl,
        sGradient,
        Or.inr
          ⟨
            hCancellation,
            nativeComplementCancellationRefinement_of_doubleDirectionalEscape
              hCancellation
              hDirectional
          ⟩
      ⟩

/-! ## Neutral package -/

/--
Neutral continuation alternative with the cancellation-compatible branch
refined into complementary tail-unboundedness versus bounded additive
cancellation defect.
-/
theorem smoothContinuationExtension_or_fixed_nativeComplementGradient_refinedAlternative
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
              H3TerminalNativeComplementCancellationRefinement
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
          fixed_nativeComplementGradient_refinedAlternative_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
