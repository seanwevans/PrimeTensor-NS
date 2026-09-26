import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.ComplementaryGradientResidualNegligible
import PrimeTensor.Bridge.Log.Surjective
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Finite native cluster state for the bounded complementary residual

The bounded cancellation branch now has the exact native residual identity

    complement = ratio selected signedCurl,

together with

* bounded complementary logarithm;
* ratio-one matching of the two dominant oriented logarithms;
* complementary logarithm negligible relative to both dominant scales.

An eventually bounded real sequence has a convergent subsequence.  Applying
Bolzano--Weierstrass to the residual logarithm therefore yields a subsequence
and a finite real limit `r`.

Surjectivity of the completed logarithmic coordinate then supplies a native
state `q : MulReal` with

    logValue q = r.

Hence, in the bounded cancellation branch, the exact native multiplicative
residual has a finite native cluster state while the curl and selected-gradient
scales continue to escape and asymptotically match.

This is deliberately neutral.  It does not assert convergence of the full
residual sequence, uniqueness of the cluster state, or exclusion of the other
two terminal branches.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Small subsequence utilities -/

private theorem nat_le_of_strictMono
    {k : ℕ → ℕ}
    (hk : StrictMono k) :
    ∀ n : ℕ,
      n ≤ k n := by

  intro n

  induction n with

  | zero =>
      exact Nat.zero_le _

  | succ n ih =>

      have hstep :
          k n < k (n + 1) :=
        hk
          (Nat.lt_succ_self n)

      omega

private theorem tendsto_atTop_of_nat_le
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

/-! ## Bounded residual cluster package -/

def H3TerminalNativeComplementFiniteClusterMatching
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

/-! ## Extract the finite residual cluster -/

/--
Every bounded-relative-negligible cancellation branch admits a terminal
subsequence on which the exact native residual logarithm converges to the
logarithm of one finite native `MulReal` state.
-/
theorem nativeComplementFiniteClusterMatching_of_boundedRelativeNegligible
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hBounded :
      H3TerminalNativeComplementBoundedRelativeNegligible
        u a T p sCurl sGradient) :
    H3TerminalNativeComplementFiniteClusterMatching
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

  let R : ℕ → ℝ :=
    fun n : ℕ =>
      PrimeTensor.Bridge.MulReal.logValue
        (
          h3TerminalNativeComplementGradientForPair
            u p
            (τ n)
            (x n)
        )

  let C₀ : ℝ :=
    max C 0

  let Rtail : ℕ → ℝ :=
    fun n : ℕ =>
      R (n + N)

  have hTailMem :
      ∀ n : ℕ,
        Rtail n ∈
          Set.Icc (-C₀) C₀ := by

    intro n

    have hIndex :
        N ≤ n + N := by
      omega

    have hAbs :
        abs (Rtail n) ≤ C := by

      dsimp only [Rtail, R]

      exact
        (hBound (n + N) hIndex).1

    have hAbs₀ :
        abs (Rtail n) ≤ C₀ := by

      exact
        le_trans
          hAbs
          (le_max_left C 0)

    exact
      (abs_le.mp hAbs₀)

  obtain
    ⟨
      r,
      hr,
      φ,
      hφStrict,
      hRSub
    ⟩ :=
    tendsto_subseq_of_bounded
      (Metric.isBounded_Icc (-C₀) C₀)
      hTailMem

  let k : ℕ → ℕ :=
    fun n : ℕ =>
      φ n + N

  have hkStrict :
      StrictMono k := by

    intro m n hmn

    dsimp only [k]

    have hφ :
        φ m < φ n :=
      hφStrict hmn

    omega

  have hkLe :
      ∀ n : ℕ,
        n ≤ k n :=
    nat_le_of_strictMono
      hkStrict

  have hkTendsto :
      Tendsto k atTop atTop :=
    tendsto_atTop_of_nat_le
      hkLe

  have hResidualTendstoReal :
      Tendsto
        (
          fun n : ℕ =>
            PrimeTensor.Bridge.MulReal.logValue
              (
                h3TerminalNativeComplementGradientForPair
                  u p
                  (τ (k n))
                  (x (k n))
              )
        )
        atTop
        (𝓝 r) := by

    simpa [
      Function.comp_def,
      Rtail,
      R,
      k
    ] using hRSub

  obtain
    ⟨
      q,
      hq
    ⟩ :=
    PrimeTensor.Bridge.MulReal.logValue_surjective
      r

  have hResidualTendstoNative :
      Tendsto
        (
          fun n : ℕ =>
            PrimeTensor.Bridge.MulReal.logValue
              (
                h3TerminalNativeComplementGradientForPair
                  u p
                  (τ (k n))
                  (x (k n))
              )
        )
        atTop
        (
          𝓝
            (
              PrimeTensor.Bridge.MulReal.logValue q
            )
        ) := by

    rw [hq]

    exact hResidualTendstoReal

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
        sCurl :=
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
        sGradient :=
    nativeLogDirectionalEscape_comp_atTop
      hGradientDirectional
      hkTendsto

  have hSubRatio :
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
                        (τ (k n))
                        (x (k n))
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
                    (τ (k n))
                    (x (k n))
                )
            )
        )
        atTop
        (𝓝 1) :=
    hRatio.comp
      hkTendsto

  have hSubRelativeCurl :
      Tendsto
        (
          fun n : ℕ =>
            abs
              (
                PrimeTensor.Bridge.MulReal.logValue
                  (
                    h3TerminalNativeComplementGradientForPair
                      u p
                      (τ (k n))
                      (x (k n))
                  )
              )
              /
            h3TerminalOrientedValue
              sGradient
              (
                h3TerminalSelectedSignedNativeCurlLog
                  u p
                  (τ (k n))
                  (x (k n))
              )
        )
        atTop
        (𝓝 0) :=
    hRelativeCurl.comp
      hkTendsto

  have hSubRelativeGradient :
      Tendsto
        (
          fun n : ℕ =>
            abs
              (
                PrimeTensor.Bridge.MulReal.logValue
                  (
                    h3TerminalNativeComplementGradientForPair
                      u p
                      (τ (k n))
                      (x (k n))
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
                      (τ (k n))
                      (x (k n))
                  )
              )
        )
        atTop
        (𝓝 0) :=
    hRelativeGradient.comp
      hkTendsto

  refine
    ⟨
      (fun n : ℕ => τ (k n)),
      (fun n : ℕ => x (k n)),
      q,
      ?_,
      hSubTauTendsto,
      hCancellation,
      hSubCurlDirectional,
      hSubGradientDirectional,
      hResidualTendstoNative,
      hSubRatio,
      hSubRelativeCurl,
      hSubRelativeGradient
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
      exact_mod_cast
        (hkLe n)

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
      hLocalized
    ⟩

/-! ## Exhaustive terminal alternative with finite residual cluster -/

/--
Under hypothetical nonextension, one fixed structural pair satisfies one of:

1. reinforcing-sign complementary escape;
2. cancellation-compatible synchronized triple escape on a subsequence;
3. cancellation-compatible bounded residual with a finite native cluster state,
   while the dominant oriented logs retain ratio-one matching and the residual
   remains logarithmically negligible relative to both.

The exact native residual law holds pointwise in every branch.
-/
theorem fixed_nativeComplementGradient_threeBranchAlternative_withFiniteResidualCluster_of_noH3PathExtension
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
          H3TerminalNativeComplementFiniteClusterMatching
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
                  nativeComplementFiniteClusterMatching_of_boundedRelativeNegligible
                    hBounded
                )
            )
        ⟩

/-! ## Neutral package -/

/--
Neutral continuation alternative with exact native residual law and a finite
native residual cluster state in the bounded cancellation branch.
-/
theorem smoothContinuationExtension_or_fixed_nativeComplementGradient_threeBranchAlternative_withFiniteResidualCluster
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
            H3TerminalNativeComplementFiniteClusterMatching
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
          fixed_nativeComplementGradient_threeBranchAlternative_withFiniteResidualCluster_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
