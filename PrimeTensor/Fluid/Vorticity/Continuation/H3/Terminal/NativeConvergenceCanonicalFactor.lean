import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.ComplementaryGradientAsymptoticProportionality

/-!
# Terminal native convergence semantics and canonical residual factor

The terminal development introduced an `ℕ`-indexed intrinsic convergence notion

    H3TerminalNativeNatConvergesTo Ω q

meaning that at every native multiplicative scale, `Ω n` is eventually
`ScaleNear` `q`.

Only the easy direction had been used so far:

    logValue Ω n -> logValue q
      => intrinsic native convergence.

This file proves the converse.  Therefore, for terminal natural-number
sequences,

    intrinsic native convergence
      <-> ordinary convergence of canonical logarithmic coordinates.

As immediate consequences:

* intrinsic native limits are unique;
* the finite residual state `q` in the bounded cancellation branch is unique
  for the chosen terminal subsequence;
* hence `q` is a canonical native proportionality factor on that subsequence.

This does not assert that the full bounded residual sequence has a unique
cluster point.  Different extracted subsequences could still have different
finite cluster states unless a separate argument rules that out.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Exact semantics of terminal natural-number native convergence -/

/--
For `ℕ`-indexed terminal sequences, intrinsic convergence at every native
`ScaleNear` scale is exactly ordinary real convergence of the canonical
logarithmic coordinates.
-/
theorem terminalNativeNatConvergesTo_iff_logValue_tendsto
    (Ω : ℕ → MulReal)
    (q : MulReal) :
    H3TerminalNativeNatConvergesTo Ω q
      ↔
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
      ) := by

  constructor

  · intro hNative

    rw [Metric.tendsto_nhds]

    intro ε hε

    obtain
      ⟨
        level,
        hRadius
      ⟩ :=
      PrimeTensor.Bridge.exists_logScaleRadius_lt
        hε

    have hEventually :=
      hNative level

    filter_upwards
      [hEventually]
      with n hn

    rw [Real.dist_eq]

    exact
      lt_of_le_of_lt
        (
          PrimeTensor.Bridge.MulReal.scaleNear_logValue_le
            hn
        )
        hRadius

  · intro hLog

    exact
      terminalNativeNatConvergesTo_of_logValue_tendsto
        hLog

/--
Intrinsic native limits of an `ℕ`-indexed terminal sequence are unique.
-/
theorem terminalNativeNatConvergesTo_unique
    {Ω : ℕ → MulReal}
    {q₁ q₂ : MulReal}
    (h₁ :
      H3TerminalNativeNatConvergesTo
        Ω q₁)
    (h₂ :
      H3TerminalNativeNatConvergesTo
        Ω q₂) :
    q₁ = q₂ := by

  apply
    PrimeTensor.Bridge.MulReal.logValue_injective

  exact
    tendsto_nhds_unique
      (
        (
          terminalNativeNatConvergesTo_iff_logValue_tendsto
            Ω q₁
        ).1 h₁
      )
      (
        (
          terminalNativeNatConvergesTo_iff_logValue_tendsto
            Ω q₂
        ).1 h₂
      )

/-! ## Canonical native residual factor on a fixed terminal sequence -/

def H3TerminalNativeComplementProportionalityFactor
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (q : MulReal) : Prop :=
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

/--
For a fixed structural pair and fixed terminal spacetime sequence, the finite
native proportionality factor is unique whenever it exists.
-/
theorem nativeComplementProportionalityFactor_unique
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {q₁ q₂ : MulReal}
    (h₁ :
      H3TerminalNativeComplementProportionalityFactor
        u p τ x q₁)
    (h₂ :
      H3TerminalNativeComplementProportionalityFactor
        u p τ x q₂) :
    q₁ = q₂ := by

  exact
    terminalNativeNatConvergesTo_unique
      h₁ h₂

/-! ## Canonical-factor bounded cancellation package -/

def H3TerminalNativeComplementCanonicalProportionality
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
        H3TerminalNativeComplementProportionalityFactor
          u p τ x q
          ∧
        (
          ∀ q' : MulReal,
            H3TerminalNativeComplementProportionalityFactor
              u p τ x q' →
            q' = q
        )
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
Upgrade native asymptotic proportionality by recording that the finite native
factor is the unique intrinsic limit of the residual ratio on the chosen
terminal subsequence.
-/
theorem nativeComplementCanonicalProportionality_of_asymptoticProportionality
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    (hProportional :
      H3TerminalNativeComplementAsymptoticProportionality
        u a T p sCurl sGradient) :
    H3TerminalNativeComplementCanonicalProportionality
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
      hNormalized,
      hResidualLog,
      hRatio,
      hRelativeCurl,
      hRelativeGradient
    ⟩ :=
    hProportional

  have hFactor :
      H3TerminalNativeComplementProportionalityFactor
        u p τ x q := by

    exact
      hResidualNative

  have hUnique :
      ∀ q' : MulReal,
        H3TerminalNativeComplementProportionalityFactor
          u p τ x q' →
        q' = q := by

    intro q' hq'

    exact
      nativeComplementProportionalityFactor_unique
        hq'
        hFactor

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
      hFactor,
      hUnique,
      hNormalized,
      hResidualLog,
      hRatio,
      hRelativeCurl,
      hRelativeGradient
    ⟩

/-! ## Exhaustive terminal alternative with canonical bounded factor -/

/--
Under hypothetical nonextension, one fixed structural pair satisfies one of:

1. reinforcing-sign complementary escape;
2. cancellation-compatible synchronized triple escape on a subsequence;
3. cancellation-compatible bounded residual with a finite native
   proportionality factor `q` that is unique on the chosen terminal
   subsequence.

The third branch retains the intrinsic law

    selectedGradient ~ q * selectedSignedCurl,

together with ratio-one dominant matching and logarithmic relative
negligibility.
-/
theorem fixed_nativeComplementGradient_threeBranchAlternative_withCanonicalFactor_of_noH3PathExtension
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
          H3TerminalNativeComplementCanonicalProportionality
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
    fixed_nativeComplementGradient_threeBranchAlternative_withAsymptoticProportionality_of_noH3PathExtension
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

  · rcases hRest with hTriple | hProportional

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
                  nativeComplementCanonicalProportionality_of_asymptoticProportionality
                    hProportional
                )
            )
        ⟩

/-! ## Neutral package -/

/--
Neutral continuation alternative with exact `ℕ`-indexed native convergence
semantics and a canonical finite native proportionality factor in the bounded
cancellation branch.
-/
theorem smoothContinuationExtension_or_fixed_nativeComplementGradient_threeBranchAlternative_withCanonicalFactor
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
            H3TerminalNativeComplementCanonicalProportionality
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
          fixed_nativeComplementGradient_threeBranchAlternative_withCanonicalFactor_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
