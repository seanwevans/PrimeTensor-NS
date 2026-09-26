import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeConvergenceCanonicalFactor

/-!
# Cauchy criterion for a full terminal native proportionality factor

The preceding terminal development identifies a finite native
proportionality factor on an extracted bounded-residual subsequence.

That does not imply convergence of the residual on the original bounded
terminal sequence: boundedness alone only gives cluster subsequences.

This file isolates the exact missing condition.

For any `ℕ`-indexed native sequence `Ω`,

    there exists a unique intrinsic native limit of `Ω`

if and only if

    logValue (Ω n)

is an ordinary real Cauchy sequence.

Specializing to the complementary residual

    ratio selectedGradient selectedSignedCurl,

a full canonical proportionality factor on a fixed terminal spacetime
sequence is therefore equivalent to Cauchy control of the residual
logarithm.

Thus the remaining upgrade from "canonical on an extracted subsequence" to
"canonical on the full bounded sequence" is exactly a Cauchy problem.  No
claim is made here that the currently available boundedness, ratio-one, or
relative-negligibility hypotheses already imply that Cauchy property.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## A real convergence-to-Cauchy bridge -/

/--
A real sequence converging to a finite limit is Cauchy.

This is stated locally so the terminal native criterion below does not depend
on a separate convenience theorem for the forward implication.
-/
private theorem real_cauchySeq_of_tendsto
    {f : ℕ → ℝ}
    {r : ℝ}
    (h :
      Tendsto
        f
        atTop
        (𝓝 r)) :
    CauchySeq f := by

  rw [Metric.cauchySeq_iff]

  intro ε hε

  have hHalf :
      0 < ε / 2 := by
    positivity

  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        dist (f n) r < ε / 2 :=
    (Metric.tendsto_nhds.mp h)
      (ε / 2)
      hHalf

  obtain
    ⟨
      N,
      hN
    ⟩ :=
    eventually_atTop.1 hEventually

  refine
    ⟨
      N,
      ?_
    ⟩

  intro m hm n hn

  have hm' :
      dist (f m) r < ε / 2 :=
    hN m hm

  have hn' :
      dist r (f n) < ε / 2 := by

    simpa [dist_comm] using
      (hN n hn)

  calc
    dist (f m) (f n)
        ≤
      dist (f m) r
        +
      dist r (f n) := by
          exact
            dist_triangle
              (f m)
              r
              (f n)

    _ <
      ε / 2 + ε / 2 := by
        exact
          add_lt_add
            hm'
            hn'

    _ = ε := by
      ring

/-! ## Exact Cauchy criterion for terminal native convergence -/

/--
An `ℕ`-indexed native sequence admits a unique intrinsic native limit exactly
when its canonical logarithmic coordinate sequence is Cauchy.

The reverse implication uses completeness of `ℝ`, surjectivity of
`MulReal.logValue`, and the already-proved equivalence between intrinsic
native convergence and ordinary logarithmic convergence.
-/
theorem terminalNativeNat_existsUniqueLimit_iff_logValue_cauchySeq
    (Ω : ℕ → MulReal) :
    (
      ∃! q : MulReal,
        H3TerminalNativeNatConvergesTo
          Ω q
    )
      ↔
    CauchySeq
      (
        fun n : ℕ =>
          PrimeTensor.Bridge.MulReal.logValue
            (Ω n)
      ) := by

  constructor

  · rintro
      ⟨
        q,
        hq,
        _
      ⟩

    have hLog :
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
          ) :=
      (
        terminalNativeNatConvergesTo_iff_logValue_tendsto
          Ω q
      ).1 hq

    exact
      real_cauchySeq_of_tendsto
        hLog

  · intro hCauchy

    obtain
      ⟨
        r,
        hr
      ⟩ :=
      cauchySeq_tendsto_of_complete
        hCauchy

    obtain
      ⟨
        q,
        hq
      ⟩ :=
      PrimeTensor.Bridge.MulReal.logValue_surjective
        r

    have hLog :
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

      rw [hq]

      exact hr

    have hNative :
        H3TerminalNativeNatConvergesTo
          Ω q :=
      (
        terminalNativeNatConvergesTo_iff_logValue_tendsto
          Ω q
      ).2 hLog

    refine
      ⟨
        q,
        hNative,
        ?_
      ⟩

    intro q' hq'

    exact
      terminalNativeNatConvergesTo_unique
        hq'
        hNative

/-! ## Full residual-factor criterion on a fixed terminal sequence -/

/--
The exact residual logarithm on a fixed terminal spacetime sequence is Cauchy.
-/
def H3TerminalNativeComplementResidualLogCauchy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  CauchySeq
    (
      fun n : ℕ =>
        PrimeTensor.Bridge.MulReal.logValue
          (
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
    )

/--
A fixed terminal spacetime sequence has a full canonical native
proportionality factor when the exact residual ratio has a unique intrinsic
native limit.
-/
def H3TerminalNativeComplementHasCanonicalFactor
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  ∃! q : MulReal,
    H3TerminalNativeComplementProportionalityFactor
      u p τ x q

/--
For a fixed terminal spacetime sequence, existence of a full canonical native
proportionality factor is exactly the Cauchy property of the residual
logarithm.
-/
theorem nativeComplementHasCanonicalFactor_iff_residualLogCauchy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) :
    H3TerminalNativeComplementHasCanonicalFactor
        u p τ x
      ↔
    H3TerminalNativeComplementResidualLogCauchy
        u p τ x := by

  unfold
    H3TerminalNativeComplementHasCanonicalFactor
    H3TerminalNativeComplementResidualLogCauchy
    H3TerminalNativeComplementProportionalityFactor

  exact
    terminalNativeNat_existsUniqueLimit_iff_logValue_cauchySeq
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

/--
The Cauchy criterion can equivalently be stated using the native complementary
gradient itself, because that quantity is pointwise exactly the residual ratio.
-/
theorem nativeComplementResidualLogCauchy_iff_complementLogCauchy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) :
    H3TerminalNativeComplementResidualLogCauchy
        u p τ x
      ↔
    CauchySeq
      (
        fun n : ℕ =>
          PrimeTensor.Bridge.MulReal.logValue
            (
              h3TerminalNativeComplementGradientForPair
                u p
                (τ n)
                (x n)
            )
      ) := by

  unfold
    H3TerminalNativeComplementResidualLogCauchy

  constructor

  · intro h

    simpa only [
      h3TerminalNativeComplementGradientForPair_eq_residualRatio
    ] using h

  · intro h

    simpa only [
      h3TerminalNativeComplementGradientForPair_eq_residualRatio
    ] using h

/--
Equivalent formulation: the complementary native residual itself has a unique
intrinsic native limit exactly when its logarithmic coordinate sequence is
Cauchy.
-/
theorem nativeComplement_existsUniqueLimit_iff_complementLogCauchy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) :
    (
      ∃! q : MulReal,
        H3TerminalNativeNatConvergesTo
          (
            fun n : ℕ =>
              h3TerminalNativeComplementGradientForPair
                u p
                (τ n)
                (x n)
          )
          q
    )
      ↔
    CauchySeq
      (
        fun n : ℕ =>
          PrimeTensor.Bridge.MulReal.logValue
            (
              h3TerminalNativeComplementGradientForPair
                u p
                (τ n)
                (x n)
            )
      ) := by

  exact
    terminalNativeNat_existsUniqueLimit_iff_logValue_cauchySeq
      (
        fun n : ℕ =>
          h3TerminalNativeComplementGradientForPair
            u p
            (τ n)
            (x n)
      )

end

end Euclidean
end Bridge
end PrimeTensor
