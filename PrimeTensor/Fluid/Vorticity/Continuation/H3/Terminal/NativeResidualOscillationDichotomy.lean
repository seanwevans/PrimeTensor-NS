import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualFiniteVariation

/-!
# Canonical factor versus persistent residual oscillation

The previous terminal development identified two one-way implications:

* residual-log Cauchy control is exactly equivalent to existence of a full
  canonical native proportionality factor;
* finite total residual-log variation is sufficient for that Cauchy control.

This file records the exact complementary alternative when Cauchy control
fails.

For a real sequence `R`, failure of the Cauchy property is equivalent to the
existence of one fixed scale `ε > 0` such that arbitrarily far down the
sequence there are two indices `m,n` with

    dist (R m) (R n) ≥ ε.

Specializing to the exact complementary residual logarithm gives a neutral
and exhaustive alternative on every fixed terminal spacetime sequence:

    full canonical native factor
      OR
    persistent tail separation of the residual logarithm.

The second branch is not interpreted as blowup.  It is precisely the
topological obstruction to full residual convergence.  In particular, it
allows a bounded residual to continue oscillating between multiple finite
cluster states.

Since finite total consecutive variation would force Cauchy convergence,
persistent tail separation also rules out the finite-variation criterion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Generic metric obstruction to Cauchy convergence -/

/--
A real sequence is either Cauchy or has a fixed positive separation scale that
reappears arbitrarily far down its tail.
-/
private theorem real_cauchySeq_or_persistentTailSeparation
    (R : ℕ → ℝ) :
    CauchySeq R
      ∨
    ∃ ε : ℝ,
      0 < ε
        ∧
      ∀ N : ℕ,
        ∃ m : ℕ,
          N ≤ m
            ∧
          ∃ n : ℕ,
            N ≤ n
              ∧
            ε ≤ dist (R m) (R n) := by

  by_cases hCauchy :
      CauchySeq R

  · exact
      Or.inl hCauchy

  · right

    have hMetric :
        ¬
          (
            ∀ ε : ℝ,
              0 < ε →
              ∃ N : ℕ,
                ∀ m : ℕ,
                  N ≤ m →
                  ∀ n : ℕ,
                    N ≤ n →
                    dist (R m) (R n) < ε
          ) := by

      intro h

      exact
        hCauchy
          (
            Metric.cauchySeq_iff.2
              h
          )

    push_neg at hMetric

    exact hMetric

/--
Persistent tail separation is exactly the negation of the Cauchy property.
-/
private theorem real_not_cauchySeq_iff_persistentTailSeparation
    (R : ℕ → ℝ) :
    (¬ CauchySeq R)
      ↔
    ∃ ε : ℝ,
      0 < ε
        ∧
      ∀ N : ℕ,
        ∃ m : ℕ,
          N ≤ m
            ∧
          ∃ n : ℕ,
            N ≤ n
              ∧
            ε ≤ dist (R m) (R n) := by

  constructor

  · intro hNotCauchy

    rcases
      real_cauchySeq_or_persistentTailSeparation R
      with
      hCauchy | hSeparated

    · exact
        False.elim
          (
            hNotCauchy hCauchy
          )

    · exact hSeparated

  · rintro
      ⟨
        ε,
        hε,
        hSeparated
      ⟩
      hCauchy

    obtain
      ⟨
        N,
        hN
      ⟩ :=
      (
        Metric.cauchySeq_iff.1
          hCauchy
      )
        ε
        hε

    obtain
      ⟨
        m,
        hm,
        n,
        hn,
        hmn
      ⟩ :=
      hSeparated N

    exact
      (
        not_lt_of_ge hmn
      )
        (
          hN
            m hm
            n hn
        )

/-! ## Terminal residual oscillation -/

/--
The exact complementary residual logarithm has a fixed positive separation
scale on arbitrarily late tails of the chosen terminal spacetime sequence.
-/
def H3TerminalNativeComplementResidualPersistentTailSeparation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  ∃ ε : ℝ,
    0 < ε
      ∧
    ∀ N : ℕ,
      ∃ m : ℕ,
        N ≤ m
          ∧
        ∃ n : ℕ,
          N ≤ n
            ∧
          ε
            ≤
          dist
            (
              h3TerminalNativeComplementResidualLogSequence
                u p τ x m
            )
            (
              h3TerminalNativeComplementResidualLogSequence
                u p τ x n
            )

/--
Failure of residual-log Cauchy convergence is exactly persistent tail
separation.
-/
theorem not_nativeComplementResidualLogCauchy_iff_persistentTailSeparation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) :
    (
      ¬
        H3TerminalNativeComplementResidualLogCauchy
          u p τ x
    )
      ↔
    H3TerminalNativeComplementResidualPersistentTailSeparation
      u p τ x := by

  let R : ℕ → ℝ :=
    h3TerminalNativeComplementResidualLogSequence
      u p τ x

  have hGeneric :=
    real_not_cauchySeq_iff_persistentTailSeparation
      R

  unfold
    H3TerminalNativeComplementResidualPersistentTailSeparation

  change
    (
      ¬
        H3TerminalNativeComplementResidualLogCauchy
          u p τ x
    )
      ↔
    ∃ ε : ℝ,
      0 < ε
        ∧
      ∀ N : ℕ,
        ∃ m : ℕ,
          N ≤ m
            ∧
          ∃ n : ℕ,
            N ≤ n
              ∧
            ε ≤ dist (R m) (R n)

  have hResidual :
      H3TerminalNativeComplementResidualLogCauchy
          u p τ x
        ↔
      CauchySeq R := by

    unfold
      H3TerminalNativeComplementResidualLogCauchy

    change
      CauchySeq
        (
          h3TerminalNativeComplementResidualLogSequence
            u p τ x
        )
        ↔
      CauchySeq R

    rfl

  rw [hResidual]

  exact hGeneric

/--
Every fixed terminal spacetime sequence satisfies the exact alternative:

* the residual logarithm is Cauchy;
* or it has persistent tail separation.
-/
theorem nativeComplementResidualLogCauchy_or_persistentTailSeparation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) :
    H3TerminalNativeComplementResidualLogCauchy
        u p τ x
      ∨
    H3TerminalNativeComplementResidualPersistentTailSeparation
        u p τ x := by

  classical

  by_cases hCauchy :
      H3TerminalNativeComplementResidualLogCauchy
        u p τ x

  · exact
      Or.inl hCauchy

  · exact
      Or.inr
        (
          (
            not_nativeComplementResidualLogCauchy_iff_persistentTailSeparation
              u p τ x
          ).1 hCauchy
        )

/-! ## Exact canonical-factor dichotomy -/

/--
Failure of a full canonical native factor is exactly persistent tail
separation of the residual logarithm.
-/
theorem not_nativeComplementHasCanonicalFactor_iff_persistentTailSeparation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) :
    (
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x
    )
      ↔
    H3TerminalNativeComplementResidualPersistentTailSeparation
      u p τ x := by

  constructor

  · intro hNoFactor

    have hNotCauchy :
        ¬
          H3TerminalNativeComplementResidualLogCauchy
            u p τ x := by

      intro hCauchy

      exact
        hNoFactor
          (
            (
              nativeComplementHasCanonicalFactor_iff_residualLogCauchy
                u p τ x
            ).2 hCauchy
          )

    exact
      (
        not_nativeComplementResidualLogCauchy_iff_persistentTailSeparation
          u p τ x
      ).1 hNotCauchy

  · intro hSeparated
    intro hFactor

    have hCauchy :
        H3TerminalNativeComplementResidualLogCauchy
          u p τ x :=
      (
        nativeComplementHasCanonicalFactor_iff_residualLogCauchy
          u p τ x
      ).1 hFactor

    have hNotCauchy :
        ¬
          H3TerminalNativeComplementResidualLogCauchy
            u p τ x :=
      (
        not_nativeComplementResidualLogCauchy_iff_persistentTailSeparation
          u p τ x
      ).2 hSeparated

    exact
      hNotCauchy hCauchy

/--
Neutral and exhaustive fixed-sequence formulation: either a unique full native
proportionality factor exists, or the residual logarithm remains separated on
arbitrarily late tails by one fixed positive scale.
-/
theorem nativeComplementHasCanonicalFactor_or_persistentTailSeparation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) :
    H3TerminalNativeComplementHasCanonicalFactor
        u p τ x
      ∨
    H3TerminalNativeComplementResidualPersistentTailSeparation
        u p τ x := by

  classical

  by_cases hFactor :
      H3TerminalNativeComplementHasCanonicalFactor
        u p τ x

  · exact
      Or.inl hFactor

  · exact
      Or.inr
        (
          (
            not_nativeComplementHasCanonicalFactor_iff_persistentTailSeparation
              u p τ x
          ).1 hFactor
        )

/-! ## Relation to finite variation -/

/--
Persistent residual tail separation excludes finite total consecutive
residual-log variation.

This is only the contrapositive of the previously proved sufficient criterion;
no converse is claimed.
-/
theorem not_nativeComplementResidualFiniteVariation_of_persistentTailSeparation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (hSeparated :
      H3TerminalNativeComplementResidualPersistentTailSeparation
        u p τ x) :
    ¬
      H3TerminalNativeComplementResidualFiniteVariation
        u p τ x := by

  intro hVariation

  have hFactor :
      H3TerminalNativeComplementHasCanonicalFactor
        u p τ x :=
    nativeComplementHasCanonicalFactor_of_finiteVariation
      u p τ x
      hVariation

  have hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x :=
    (
      not_nativeComplementHasCanonicalFactor_iff_persistentTailSeparation
        u p τ x
    ).2 hSeparated

  exact
    hNoFactor hFactor

end

end Euclidean
end Bridge
end PrimeTensor
