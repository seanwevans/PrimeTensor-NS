import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualPositiveClusterGap

/-!
# Cofinal synchronization criterion for the terminal native residual

The bounded two-cluster analysis identified a positive synchronized logarithmic
gap between two cofinal residual refinements.  This file isolates the exact
topological principle behind that phenomenon, without assuming boundedness.

For a fixed terminal spacetime sequence, define cofinal synchronization to mean:

    every two cofinal refinements of the residual logarithm
    have mutual distance tending to zero.

This condition is exactly equivalent to the residual logarithm being Cauchy,
and hence exactly equivalent to existence of the full canonical native factor.

The negation also has an exact form: there are two cofinal refinements and one
fixed `ε > 0` whose synchronized residual-log distance stays at least `ε` at
every index.

Thus the remaining PDE problem can be stated without reference to abstract
Cauchy filters or cluster extraction:

    prove that all cofinal terminal residual refinements synchronize.

No spatial regularity estimate capable of proving that statement is assumed
here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Cofinal synchronized obstruction -/

/--
A fixed positive residual-log gap along two cofinal refinements of the same
terminal spacetime sequence.
-/
def H3TerminalNativeComplementResidualCofinalGap
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  ∃ ε : ℝ,
    0 < ε
      ∧
    ∃ k₁ k₂ : ℕ → ℕ,
      Tendsto k₁ atTop atTop
        ∧
      Tendsto k₂ atTop atTop
        ∧
      ∀ j : ℕ,
        ε
          ≤
        dist
          (
            h3TerminalNativeComplementResidualLogSequence
              u p τ x (k₁ j)
          )
          (
            h3TerminalNativeComplementResidualLogSequence
              u p τ x (k₂ j)
          )

/--
Persistent tail separation can be synchronized onto two cofinal refinements.
-/
theorem nativeComplementResidualCofinalGap_of_persistentTailSeparation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hSeparated :
      H3TerminalNativeComplementResidualPersistentTailSeparation
        u p τ x) :
    H3TerminalNativeComplementResidualCofinalGap
      u p τ x := by

  obtain
    ⟨
      ε,
      hε,
      hTail
    ⟩ :=
    hSeparated

  have hChoice :
      ∀ j : ℕ,
        ∃ m : ℕ,
          j ≤ m
            ∧
          ∃ n : ℕ,
            j ≤ n
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
              ) := by

    intro j

    exact
      hTail j

  choose k₁ hk₁ k₂ hk₂ hGap using
    hChoice

  have hk₁Top :
      Tendsto k₁ atTop atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro N

    filter_upwards
      [eventually_ge_atTop N]
      with j hj

    exact
      le_trans
        hj
        (hk₁ j)

  have hk₂Top :
      Tendsto k₂ atTop atTop := by

    refine
      tendsto_atTop.2
        ?_

    intro N

    filter_upwards
      [eventually_ge_atTop N]
      with j hj

    exact
      le_trans
        hj
        (hk₂ j)

  exact
    ⟨
      ε,
      hε,
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      hGap
    ⟩

/--
A fixed positive gap on two cofinal refinements implies persistent tail
separation of the original residual logarithm.
-/
theorem persistentTailSeparation_of_nativeComplementResidualCofinalGap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hGap :
      H3TerminalNativeComplementResidualCofinalGap
        u p τ x) :
    H3TerminalNativeComplementResidualPersistentTailSeparation
      u p τ x := by

  obtain
    ⟨
      ε,
      hε,
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      hGap
    ⟩ :=
    hGap

  refine
    ⟨
      ε,
      hε,
      ?_
    ⟩

  intro N

  have hEventually₁ :
      ∀ᶠ j : ℕ in atTop,
        N ≤ k₁ j :=
    (tendsto_atTop.1 hk₁Top)
      N

  have hEventually₂ :
      ∀ᶠ j : ℕ in atTop,
        N ≤ k₂ j :=
    (tendsto_atTop.1 hk₂Top)
      N

  have hEventually :
      ∀ᶠ j : ℕ in atTop,
        N ≤ k₁ j
          ∧
        N ≤ k₂ j :=
    hEventually₁.and
      hEventually₂

  rw [eventually_atTop] at hEventually

  obtain
    ⟨
      J,
      hJ
    ⟩ :=
    hEventually

  have hAtJ :=
    hJ J le_rfl

  exact
    ⟨
      k₁ J,
      hAtJ.1,
      k₂ J,
      hAtJ.2,
      hGap J
    ⟩

/--
Persistent tail separation and a synchronized positive cofinal gap are exactly
the same obstruction.
-/
theorem nativeComplementResidualPersistentTailSeparation_iff_cofinalGap
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) :
    H3TerminalNativeComplementResidualPersistentTailSeparation
        u p τ x
      ↔
    H3TerminalNativeComplementResidualCofinalGap
        u p τ x := by

  constructor

  · exact
      nativeComplementResidualCofinalGap_of_persistentTailSeparation

  · exact
      persistentTailSeparation_of_nativeComplementResidualCofinalGap

/--
Failure of residual-log Cauchy convergence is exactly the existence of a
positive synchronized cofinal gap.
-/
theorem not_nativeComplementResidualLogCauchy_iff_cofinalGap
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
    H3TerminalNativeComplementResidualCofinalGap
      u p τ x := by

  rw [
    not_nativeComplementResidualLogCauchy_iff_persistentTailSeparation,
    nativeComplementResidualPersistentTailSeparation_iff_cofinalGap
  ]

/-! ## Exact cofinal synchronization criterion -/

/--
Every two cofinal refinements of the residual logarithm synchronize:
their pointwise mutual distance tends to zero.
-/
def H3TerminalNativeComplementResidualCofinalSynchronization
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  ∀ k₁ k₂ : ℕ → ℕ,
    Tendsto k₁ atTop atTop →
    Tendsto k₂ atTop atTop →
    Tendsto
      (
        fun j : ℕ =>
          dist
            (
              h3TerminalNativeComplementResidualLogSequence
                u p τ x (k₁ j)
            )
            (
              h3TerminalNativeComplementResidualLogSequence
                u p τ x (k₂ j)
            )
      )
      atTop
      (𝓝 0)

/--
Residual-log Cauchy convergence forces synchronization of every pair of
cofinal refinements.
-/
theorem nativeComplementResidualCofinalSynchronization_of_logCauchy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hCauchy :
      H3TerminalNativeComplementResidualLogCauchy
        u p τ x) :
    H3TerminalNativeComplementResidualCofinalSynchronization
      u p τ x := by

  have hR :
      CauchySeq
        (
          h3TerminalNativeComplementResidualLogSequence
            u p τ x
        ) := by

    unfold
      H3TerminalNativeComplementResidualLogCauchy
      at hCauchy

    change
      CauchySeq
        (
          h3TerminalNativeComplementResidualLogSequence
            u p τ x
        )
      at hCauchy

    exact hCauchy

  obtain
    ⟨
      r,
      hr
    ⟩ :=
    cauchySeq_tendsto_of_complete
      hR

  intro k₁ k₂ hk₁Top hk₂Top

  have h₁ :
      Tendsto
        (
          fun j : ℕ =>
            h3TerminalNativeComplementResidualLogSequence
              u p τ x (k₁ j)
        )
        atTop
        (𝓝 r) :=
    hr.comp
      hk₁Top

  have h₂ :
      Tendsto
        (
          fun j : ℕ =>
            h3TerminalNativeComplementResidualLogSequence
              u p τ x (k₂ j)
        )
        atTop
        (𝓝 r) :=
    hr.comp
      hk₂Top

  simpa using
    h₁.dist h₂

/--
If every pair of cofinal residual refinements synchronizes, then the original
residual logarithm is Cauchy.
-/
theorem nativeComplementResidualLogCauchy_of_cofinalSynchronization
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hSync :
      H3TerminalNativeComplementResidualCofinalSynchronization
        u p τ x) :
    H3TerminalNativeComplementResidualLogCauchy
      u p τ x := by

  classical

  by_contra hNotCauchy

  have hGap :
      H3TerminalNativeComplementResidualCofinalGap
        u p τ x :=
    (
      not_nativeComplementResidualLogCauchy_iff_cofinalGap
        u p τ x
    ).1 hNotCauchy

  obtain
    ⟨
      ε,
      hε,
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      hGap
    ⟩ :=
    hGap

  have hZero :
      Tendsto
        (
          fun j : ℕ =>
            dist
              (
                h3TerminalNativeComplementResidualLogSequence
                  u p τ x (k₁ j)
              )
              (
                h3TerminalNativeComplementResidualLogSequence
                  u p τ x (k₂ j)
              )
        )
        atTop
        (𝓝 0) :=
    hSync
      k₁ k₂
      hk₁Top hk₂Top

  have hEventuallySmall :
      ∀ᶠ j : ℕ in atTop,
        dist
          (
            h3TerminalNativeComplementResidualLogSequence
              u p τ x (k₁ j)
          )
          (
            h3TerminalNativeComplementResidualLogSequence
              u p τ x (k₂ j)
          )
          < ε :=
    hZero.eventually_lt
      tendsto_const_nhds
      hε

  rw [eventually_atTop] at hEventuallySmall

  obtain
    ⟨
      J,
      hJ
    ⟩ :=
    hEventuallySmall

  have hSmall :
      dist
        (
          h3TerminalNativeComplementResidualLogSequence
            u p τ x (k₁ J)
        )
        (
          h3TerminalNativeComplementResidualLogSequence
            u p τ x (k₂ J)
        )
        < ε :=
    hJ J le_rfl

  exact
    (
      not_lt_of_ge
        (hGap J)
    )
      hSmall

/--
The residual logarithm is Cauchy exactly when all of its cofinal refinements
synchronize pairwise.
-/
theorem nativeComplementResidualLogCauchy_iff_cofinalSynchronization
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) :
    H3TerminalNativeComplementResidualLogCauchy
        u p τ x
      ↔
    H3TerminalNativeComplementResidualCofinalSynchronization
        u p τ x := by

  constructor

  · exact
      nativeComplementResidualCofinalSynchronization_of_logCauchy

  · exact
      nativeComplementResidualLogCauchy_of_cofinalSynchronization

/-! ## Canonical native factor criterion -/

/--
A fixed terminal sequence has a full canonical native residual factor exactly
when every pair of cofinal residual refinements synchronizes logarithmically.
-/
theorem nativeComplementHasCanonicalFactor_iff_cofinalSynchronization
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) :
    H3TerminalNativeComplementHasCanonicalFactor
        u p τ x
      ↔
    H3TerminalNativeComplementResidualCofinalSynchronization
        u p τ x := by

  rw [
    nativeComplementHasCanonicalFactor_iff_residualLogCauchy,
    nativeComplementResidualLogCauchy_iff_cofinalSynchronization
  ]

/--
Failure of the full canonical native factor is exactly the existence of two
cofinal refinements carrying a fixed positive synchronized residual-log gap.
-/
theorem not_nativeComplementHasCanonicalFactor_iff_cofinalGap
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
    H3TerminalNativeComplementResidualCofinalGap
      u p τ x := by

  rw [
    not_nativeComplementHasCanonicalFactor_iff_persistentTailSeparation,
    nativeComplementResidualPersistentTailSeparation_iff_cofinalGap
  ]

end

end Euclidean
end Bridge
end PrimeTensor
