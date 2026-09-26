import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualBoundedFactorAlternative

/-!
# Exclusive bounded residual factor dichotomy

The previous terminal development established that an eventually bounded
complementary residual logarithm satisfies the exhaustive alternative

    full canonical native factor

or

    two distinct finite native cluster factors.

This file closes the remaining logical point: those two alternatives are
mutually exclusive.

The key observation is intrinsic and independent of the PDE.  Native
convergence of an `ℕ`-indexed sequence is inherited by every cofinal
subsequence.  Hence, if the full residual has a canonical native limit `q`,
every cofinal cluster refinement must converge to that same `q`; two distinct
cluster factors are impossible.

Conversely, under eventual boundedness, failure of the canonical factor gives
persistent tail separation, and the bounded-separation theorem already
extracts two distinct finite cluster factors.

Thus, for an eventually bounded residual logarithm,

    canonical full factor
      ↔
    no two distinct finite cluster factors.

Equivalently, exactly one of the two bounded alternatives occurs.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Native convergence survives cofinal refinement -/

/--
Intrinsic terminal native convergence is inherited by any cofinal
`ℕ`-subsequence.
-/
theorem terminalNativeNatConvergesTo_comp_atTop
    {Ω : ℕ → MulReal}
    {q : MulReal}
    {k : ℕ → ℕ}
    (hNative :
      H3TerminalNativeNatConvergesTo
        Ω q)
    (hk :
      Tendsto k atTop atTop) :
    H3TerminalNativeNatConvergesTo
      (fun n : ℕ => Ω (k n))
      q := by

  apply
    (
      terminalNativeNatConvergesTo_iff_logValue_tendsto
        (fun n : ℕ => Ω (k n))
        q
    ).2

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
    ).1 hNative

  exact
    hLog.comp hk

/--
A full complementary native proportionality factor remains a proportionality
factor on every cofinal refinement of the chosen terminal spacetime sequence.
-/
theorem nativeComplementProportionalityFactor_comp_atTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {q : MulReal}
    {k : ℕ → ℕ}
    (hFactor :
      H3TerminalNativeComplementProportionalityFactor
        u p τ x q)
    (hk :
      Tendsto k atTop atTop) :
    H3TerminalNativeComplementProportionalityFactor
      u p
      (fun n : ℕ => τ (k n))
      (fun n : ℕ => x (k n))
      q := by

  unfold
    H3TerminalNativeComplementProportionalityFactor
    at hFactor ⊢

  exact
    terminalNativeNatConvergesTo_comp_atTop
      hFactor
      hk

/-! ## Canonical factor excludes distinct cofinal cluster factors -/

/--
A full canonical native factor on a fixed terminal sequence excludes two
distinct finite native cluster factors on cofinal refinements.
-/
theorem not_twoDistinctClusterFactors_of_nativeComplementHasCanonicalFactor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hCanonical :
      H3TerminalNativeComplementHasCanonicalFactor
        u p τ x) :
    ¬
      H3TerminalNativeComplementHasTwoDistinctClusterFactors
        u p τ x := by

  rintro
    ⟨
      q₁,
      q₂,
      hqNe,
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      hCluster₁,
      hCluster₂
    ⟩

  obtain
    ⟨
      q,
      hq,
      _
    ⟩ :=
    hCanonical

  have hqSub₁ :
      H3TerminalNativeComplementProportionalityFactor
        u p
        (fun n : ℕ => τ (k₁ n))
        (fun n : ℕ => x (k₁ n))
        q :=
    nativeComplementProportionalityFactor_comp_atTop
      hq
      hk₁Top

  have hqSub₂ :
      H3TerminalNativeComplementProportionalityFactor
        u p
        (fun n : ℕ => τ (k₂ n))
        (fun n : ℕ => x (k₂ n))
        q :=
    nativeComplementProportionalityFactor_comp_atTop
      hq
      hk₂Top

  have hq₁Eq :
      q₁ = q :=
    nativeComplementProportionalityFactor_unique
      hCluster₁
      hqSub₁

  have hq₂Eq :
      q₂ = q :=
    nativeComplementProportionalityFactor_unique
      hCluster₂
      hqSub₂

  apply hqNe

  calc
    q₁ = q := hq₁Eq
    _ = q₂ := hq₂Eq.symm

/-! ## Exact bounded dichotomy -/

/--
For an eventually bounded complementary residual logarithm, existence of the
full canonical native factor is equivalent to absence of two distinct finite
native cluster factors.
-/
theorem nativeComplementHasCanonicalFactor_iff_not_twoDistinctClusterFactors_of_complementBound
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (N : ℕ)
    (C : ℝ)
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
    H3TerminalNativeComplementHasCanonicalFactor
        u p τ x
      ↔
    ¬
      H3TerminalNativeComplementHasTwoDistinctClusterFactors
        u p τ x := by

  constructor

  · intro hCanonical

    exact
      not_twoDistinctClusterFactors_of_nativeComplementHasCanonicalFactor
        hCanonical

  · intro hNoTwo

    by_contra hNoCanonical

    have hSeparated :
        H3TerminalNativeComplementResidualPersistentTailSeparation
          u p τ x :=
      (
        not_nativeComplementHasCanonicalFactor_iff_persistentTailSeparation
          u p τ x
      ).1 hNoCanonical

    have hTwo :
        H3TerminalNativeComplementHasTwoDistinctClusterFactors
          u p τ x :=
      nativeComplementHasTwoDistinctClusterFactors_of_complementBound_of_persistentTailSeparation
        u p τ x
        N C
        hComplementBound
        hSeparated

    exact
      hNoTwo hTwo

/--
Equivalent negated form: under eventual boundedness, two distinct finite
cluster factors occur exactly when the full canonical factor fails.
-/
theorem nativeComplementHasTwoDistinctClusterFactors_iff_not_canonicalFactor_of_complementBound
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (N : ℕ)
    (C : ℝ)
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
    H3TerminalNativeComplementHasTwoDistinctClusterFactors
        u p τ x
      ↔
    ¬
      H3TerminalNativeComplementHasCanonicalFactor
        u p τ x := by

  constructor

  · intro hTwo hCanonical

    exact
      (
        not_twoDistinctClusterFactors_of_nativeComplementHasCanonicalFactor
          hCanonical
      )
        hTwo

  · intro hNoCanonical

    have hSeparated :
        H3TerminalNativeComplementResidualPersistentTailSeparation
          u p τ x :=
      (
        not_nativeComplementHasCanonicalFactor_iff_persistentTailSeparation
          u p τ x
      ).1 hNoCanonical

    exact
      nativeComplementHasTwoDistinctClusterFactors_of_complementBound_of_persistentTailSeparation
        u p τ x
        N C
        hComplementBound
        hSeparated

/--
Under eventual boundedness, exactly one of the two residual alternatives
occurs.
-/
theorem nativeComplement_exactlyOne_canonicalFactor_twoDistinctClusters_of_complementBound
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (N : ℕ)
    (C : ℝ)
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
    (
      H3TerminalNativeComplementHasCanonicalFactor
          u p τ x
        ∧
      ¬
        H3TerminalNativeComplementHasTwoDistinctClusterFactors
          u p τ x
    )
      ∨
    (
      H3TerminalNativeComplementHasTwoDistinctClusterFactors
          u p τ x
        ∧
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x
    ) := by

  classical

  by_cases hCanonical :
      H3TerminalNativeComplementHasCanonicalFactor
        u p τ x

  · exact
      Or.inl
        ⟨
          hCanonical,
          not_twoDistinctClusterFactors_of_nativeComplementHasCanonicalFactor
            hCanonical
        ⟩

  · have hSeparated :
        H3TerminalNativeComplementResidualPersistentTailSeparation
          u p τ x :=
      (
        not_nativeComplementHasCanonicalFactor_iff_persistentTailSeparation
          u p τ x
      ).1 hCanonical

    have hTwo :
        H3TerminalNativeComplementHasTwoDistinctClusterFactors
          u p τ x :=
      nativeComplementHasTwoDistinctClusterFactors_of_complementBound_of_persistentTailSeparation
        u p τ x
        N C
        hComplementBound
        hSeparated

    exact
      Or.inr
        ⟨
          hTwo,
          hCanonical
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
