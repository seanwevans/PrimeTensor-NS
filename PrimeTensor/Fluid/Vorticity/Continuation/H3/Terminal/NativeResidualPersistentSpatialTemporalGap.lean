import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSpatialTemporalSynchronization

/-!
# Persistent spatial-or-temporal obstruction for the terminal residual

The previous file split every positive synchronized complementary-gradient gap
pointwise into a same-time spatial leg or a same-point temporal leg.

Pointwise splitting still allows the responsible leg to alternate forever.
This file removes that ambiguity by passing to one further cofinal
subsequence.

If the spatial half-gap occurs frequently, extract a strictly increasing
subsequence on which it occurs at every index.

If it does not occur frequently, it is eventually false; because the full
half-gap disjunction holds at every index, the temporal half-gap is then
eventually true, and a cofinal extraction makes it true at every index.

Hence failure of the full canonical native factor forces one definite
mechanism on cofinal refinements:

* a persistent same-time spatial complementary-gradient gap; or
* a persistent same-point temporal complementary-gradient gap.

This remains a structural reduction only.  It does not decide which mechanism
is realized by a hypothetical noncontinuing solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Persistent leg predicates -/

/--
Two cofinal refinements retain one fixed positive same-time spatial gap in the
ordinary complementary first derivative.
-/
def H3TerminalComplementGradientPersistentSpatialCofinalGap
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ k₁ k₂ : ℕ → ℕ,
      Tendsto k₁ atTop atTop
        ∧
      Tendsto k₂ atTop atTop
        ∧
      ∀ j : ℕ,
        δ
          ≤
        dist
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ (k₁ j))
              (x (k₁ j))
          )
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ (k₁ j))
              (x (k₂ j))
          )

/--
Two cofinal refinements retain one fixed positive same-point temporal gap in
the ordinary complementary first derivative.
-/
def H3TerminalComplementGradientPersistentTemporalCofinalGap
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ k₁ k₂ : ℕ → ℕ,
      Tendsto k₁ atTop atTop
        ∧
      Tendsto k₂ atTop atTop
        ∧
      ∀ j : ℕ,
        δ
          ≤
        dist
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ (k₁ j))
              (x (k₂ j))
          )
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ (k₂ j))
              (x (k₂ j))
          )

/-! ## Cofinal extraction of one persistent mechanism -/

/--
A full physical cofinal gap has a cofinal refinement on which either the
spatial leg carries a fixed positive gap at every index or the temporal leg
does.
-/
theorem complementGradientCofinalGap_refines_to_persistentSpatial_or_temporal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hGap :
      H3TerminalComplementGradientCofinalGap
        u p τ x) :
    H3TerminalComplementGradientPersistentSpatialCofinalGap
        u p τ x
      ∨
    H3TerminalComplementGradientPersistentTemporalCofinalGap
        u p τ x := by

  classical

  obtain
    ⟨
      ε,
      hε,
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      hSplit
    ⟩ :=
    complementGradientCofinalGap_split_spatial_temporal
      hGap

  let S : ℕ → Prop :=
    fun j : ℕ =>
      ε / 2
        ≤
      dist
        (
          h3TerminalComplementGradientFieldForPair
            u p
            (τ (k₁ j))
            (x (k₁ j))
        )
        (
          h3TerminalComplementGradientFieldForPair
            u p
            (τ (k₁ j))
            (x (k₂ j))
        )

  let Q : ℕ → Prop :=
    fun j : ℕ =>
      ε / 2
        ≤
      dist
        (
          h3TerminalComplementGradientFieldForPair
            u p
            (τ (k₁ j))
            (x (k₂ j))
        )
        (
          h3TerminalComplementGradientFieldForPair
            u p
            (τ (k₂ j))
            (x (k₂ j))
        )

  have hSQ :
      ∀ j : ℕ,
        S j ∨ Q j := by

    intro j

    simpa only [S, Q] using
      hSplit j

  have hHalfPos :
      0 < ε / 2 :=
    half_pos hε

  by_cases hSFreq :
      ∃ᶠ j : ℕ in atTop,
        S j

  · obtain
      ⟨
        φ,
        hφStrict,
        hφS
      ⟩ :=
      extraction_of_frequently_atTop
        hSFreq

    let K₁ : ℕ → ℕ :=
      fun j : ℕ =>
        k₁ (φ j)

    let K₂ : ℕ → ℕ :=
      fun j : ℕ =>
        k₂ (φ j)

    have hK₁Top :
        Tendsto K₁ atTop atTop := by

      dsimp only [K₁]

      exact
        hk₁Top.comp
          hφStrict.tendsto_atTop

    have hK₂Top :
        Tendsto K₂ atTop atTop := by

      dsimp only [K₂]

      exact
        hk₂Top.comp
          hφStrict.tendsto_atTop

    left

    refine
      ⟨
        ε / 2,
        hHalfPos,
        K₁,
        K₂,
        hK₁Top,
        hK₂Top,
        ?_
      ⟩

    intro j

    have h :=
      hφS j

    simpa only [S, K₁, K₂] using h

  · have hEventuallyNotS :
        ∀ᶠ j : ℕ in atTop,
          ¬ S j :=
      (
        not_frequently
      ).1 hSFreq

    have hEventuallyQ :
        ∀ᶠ j : ℕ in atTop,
          Q j := by

      filter_upwards
        [hEventuallyNotS]
        with j hj

      exact
        (hSQ j).resolve_left
          hj

    obtain
      ⟨
        φ,
        hφStrict,
        hφQ
      ⟩ :=
      extraction_of_eventually_atTop
        hEventuallyQ

    let K₁ : ℕ → ℕ :=
      fun j : ℕ =>
        k₁ (φ j)

    let K₂ : ℕ → ℕ :=
      fun j : ℕ =>
        k₂ (φ j)

    have hK₁Top :
        Tendsto K₁ atTop atTop := by

      dsimp only [K₁]

      exact
        hk₁Top.comp
          hφStrict.tendsto_atTop

    have hK₂Top :
        Tendsto K₂ atTop atTop := by

      dsimp only [K₂]

      exact
        hk₂Top.comp
          hφStrict.tendsto_atTop

    right

    refine
      ⟨
        ε / 2,
        hHalfPos,
        K₁,
        K₂,
        hK₁Top,
        hK₂Top,
        ?_
      ⟩

    intro j

    have h :=
      hφQ j

    simpa only [Q, K₁, K₂] using h

/-! ## Canonical-factor obstruction -/

/--
Failure of the full canonical native factor forces one persistent cofinal
mechanism: either a same-time spatial gap or a same-point temporal gap.
-/
theorem not_nativeComplementHasCanonicalFactor_forces_persistentSpatial_or_temporalGap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x) :
    H3TerminalComplementGradientPersistentSpatialCofinalGap
        u p τ x
      ∨
    H3TerminalComplementGradientPersistentTemporalCofinalGap
        u p τ x := by

  have hGap :
      H3TerminalComplementGradientCofinalGap
        u p τ x :=
    (
      not_nativeComplementHasCanonicalFactor_iff_complementGradientCofinalGap
        u p τ x
    ).1 hNoFactor

  exact
    complementGradientCofinalGap_refines_to_persistentSpatial_or_temporal
      hGap

/-! ## Logical synchronization frontier -/

/--
If neither persistent cofinal obstruction can occur, the full canonical native
factor must exist.
-/
theorem nativeComplementHasCanonicalFactor_of_no_persistentSpatial_or_temporalGap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hNoSpatial :
      ¬
        H3TerminalComplementGradientPersistentSpatialCofinalGap
          u p τ x)
    (hNoTemporal :
      ¬
        H3TerminalComplementGradientPersistentTemporalCofinalGap
          u p τ x) :
    H3TerminalNativeComplementHasCanonicalFactor
      u p τ x := by

  by_contra hNoFactor

  rcases
    not_nativeComplementHasCanonicalFactor_forces_persistentSpatial_or_temporalGap
      hNoFactor
    with
    hSpatial | hTemporal

  · exact
      hNoSpatial hSpatial

  · exact
      hNoTemporal hTemporal

end

end Euclidean
end Bridge
end PrimeTensor
