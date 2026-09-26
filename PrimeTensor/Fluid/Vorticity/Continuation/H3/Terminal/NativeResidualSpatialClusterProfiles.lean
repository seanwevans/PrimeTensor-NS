import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSpatialEscapeDichotomy
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Two finite spatial cluster profiles retaining the residual gap

The geometric terminal analysis has separated the noncanonical residual branch
into spatial escape or bounded spatial clustering.

For the bounded branch, it is important not to discard the PDE information
that created the spatial separation in the first place.

This file therefore extracts two distinct finite spatial cluster points while
retaining, on the same cofinal refinements,

* convergence of both selected time sequences to the terminal time `T`;
* convergence of the two selected spatial sequences to distinct points
  `y₁ ≠ y₂`; and
* one fixed positive same-time gap in the ordinary complementary first
  derivative.

Thus the bounded noncanonical branch becomes a genuine two-profile terminal
configuration rather than merely the existence of two geometric cluster
points.

No limit of the derivative values themselves is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualSpatialClusterProfiles
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Two terminal spatial profiles -/

/--
Two distinct finite spatial cluster points are realized by cofinal terminal
refinements that retain one fixed positive same-time complementary-gradient
gap.
-/
def H3TerminalComplementGradientHasTwoDistinctSpatialClusterProfiles
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ y₁ y₂ : Point3,
      y₁ ≠ y₂
        ∧
      ∃ k₁ k₂ : ℕ → ℕ,
        Tendsto k₁ atTop atTop
          ∧
        Tendsto k₂ atTop atTop
          ∧
        Tendsto
          (fun j : ℕ => τ (k₁ j))
          atTop
          (𝓝 T)
          ∧
        Tendsto
          (fun j : ℕ => τ (k₂ j))
          atTop
          (𝓝 T)
          ∧
        Tendsto
          (fun j : ℕ => x (k₁ j))
          atTop
          (𝓝 y₁)
          ∧
        Tendsto
          (fun j : ℕ => x (k₂ j))
          atTop
          (𝓝 y₂)
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

/-! ## Bounded extraction preserving the derivative gap -/

/--
A bounded persistent spatial residual gap, together with the selected spatial
uniform modulus and terminal-time convergence, yields two distinct finite
terminal spatial cluster profiles that retain the original derivative gap.
-/
theorem complementGradientHasTwoDistinctSpatialClusterProfiles_of_bounded_of_persistentSpatialGap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hBounded :
      Bornology.IsBounded (Set.range x))
    (hSpatialModulus :
      H3TerminalComplementGradientSelectedSpatialUniformModulus
        u p τ x)
    (hSpatial :
      H3TerminalComplementGradientPersistentSpatialCofinalGap
        u p τ x) :
    H3TerminalComplementGradientHasTwoDistinctSpatialClusterProfiles
      u p τ x T := by

  obtain
    ⟨
      δ,
      hδ,
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      hGap
    ⟩ :=
    hSpatial

  obtain
    ⟨
      η,
      hη,
      hUniform
    ⟩ :=
    hSpatialModulus
      δ
      hδ

  have hPointGap :
      ∀ j : ℕ,
        η
          ≤
        dist
          (x (k₁ j))
          (x (k₂ j)) := by

    intro j

    apply le_of_not_gt

    intro hNear

    have hSmall :
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
          < δ :=
      hUniform
        (k₁ j)
        (k₂ j)
        hNear

    exact
      (
        not_lt_of_ge
          (hGap j)
      )
        hSmall

  have hk₁Mem :
      ∀ j : ℕ,
        x (k₁ j) ∈ Set.range x := by

    intro j

    exact
      ⟨
        k₁ j,
        rfl
      ⟩

  obtain
    ⟨
      y₁,
      _hy₁Mem,
      φ,
      hφStrict,
      hFirst
    ⟩ :=
    tendsto_subseq_of_bounded
      hBounded
      hk₁Mem

  let secondAfterPhi : ℕ → Point3 :=
    fun j : ℕ =>
      x (k₂ (φ j))

  have hSecondMem :
      ∀ j : ℕ,
        secondAfterPhi j ∈ Set.range x := by

    intro j

    exact
      ⟨
        k₂ (φ j),
        rfl
      ⟩

  obtain
    ⟨
      y₂,
      _hy₂Mem,
      ψ,
      hψStrict,
      hSecond
    ⟩ :=
    tendsto_subseq_of_bounded
      hBounded
      hSecondMem

  have hφψTop :
      Tendsto
        (fun j : ℕ => φ (ψ j))
        atTop
        atTop := by

    exact
      hφStrict.tendsto_atTop.comp
        hψStrict.tendsto_atTop

  have hFirstFinal :
      Tendsto
        (
          fun j : ℕ =>
            x (k₁ (φ (ψ j)))
        )
        atTop
        (𝓝 y₁) := by

    simpa [Function.comp_def] using
      hFirst.comp
        hψStrict.tendsto_atTop

  have hSecondFinal :
      Tendsto
        (
          fun j : ℕ =>
            x (k₂ (φ (ψ j)))
        )
        atTop
        (𝓝 y₂) := by

    simpa [
      Function.comp_def,
      secondAfterPhi
    ] using
      hSecond

  have hDistance :
      Tendsto
        (
          fun j : ℕ =>
            dist
              (x (k₁ (φ (ψ j))))
              (x (k₂ (φ (ψ j))))
        )
        atTop
        (𝓝 (dist y₁ y₂)) :=
    hFirstFinal.dist
      hSecondFinal

  have hLimitSeparated :
      η ≤ dist y₁ y₂ := by

    apply
      ge_of_tendsto
        hDistance

    filter_upwards with j

    exact
      hPointGap
        (φ (ψ j))

  have hyNe :
      y₁ ≠ y₂ := by

    intro hyEq

    have hηZero :
        η ≤ 0 := by

      simpa [hyEq] using
        hLimitSeparated

    linarith

  let K₁ : ℕ → ℕ :=
    fun j : ℕ =>
      k₁ (φ (ψ j))

  let K₂ : ℕ → ℕ :=
    fun j : ℕ =>
      k₂ (φ (ψ j))

  have hK₁Top :
      Tendsto K₁ atTop atTop := by

    dsimp only [K₁]

    exact
      hk₁Top.comp
        hφψTop

  have hK₂Top :
      Tendsto K₂ atTop atTop := by

    dsimp only [K₂]

    exact
      hk₂Top.comp
        hφψTop

  have hTime₁ :
      Tendsto
        (fun j : ℕ => τ (K₁ j))
        atTop
        (𝓝 T) :=
    hTau.comp
      hK₁Top

  have hTime₂ :
      Tendsto
        (fun j : ℕ => τ (K₂ j))
        atTop
        (𝓝 T) :=
    hTau.comp
      hK₂Top

  have hPoint₁ :
      Tendsto
        (fun j : ℕ => x (K₁ j))
        atTop
        (𝓝 y₁) := by

    simpa only [K₁] using
      hFirstFinal

  have hPoint₂ :
      Tendsto
        (fun j : ℕ => x (K₂ j))
        atTop
        (𝓝 y₂) := by

    simpa only [K₂] using
      hSecondFinal

  have hGapFinal :
      ∀ j : ℕ,
        δ
          ≤
        dist
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ (K₁ j))
              (x (K₁ j))
          )
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ (K₁ j))
              (x (K₂ j))
          ) := by

    intro j

    simpa only [K₁, K₂] using
      hGap
        (φ (ψ j))

  exact
    ⟨
      δ,
      hδ,
      y₁,
      y₂,
      hyNe,
      K₁,
      K₂,
      hK₁Top,
      hK₂Top,
      hTime₁,
      hTime₂,
      hPoint₁,
      hPoint₂,
      hGapFinal
    ⟩

/-! ## Noncanonical bounded branch -/

/--
Under the selected temporal modulus, failure of the canonical factor is forced
into the spatial branch.  If the selected points are also bounded and the
selected spatial modulus is available, that branch yields two distinct finite
terminal cluster profiles retaining a fixed positive derivative gap.
-/
theorem complementGradientHasTwoDistinctSpatialClusterProfiles_of_noCanonicalFactor_of_uniformModuli_of_bounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hTemporalModulus :
      H3TerminalComplementGradientSelectedTemporalUniformModulus
        u p τ x)
    (hSpatialModulus :
      H3TerminalComplementGradientSelectedSpatialUniformModulus
        u p τ x)
    (hBounded :
      Bornology.IsBounded (Set.range x))
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x) :
    H3TerminalComplementGradientHasTwoDistinctSpatialClusterProfiles
      u p τ x T := by

  have hSpatial :
      H3TerminalComplementGradientPersistentSpatialCofinalGap
        u p τ x :=
    persistentSpatialGap_of_noCanonicalFactor_of_selectedTemporalUniformModulus
      hTau
      hTemporalModulus
      hNoFactor

  exact
    complementGradientHasTwoDistinctSpatialClusterProfiles_of_bounded_of_persistentSpatialGap
      hTau
      hBounded
      hSpatialModulus
      hSpatial

end

end Euclidean
end Bridge
end PrimeTensor
