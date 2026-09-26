import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSpatialGeometricSeparation
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Bounded spatial obstruction gives two distinct point clusters

The preceding terminal analysis shows that, under selected spatial and temporal
uniform moduli, failure of the full canonical native residual factor forces a
persistent positive cofinal separation of the selected spatial points.

Because `Point3` is a finite product of real lines, it is a proper metric
space once the finite axis instance is installed.  Therefore a bounded
spatial selection has convergent subsequences.

This file combines those facts:

* persistent cofinal spatial separation + bounded selected points
  gives two distinct finite `Point3` cluster points;
* without boundedness, the selected points are spatially unbounded.

Hence, under both selected moduli and terminal-time convergence, a
noncanonical native residual factor forces the selected geometry into exactly
the useful bounded/unbounded alternative:

    spatially unbounded selection

or

    two distinct finite spatial cluster points.

No compactness of the full Navier--Stokes trajectory, translation
recentering, or uniqueness of the spatial cluster point is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualSpatialClusterDichotomy
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Two distinct spatial cluster points -/

/--
The selected point sequence has two distinct finite cluster points realized by
cofinal refinements.
-/
def H3TerminalSelectedPointHasTwoDistinctClusterPoints
    (x : ℕ → Point3) : Prop :=
  ∃ y₁ y₂ : Point3,
    y₁ ≠ y₂
      ∧
    ∃ k₁ k₂ : ℕ → ℕ,
      Tendsto k₁ atTop atTop
        ∧
      Tendsto k₂ atTop atTop
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

/--
A bounded selected-point sequence with persistent cofinal separation has two
distinct finite cluster points.
-/
theorem selectedPointHasTwoDistinctClusterPoints_of_bounded_of_persistentCofinalSeparation
    {x : ℕ → Point3}
    (hBounded :
      Bornology.IsBounded (Set.range x))
    (hSeparated :
      H3TerminalSelectedPointPersistentCofinalSeparation
        x) :
    H3TerminalSelectedPointHasTwoDistinctClusterPoints
      x := by

  obtain
    ⟨
      η,
      hη,
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      hGap
    ⟩ :=
    hSeparated

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
      hGap
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

  have hK₁Limit :
      Tendsto
        (fun j : ℕ => x (K₁ j))
        atTop
        (𝓝 y₁) := by

    simpa only [K₁] using
      hFirstFinal

  have hK₂Limit :
      Tendsto
        (fun j : ℕ => x (K₂ j))
        atTop
        (𝓝 y₂) := by

    simpa only [K₂] using
      hSecondFinal

  exact
    ⟨
      y₁,
      y₂,
      hyNe,
      K₁,
      K₂,
      hK₁Top,
      hK₂Top,
      hK₁Limit,
      hK₂Limit
    ⟩

/-! ## Bounded / unbounded geometric dichotomy -/

/--
Persistent cofinal point separation forces either spatial unboundedness or two
distinct finite spatial cluster points.
-/
theorem selectedPoint_unbounded_or_twoDistinctClusterPoints_of_persistentCofinalSeparation
    {x : ℕ → Point3}
    (hSeparated :
      H3TerminalSelectedPointPersistentCofinalSeparation
        x) :
    (
      ¬ Bornology.IsBounded (Set.range x)
    )
      ∨
    H3TerminalSelectedPointHasTwoDistinctClusterPoints
      x := by

  classical

  by_cases hBounded :
      Bornology.IsBounded (Set.range x)

  · exact
      Or.inr
        (
          selectedPointHasTwoDistinctClusterPoints_of_bounded_of_persistentCofinalSeparation
            hBounded
            hSeparated
        )

  · exact
      Or.inl hBounded

/-! ## Noncanonical residual implies geometric spatial classification -/

/--
Under terminal-time convergence and both selected uniform moduli, failure of
the canonical native residual factor forces either

* an unbounded selected spatial sequence; or
* two distinct finite spatial cluster points on cofinal refinements.
-/
theorem selectedPoint_unbounded_or_twoDistinctClusterPoints_of_noCanonicalFactor_of_uniformModuli
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
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x) :
    (
      ¬ Bornology.IsBounded (Set.range x)
    )
      ∨
    H3TerminalSelectedPointHasTwoDistinctClusterPoints
      x := by

  have hSeparated :
      H3TerminalSelectedPointPersistentCofinalSeparation
        x :=
    selectedPointPersistentCofinalSeparation_of_noCanonicalFactor_of_uniformModuli
      hTau
      hTemporalModulus
      hSpatialModulus
      hNoFactor

  exact
    selectedPoint_unbounded_or_twoDistinctClusterPoints_of_persistentCofinalSeparation
      hSeparated

/-! ## Bounded specialization -/

/--
If the selected points are known to remain bounded, the same hypotheses reduce
noncanonicality directly to two distinct finite spatial cluster points.
-/
theorem selectedPointHasTwoDistinctClusterPoints_of_noCanonicalFactor_of_uniformModuli_of_bounded
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
    H3TerminalSelectedPointHasTwoDistinctClusterPoints
      x := by

  have hSeparated :
      H3TerminalSelectedPointPersistentCofinalSeparation
        x :=
    selectedPointPersistentCofinalSeparation_of_noCanonicalFactor_of_uniformModuli
      hTau
      hTemporalModulus
      hSpatialModulus
      hNoFactor

  exact
    selectedPointHasTwoDistinctClusterPoints_of_bounded_of_persistentCofinalSeparation
      hBounded
      hSeparated

end

end Euclidean
end Bridge
end PrimeTensor
