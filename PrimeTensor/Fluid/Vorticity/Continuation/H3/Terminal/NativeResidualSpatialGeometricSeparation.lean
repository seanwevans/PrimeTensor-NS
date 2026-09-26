import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualTemporalVanishingGap
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Geometric spatial obstruction for the terminal residual

After excluding the temporal obstruction by a selected uniform temporal modulus,
failure of the full canonical native residual factor is forced into the
same-time spatial branch.

This file makes that branch geometric.

A selected spatial uniform modulus says that, at every selected time, nearby
selected spatial points give nearby values of the ordinary complementary first
derivative, uniformly over the selected sequence.

Under such a modulus, a persistent positive same-time derivative gap forces the
two cofinal selected spatial refinements themselves to remain a fixed positive
distance apart.

Thus, once the temporal modulus is available, failure of the canonical factor
forces a persistent geometric separation of selected spatial points.

A Cauchy selected-point sequence cannot exhibit such a cofinal separation.
Consequently:

    selected-point Cauchy
      + selected spatial uniform modulus
      + selected temporal uniform modulus
      + terminal-time convergence

implies existence of the full canonical native residual factor.

No claim is made here that the existing H³ assumptions already imply either
uniform modulus or Cauchy spatial selection.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualSpatialGeometricSeparation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Selected spatial modulus -/

/--
Uniform spatial continuity of the complementary first derivative on the
selected spacetime sequence.

The time is held at the first selected index while the two selected spatial
points are compared, matching the spatial leg of the synchronization split.
-/
def H3TerminalComplementGradientSelectedSpatialUniformModulus
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ η : ℝ,
      0 < η
        ∧
      ∀ m n : ℕ,
        dist (x m) (x n) < η →
        dist
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ m)
              (x m)
          )
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ m)
              (x n)
          )
          < ε

/-! ## Geometric cofinal separation -/

/--
Two cofinal refinements of the selected spatial points remain separated by one
fixed positive spatial distance.
-/
def H3TerminalSelectedPointPersistentCofinalSeparation
    (x : ℕ → Point3) : Prop :=
  ∃ η : ℝ,
    0 < η
      ∧
    ∃ k₁ k₂ : ℕ → ℕ,
      Tendsto k₁ atTop atTop
        ∧
      Tendsto k₂ atTop atTop
        ∧
      ∀ j : ℕ,
        η
          ≤
        dist
          (x (k₁ j))
          (x (k₂ j))

/--
A persistent same-time complementary-gradient value gap, together with a
selected spatial uniform modulus, forces persistent geometric separation of
the corresponding selected points.
-/
theorem selectedPointPersistentCofinalSeparation_of_persistentSpatialGap_of_spatialUniformModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hModulus :
      H3TerminalComplementGradientSelectedSpatialUniformModulus
        u p τ x)
    (hSpatial :
      H3TerminalComplementGradientPersistentSpatialCofinalGap
        u p τ x) :
    H3TerminalSelectedPointPersistentCofinalSeparation
      x := by

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
    hModulus
      δ
      hδ

  refine
    ⟨
      η,
      hη,
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      ?_
    ⟩

  intro j

  apply
    le_of_not_gt

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

/-! ## Noncanonicality becomes geometric under both moduli -/

/--
If the temporal uniform modulus excludes the vanishing-time temporal branch
and the spatial uniform modulus converts the remaining spatial value gap into
point separation, then failure of the canonical factor forces persistent
cofinal geometric separation of the selected points.
-/
theorem selectedPointPersistentCofinalSeparation_of_noCanonicalFactor_of_uniformModuli
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
    H3TerminalSelectedPointPersistentCofinalSeparation
      x := by

  have hSpatial :
      H3TerminalComplementGradientPersistentSpatialCofinalGap
        u p τ x :=
    persistentSpatialGap_of_noCanonicalFactor_of_selectedTemporalUniformModulus
      hTau
      hTemporalModulus
      hNoFactor

  exact
    selectedPointPersistentCofinalSeparation_of_persistentSpatialGap_of_spatialUniformModulus
      hSpatialModulus
      hSpatial

/-! ## Cauchy selected points exclude geometric separation -/

/--
A Cauchy sequence of selected spatial points cannot contain two cofinal
refinements that remain a fixed positive distance apart.
-/
theorem not_selectedPointPersistentCofinalSeparation_of_cauchySeq
    {x : ℕ → Point3}
    (hCauchy :
      CauchySeq x) :
    ¬
      H3TerminalSelectedPointPersistentCofinalSeparation
        x := by

  rintro
    ⟨
      η,
      hη,
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      hSeparated
    ⟩

  obtain
    ⟨
      N,
      hN
    ⟩ :=
    (
      Metric.cauchySeq_iff.1
        hCauchy
    )
      η
      hη

  have hEventually₁ :
      ∀ᶠ j : ℕ in atTop,
        N ≤ k₁ j :=
    (
      tendsto_atTop.1
        hk₁Top
    )
      N

  have hEventually₂ :
      ∀ᶠ j : ℕ in atTop,
        N ≤ k₂ j :=
    (
      tendsto_atTop.1
        hk₂Top
    )
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

  have hSmall :
      dist
        (x (k₁ J))
        (x (k₂ J))
        < η :=
    hN
      (k₁ J)
      hAtJ.1
      (k₂ J)
      hAtJ.2

  exact
    (
      not_lt_of_ge
        (hSeparated J)
    )
      hSmall

/-! ## Canonical factor from geometric compactness along the selection -/

/--
If the selected spatial points are Cauchy, while both selected spatial and
temporal uniform moduli hold and the selected times converge to the terminal
time, then the full canonical native residual factor exists.
-/
theorem nativeComplementHasCanonicalFactor_of_cauchySelectedPoints_of_uniformModuli
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hXCauchy :
      CauchySeq x)
    (hTemporalModulus :
      H3TerminalComplementGradientSelectedTemporalUniformModulus
        u p τ x)
    (hSpatialModulus :
      H3TerminalComplementGradientSelectedSpatialUniformModulus
        u p τ x) :
    H3TerminalNativeComplementHasCanonicalFactor
      u p τ x := by

  by_contra hNoFactor

  have hSeparated :
      H3TerminalSelectedPointPersistentCofinalSeparation
        x :=
    selectedPointPersistentCofinalSeparation_of_noCanonicalFactor_of_uniformModuli
      hTau
      hTemporalModulus
      hSpatialModulus
      hNoFactor

  exact
    (
      not_selectedPointPersistentCofinalSeparation_of_cauchySeq
        hXCauchy
    )
      hSeparated

end

end Euclidean
end Bridge
end PrimeTensor
