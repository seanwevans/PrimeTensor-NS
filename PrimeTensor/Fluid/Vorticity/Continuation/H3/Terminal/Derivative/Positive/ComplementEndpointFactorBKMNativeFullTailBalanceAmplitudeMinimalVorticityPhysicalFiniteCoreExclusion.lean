import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalSpatialEscapeExclusion

/-!
# Exclude the physical vorticity finite-core branch under endpoint regularity

The physical obstruction has now been reduced to a geometric alternative:

* a finite spatial cluster; or
* spatial escape.

The escape branch is already incompatible with the selected endpoint temporal
modulus for the fixed actual-vorticity component.

For the finite-cluster branch, no terminal value at the cluster point is
needed.  Selected spatial equicontinuity lets one compare the moving blowup
point with one fixed selected anchor at the same moving time.  The endpoint
temporal modulus then compares the value at that fixed anchor with its finite
actual terminal value.

Hence the moving physical-vorticity values remain bounded on the cluster
refinement, contradicting the existing oriented linear lower bound.

Thus endpoint temporal control together with selected spatial equicontinuity
eliminates both spatial branches.  This file isolates those two physical
regularity properties; it does not assert that they already follow from the
current H³ hypotheses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalMinimalVorticityPhysicalFiniteCoreExclusion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Selected spatial equicontinuity of one physical vorticity component -/

/--
Uniform spatial continuity of one fixed actual-vorticity component over all
selected times and all pairs of selected spatial points.
-/
def H3TerminalActualVorticitySelectedSpatialEquicontinuity
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (i : Fin 3)
    (τ : ℕ → ℝ)
    (z : ℕ → Point3) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ ρ : ℝ,
      0 < ρ
        ∧
      ∀ r m n : ℕ,
        dist (z m) (z n) < ρ →
        dist
          (h3NativeActualVorticityComponentAt
            u i (τ r) (z m))
          (h3NativeActualVorticityComponentAt
            u i (τ r) (z n))
          < ε

/--
The two physical regularity properties needed to control the geometric
terminal alternatives.
-/
def H3TerminalActualVorticitySelectedEndpointRegularity
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (i : Fin 3)
    (τ : ℕ → ℝ)
    (z : ℕ → Point3)
    (T : ℝ) : Prop :=
  H3TerminalActualVorticitySelectedEndpointTemporalModulus
      u i τ z T
    ∧
  H3TerminalActualVorticitySelectedSpatialEquicontinuity
      u i τ z

/-! ## Finite-core contradiction -/

/--
A finite selected spatial cluster is incompatible with the oriented linear
actual-vorticity lower bound once the fixed physical component has both
endpoint temporal control and selected spatial equicontinuity.

The argument uses one fixed selected anchor from the cluster refinement.  The
moving value stays uniformly close to that anchor at the same time, while the
anchor stays uniformly close to its finite terminal value.
-/
theorem terminal_minimalVorticityPhysical_finiteCluster_impossible_of_endpointTemporalModulus_of_spatialEquicontinuity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    {i : Fin 3}
    {s : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {z : ℕ → Point3}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hOrientedLower :
      ∀ n : ℕ,
        (n : ℝ) <
          h3TerminalOrientedValue
            s
            (h3NativeActualVorticityComponentAt
              u i (τ n) (z n)))
    (hFinite :
      H3TerminalSelectedPointHasFiniteCluster z)
    (hEndpoint :
      H3TerminalActualVorticitySelectedEndpointTemporalModulus
        u i τ z T)
    (hSpatialEquicontinuity :
      H3TerminalActualVorticitySelectedSpatialEquicontinuity
        u i τ z) :
    False := by

  obtain
    ⟨
      y,
      k,
      hkTop,
      hPoint
    ⟩ :=
    hFinite

  have hTime :
      Tendsto
        (fun j : ℕ => τ (k j))
        atTop
        (𝓝 T) :=
    hTau.comp
      hkTop

  obtain
    ⟨
      ρ,
      hρ,
      hSpatial
    ⟩ :=
    hSpatialEquicontinuity
      1
      zero_lt_one

  have hThirdRhoPos :
      0 < ρ / 3 := by
    linarith

  rw [Metric.tendsto_atTop] at hPoint

  obtain
    ⟨
      J₀,
      hNearPoint
    ⟩ :=
    hPoint
      (ρ / 3)
      hThirdRhoPos

  have hAnchorNear :
      dist
          (z (k J₀))
          y
        < ρ / 3 :=
    hNearPoint
      J₀
      le_rfl

  obtain
    ⟨
      η,
      hη,
      hEndpointUniform
    ⟩ :=
    hEndpoint
      1
      zero_lt_one

  rw [Metric.tendsto_atTop] at hTime

  obtain
    ⟨
      J₁,
      hNearTime
    ⟩ :=
    hTime
      η
      hη

  let C : ℝ :=
    h3NativeActualVorticityComponentAt
      u i
      T
      (z (k J₀))

  obtain
    ⟨
      N : ℕ,
      hN
    ⟩ :=
    exists_nat_gt
      (|C| + 2)

  have hIndexLarge :
      ∀ᶠ j : ℕ in atTop,
        N ≤ k j :=
    (
      tendsto_atTop.1
        hkTop
    )
      N

  obtain
    ⟨
      K,
      hK
    ⟩ :=
    eventually_atTop.1
      hIndexLarge

  let j : ℕ :=
    max J₀ (max J₁ K)

  have hJ₀j :
      J₀ ≤ j := by
    dsimp only [j]
    exact
      le_max_left
        J₀
        (max J₁ K)

  have hJ₁j :
      J₁ ≤ j := by
    dsimp only [j]
    exact
      le_trans
        (le_max_left J₁ K)
        (le_max_right J₀ (max J₁ K))

  have hKj :
      K ≤ j := by
    dsimp only [j]
    exact
      le_trans
        (le_max_right J₁ K)
        (le_max_right J₀ (max J₁ K))

  have hMovingNear :
      dist
          (z (k j))
          y
        < ρ / 3 :=
    hNearPoint
      j
      hJ₀j

  have hSpatialNear :
      dist
          (z (k j))
          (z (k J₀))
        < ρ := by

    have hTriangle :
        dist
            (z (k j))
            (z (k J₀))
          ≤
        dist
            (z (k j))
            y
          +
        dist
            y
            (z (k J₀)) :=
      dist_triangle
        (z (k j))
        y
        (z (k J₀))

    have hAnchorNear' :
        dist
            y
            (z (k J₀))
          < ρ / 3 := by
      simpa only [dist_comm] using
        hAnchorNear

    linarith

  have hTimeNear :
      dist
          (τ (k j))
          T
        < η :=
    hNearTime
      j
      hJ₁j

  let A : ℝ :=
    h3NativeActualVorticityComponentAt
      u i
      (τ (k j))
      (z (k j))

  let B : ℝ :=
    h3NativeActualVorticityComponentAt
      u i
      (τ (k j))
      (z (k J₀))

  have hAB :
      dist A B < 1 := by

    dsimp only [A, B]

    exact
      hSpatial
        (k j)
        (k j)
        (k J₀)
        hSpatialNear

  have hBC :
      dist B C < 1 := by

    dsimp only [B, C]

    exact
      hEndpointUniform
        (k J₀)
        (k j)
        hTimeNear

  have hTriangleOne :
      dist A 0
        ≤
      dist A B + dist B 0 :=
    dist_triangle
      A B 0

  have hTriangleTwo :
      dist B 0
        ≤
      dist B C + dist C 0 :=
    dist_triangle
      B C 0

  have hC0 :
      dist C 0 = |C| := by
    simp [Real.dist_eq]

  have hA0 :
      dist A 0 < |C| + 2 := by
    linarith

  have hAAbs :
      |A| < |C| + 2 := by
    simpa [Real.dist_eq] using
      hA0

  have hkN :
      N ≤ k j :=
    hK
      j
      hKj

  have hkNReal :
      (N : ℝ) ≤ (k j : ℝ) := by
    exact_mod_cast
      hkN

  have hLower :
      (k j : ℝ) <
        h3TerminalOrientedValue
          s
          A := by

    dsimp only [A]

    exact
      hOrientedLower
        (k j)

  have hOrientedLeAbs :
      h3TerminalOrientedValue
          s
          A
        ≤
      |A| := by

    cases s

    · simpa [h3TerminalOrientedValue] using
        (le_abs_self A)

    · simpa [h3TerminalOrientedValue] using
        (neg_le_abs A)

  linarith

/-!
## Both geometric branches are impossible under the physical endpoint package
-/

/--
Endpoint temporal control plus selected spatial equicontinuity eliminates the
entire finite-cluster versus spatial-infinity alternative for a physical
vorticity sequence with the oriented linear lower bound.

The finite branch uses only the two moduli.  The escape branch additionally
uses the strict-time H³ spatial-decay theorem proved previously.
-/
theorem terminal_minimalVorticityPhysical_spatialGeometry_impossible_of_endpointRegularity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    {i : Fin 3}
    {s : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {z : ℕ → Point3}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hOrientedLower :
      ∀ n : ℕ,
        (n : ℝ) <
          h3TerminalOrientedValue
            s
            (h3NativeActualVorticityComponentAt
              u i (τ n) (z n)))
    (hGeometry :
      H3TerminalSelectedPointHasFiniteCluster z
        ∨
      H3TerminalSelectedPointEscapesToInfinity z)
    (hRegularity :
      H3TerminalActualVorticitySelectedEndpointRegularity
        u i τ z T) :
    False := by

  rcases hGeometry with
    hFinite | hEscape

  · exact
      terminal_minimalVorticityPhysical_finiteCluster_impossible_of_endpointTemporalModulus_of_spatialEquicontinuity
        hTau
        hOrientedLower
        hFinite
        hRegularity.1
        hRegularity.2

  · exact
      terminal_minimalVorticityPhysical_spatialEscape_impossible_of_endpointTemporalModulus
        hH3
        hTauStrict
        hTau
        hOrientedLower
        hEscape
        hRegularity.1

end

end Euclidean
end Bridge
end PrimeTensor
