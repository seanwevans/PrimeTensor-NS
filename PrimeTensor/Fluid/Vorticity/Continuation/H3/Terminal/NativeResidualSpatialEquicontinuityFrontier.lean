import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSpatialClusterProfiles

/-!
# Spatial equicontinuity frontier and fixed terminal anchor pair

The bounded noncanonical branch now supplies two distinct finite spatial
cluster profiles and a fixed positive same-time complementary-gradient gap.

The previously defined selected spatial modulus is intentionally asymmetric:
at time `τ m` it compares the distinguished point `x m` only with another
selected point `x n`.  That is enough to convert a derivative gap into point
separation, but it is not enough to freeze both moving spatial profiles.

The missing analytic property is spatial equicontinuity over the selected
time family.

This file packages the exact three-index modulus:

    for every epsilon,
    one spatial radius works for every selected time `τ r`
    and every pair of selected points `x m`, `x n`.

Under that modulus, convergence of the two spatial cluster profiles allows both
moving points to be replaced by fixed late selected anchors, while retaining a
positive fraction of the original derivative gap.

Thus the bounded noncanonical branch reduces to a fixed pair of spatial points
whose complementary-gradient values remain separated along times tending to
the terminal time.

No claim is made here that preterminal H³ regularity already supplies this
uniform equicontinuity up to the terminal time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualSpatialEquicontinuityFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Three-index selected spatial equicontinuity -/

/--
Uniform spatial continuity of the complementary first derivative over all
selected times and all pairs of selected spatial points.

The time index `r` is independent of the two spatial indices `m,n`.
-/
def H3TerminalComplementGradientSelectedSpatialEquicontinuity
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ η : ℝ,
      0 < η
        ∧
      ∀ r m n : ℕ,
        dist (x m) (x n) < η →
        dist
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ r)
              (x m)
          )
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ r)
              (x n)
          )
          < ε

/--
The three-index equicontinuity property implies the earlier diagonal selected
spatial modulus.
-/
theorem selectedSpatialUniformModulus_of_selectedSpatialEquicontinuity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hEquicontinuous :
      H3TerminalComplementGradientSelectedSpatialEquicontinuity
        u p τ x) :
    H3TerminalComplementGradientSelectedSpatialUniformModulus
      u p τ x := by

  intro ε hε

  obtain
    ⟨
      η,
      hη,
      hUniform
    ⟩ :=
    hEquicontinuous
      ε
      hε

  exact
    ⟨
      η,
      hη,
      fun m n hmn =>
        hUniform
          m
          m
          n
          hmn
    ⟩

/-! ## Fixed terminal spatial pair -/

/--
Two fixed selected spatial points retain a fixed positive
complementary-gradient gap along a cofinal selected time refinement converging
to the terminal time.
-/
def H3TerminalComplementGradientHasFixedSelectedSpatialPairGapAtTerminal
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ a b : ℕ,
      ∃ k : ℕ → ℕ,
        Tendsto k atTop atTop
          ∧
        Tendsto
          (fun j : ℕ => τ (k j))
          atTop
          (𝓝 T)
          ∧
        ∀ᶠ j : ℕ in atTop,
          δ
            ≤
          dist
            (
              h3TerminalComplementGradientFieldForPair
                u p
                (τ (k j))
                (x a)
            )
            (
              h3TerminalComplementGradientFieldForPair
                u p
                (τ (k j))
                (x b)
            )

/-! ## Freeze both moving cluster profiles -/

/--
Spatial equicontinuity upgrades two moving finite cluster profiles to a fixed
selected spatial pair while preserving half of the original derivative gap.
-/
theorem fixedSelectedSpatialPairGapAtTerminal_of_clusterProfiles_of_spatialEquicontinuity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hEquicontinuous :
      H3TerminalComplementGradientSelectedSpatialEquicontinuity
        u p τ x)
    (hProfiles :
      H3TerminalComplementGradientHasTwoDistinctSpatialClusterProfiles
        u p τ x T) :
    H3TerminalComplementGradientHasFixedSelectedSpatialPairGapAtTerminal
      u p τ x T := by

  obtain
    ⟨
      δ,
      hδ,
      y₁,
      y₂,
      _hyNe,
      k₁,
      k₂,
      hk₁Top,
      _hk₂Top,
      hTime₁,
      _hTime₂,
      hPoint₁,
      hPoint₂,
      hGap
    ⟩ :=
    hProfiles

  have hQuarterPos :
      0 < δ / 4 := by
    linarith

  obtain
    ⟨
      η,
      hη,
      hUniform
    ⟩ :=
    hEquicontinuous
      (δ / 4)
      hQuarterPos

  have hEtaQuarterPos :
      0 < η / 4 := by
    linarith

  rw [Metric.tendsto_atTop] at hPoint₁
  rw [Metric.tendsto_atTop] at hPoint₂

  obtain
    ⟨
      N₁,
      hN₁
    ⟩ :=
    hPoint₁
      (η / 4)
      hEtaQuarterPos

  obtain
    ⟨
      N₂,
      hN₂
    ⟩ :=
    hPoint₂
      (η / 4)
      hEtaQuarterPos

  let J : ℕ :=
    max N₁ N₂

  have hN₁J :
      N₁ ≤ J := by
    exact
      le_max_left
        N₁ N₂

  have hN₂J :
      N₂ ≤ J := by
    exact
      le_max_right
        N₁ N₂

  let a : ℕ :=
    k₁ J

  let b : ℕ :=
    k₂ J

  have hAnchor₁ :
      dist
          (x a)
          y₁
        < η / 4 := by

    dsimp only [a]

    exact
      hN₁
        J
        hN₁J

  have hAnchor₂ :
      dist
          (x b)
          y₂
        < η / 4 := by

    dsimp only [b]

    exact
      hN₂
        J
        hN₂J

  have hEventuallyAnchorGap :
      ∀ᶠ j : ℕ in atTop,
        δ / 2
          ≤
        dist
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ (k₁ j))
              (x a)
          )
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ (k₁ j))
              (x b)
          ) := by

    filter_upwards
      [eventually_ge_atTop J]
      with j hj

    have hMove₁ :
        dist
            (x (k₁ j))
            y₁
          < η / 4 :=
      hN₁
        j
        (le_trans hN₁J hj)

    have hMove₂ :
        dist
            (x (k₂ j))
            y₂
          < η / 4 :=
      hN₂
        j
        (le_trans hN₂J hj)

    have hNear₁ :
        dist
            (x (k₁ j))
            (x a)
          < η := by

      have hTri :
          dist
              (x (k₁ j))
              (x a)
            ≤
          dist
              (x (k₁ j))
              y₁
            +
          dist
              y₁
              (x a) :=
        dist_triangle
          (x (k₁ j))
          y₁
          (x a)

      have hAnchor₁' :
          dist
              y₁
              (x a)
            < η / 4 := by

        simpa only [dist_comm] using
          hAnchor₁

      linarith

    have hNear₂ :
        dist
            (x (k₂ j))
            (x b)
          < η := by

      have hTri :
          dist
              (x (k₂ j))
              (x b)
            ≤
          dist
              (x (k₂ j))
              y₂
            +
          dist
              y₂
              (x b) :=
        dist_triangle
          (x (k₂ j))
          y₂
          (x b)

      have hAnchor₂' :
          dist
              y₂
              (x b)
            < η / 4 := by

        simpa only [dist_comm] using
          hAnchor₂

      linarith

    let A : ℝ :=
      h3TerminalComplementGradientFieldForPair
        u p
        (τ (k₁ j))
        (x (k₁ j))

    let A₀ : ℝ :=
      h3TerminalComplementGradientFieldForPair
        u p
        (τ (k₁ j))
        (x a)

    let B : ℝ :=
      h3TerminalComplementGradientFieldForPair
        u p
        (τ (k₁ j))
        (x (k₂ j))

    let B₀ : ℝ :=
      h3TerminalComplementGradientFieldForPair
        u p
        (τ (k₁ j))
        (x b)

    have hErr₁ :
        dist A A₀ < δ / 4 := by

      dsimp only [A, A₀]

      exact
        hUniform
          (k₁ j)
          (k₁ j)
          a
          hNear₁

    have hErr₂ :
        dist B B₀ < δ / 4 := by

      dsimp only [B, B₀]

      exact
        hUniform
          (k₁ j)
          (k₂ j)
          b
          hNear₂

    have hOriginal :
        δ ≤ dist A B := by

      dsimp only [A, B]

      exact
        hGap j

    have hTriangleOne :
        dist A B
          ≤
        dist A A₀
          +
        dist A₀ B :=
      dist_triangle
        A A₀ B

    have hTriangleTwo :
        dist A₀ B
          ≤
        dist A₀ B₀
          +
        dist B₀ B :=
      dist_triangle
        A₀ B₀ B

    have hErr₂' :
        dist B₀ B < δ / 4 := by

      simpa only [dist_comm] using
        hErr₂

    have hCombined :
        dist A B
          ≤
        dist A A₀
          +
        dist A₀ B₀
          +
        dist B₀ B := by

      linarith

    have hFixed :
        δ / 2
          ≤
        dist A₀ B₀ := by

      linarith

    simpa only [A₀, B₀] using
      hFixed

  exact
    ⟨
      δ / 2,
      half_pos hδ,
      a,
      b,
      k₁,
      hk₁Top,
      hTime₁,
      hEventuallyAnchorGap
    ⟩

/-! ## Noncanonical bounded branch with equicontinuity -/

/--
Under both selected temporal control and the stronger spatial equicontinuity
frontier, a bounded noncanonical residual branch contains a fixed selected
spatial pair whose complementary-gradient values remain positively separated
along times tending to `T`.
-/
theorem fixedSelectedSpatialPairGapAtTerminal_of_noCanonicalFactor_of_equicontinuity_of_bounded
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
    (hSpatialEquicontinuity :
      H3TerminalComplementGradientSelectedSpatialEquicontinuity
        u p τ x)
    (hBounded :
      Bornology.IsBounded (Set.range x))
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x) :
    H3TerminalComplementGradientHasFixedSelectedSpatialPairGapAtTerminal
      u p τ x T := by

  have hSpatialModulus :
      H3TerminalComplementGradientSelectedSpatialUniformModulus
        u p τ x :=
    selectedSpatialUniformModulus_of_selectedSpatialEquicontinuity
      hSpatialEquicontinuity

  have hProfiles :
      H3TerminalComplementGradientHasTwoDistinctSpatialClusterProfiles
        u p τ x T :=
    complementGradientHasTwoDistinctSpatialClusterProfiles_of_noCanonicalFactor_of_uniformModuli_of_bounded
      hTau
      hTemporalModulus
      hSpatialModulus
      hBounded
      hNoFactor

  exact
    fixedSelectedSpatialPairGapAtTerminal_of_clusterProfiles_of_spatialEquicontinuity
      hSpatialEquicontinuity
      hProfiles

end

end Euclidean
end Bridge
end PrimeTensor
