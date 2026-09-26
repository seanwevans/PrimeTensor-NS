import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualPhysicalSynchronization

/-!
# Spatial / temporal splitting of terminal residual synchronization

The native residual frontier is now identified exactly with the ordinary real
complementary first derivative

    F(t,x) = h3TerminalComplementGradientFieldForPair u p t x.

For two cofinal refinements `k₁,k₂` of one selected terminal sequence, insert
the mixed spacetime point

    (τ (k₁ j), x (k₂ j)).

Then the residual mismatch splits by the triangle inequality into

    same-time spatial mismatch
      +
    same-point temporal mismatch.

This file packages those two mechanisms separately.

If both mismatches tend to zero for every two cofinal refinements, then the
physical complementary derivative synchronizes, hence the residual logarithm
is Cauchy, hence the full canonical native factor exists.

Conversely, any positive cofinal residual gap forces at each synchronized
index at least one of the spatial or temporal legs to carry at least half of
that gap.

This is a neutral reduction.  No spatial localization of the selected points,
joint terminal continuity, or quantitative PDE modulus is assumed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Two synchronization mechanisms -/

/--
For every two cofinal refinements, compare their selected spatial points at the
time of the first refinement.  The same-time complementary-gradient mismatch
tends to zero.
-/
def H3TerminalComplementGradientCofinalSpatialSynchronization
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
      )
      atTop
      (𝓝 0)

/--
For every two cofinal refinements, hold the second selected spatial point fixed
inside each synchronized index and compare the two selected times.  The
same-point temporal complementary-gradient mismatch tends to zero.
-/
def H3TerminalComplementGradientCofinalTemporalSynchronization
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
      )
      atTop
      (𝓝 0)

/-! ## Triangle bridge -/

/--
Spatial synchronization plus temporal synchronization implies full physical
cofinal synchronization of the complementary derivative.
-/
theorem complementGradientCofinalSynchronization_of_spatial_of_temporal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hSpatial :
      H3TerminalComplementGradientCofinalSpatialSynchronization
        u p τ x)
    (hTemporal :
      H3TerminalComplementGradientCofinalTemporalSynchronization
        u p τ x) :
    H3TerminalComplementGradientCofinalSynchronization
      u p τ x := by

  intro k₁ k₂ hk₁Top hk₂Top

  let F : ℝ → Point3 → ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p

  have hS :
      Tendsto
        (
          fun j : ℕ =>
            dist
              (F (τ (k₁ j)) (x (k₁ j)))
              (F (τ (k₁ j)) (x (k₂ j)))
        )
        atTop
        (𝓝 0) := by

    simpa only [F] using
      hSpatial
        k₁ k₂
        hk₁Top hk₂Top

  have hT :
      Tendsto
        (
          fun j : ℕ =>
            dist
              (F (τ (k₁ j)) (x (k₂ j)))
              (F (τ (k₂ j)) (x (k₂ j)))
        )
        atTop
        (𝓝 0) := by

    simpa only [F] using
      hTemporal
        k₁ k₂
        hk₁Top hk₂Top

  have hSum :
      Tendsto
        (
          fun j : ℕ =>
            dist
              (F (τ (k₁ j)) (x (k₁ j)))
              (F (τ (k₁ j)) (x (k₂ j)))
              +
            dist
              (F (τ (k₁ j)) (x (k₂ j)))
              (F (τ (k₂ j)) (x (k₂ j)))
        )
        atTop
        (𝓝 0) := by

    simpa only [zero_add] using
      hS.add hT

  have hNonneg :
      ∀ᶠ j : ℕ in atTop,
        0
          ≤
        dist
          (F (τ (k₁ j)) (x (k₁ j)))
          (F (τ (k₂ j)) (x (k₂ j))) :=
    Filter.Eventually.of_forall
      (fun _ => dist_nonneg)

  have hTriangle :
      ∀ᶠ j : ℕ in atTop,
        dist
            (F (τ (k₁ j)) (x (k₁ j)))
            (F (τ (k₂ j)) (x (k₂ j)))
          ≤
        dist
            (F (τ (k₁ j)) (x (k₁ j)))
            (F (τ (k₁ j)) (x (k₂ j)))
          +
        dist
            (F (τ (k₁ j)) (x (k₂ j)))
            (F (τ (k₂ j)) (x (k₂ j))) :=
    Filter.Eventually.of_forall
      (fun j =>
        dist_triangle
          (F (τ (k₁ j)) (x (k₁ j)))
          (F (τ (k₁ j)) (x (k₂ j)))
          (F (τ (k₂ j)) (x (k₂ j))))

  simpa only [F] using
    squeeze_zero'
      hNonneg
      hTriangle
      hSum

/--
The two synchronization mechanisms are a sufficient PDE-side criterion for
the full canonical native residual factor.
-/
theorem nativeComplementHasCanonicalFactor_of_spatial_of_temporalSynchronization
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hSpatial :
      H3TerminalComplementGradientCofinalSpatialSynchronization
        u p τ x)
    (hTemporal :
      H3TerminalComplementGradientCofinalTemporalSynchronization
        u p τ x) :
    H3TerminalNativeComplementHasCanonicalFactor
      u p τ x := by

  apply
    (
      nativeComplementHasCanonicalFactor_iff_complementGradientCofinalSynchronization
        u p τ x
    ).2

  exact
    complementGradientCofinalSynchronization_of_spatial_of_temporal
      hSpatial
      hTemporal

/-! ## Positive gap splitting -/

/--
A positive full complementary-gradient gap forces at least half of that gap
onto either the same-time spatial leg or the same-point temporal leg at each
synchronized index.
-/
theorem complementGradientCofinalGap_split_spatial_temporal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hGap :
      H3TerminalComplementGradientCofinalGap
        u p τ x) :
    ∃ ε : ℝ,
      0 < ε
        ∧
      ∃ k₁ k₂ : ℕ → ℕ,
        Tendsto k₁ atTop atTop
          ∧
        Tendsto k₂ atTop atTop
          ∧
        ∀ j : ℕ,
          (
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
          )
            ∨
          (
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
          ) := by

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
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      ?_
    ⟩

  intro j

  let A : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      (τ (k₁ j))
      (x (k₁ j))

  let B : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      (τ (k₁ j))
      (x (k₂ j))

  let C : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      (τ (k₂ j))
      (x (k₂ j))

  have hFull :
      ε ≤ dist A C := by

    simpa only [A, C] using
      hGap j

  have hTri :
      dist A C
        ≤
      dist A B + dist B C :=
    dist_triangle
      A B C

  by_cases hSpatial :
      ε / 2 ≤ dist A B

  · exact
      Or.inl
        (
          by
            simpa only [A, B] using hSpatial
        )

  · have hSpatialLt :
        dist A B < ε / 2 :=
      lt_of_not_ge
        hSpatial

    have hTemporal :
        ε / 2 ≤ dist B C := by
      linarith

    exact
      Or.inr
        (
          by
            simpa only [B, C] using hTemporal
        )

/--
Failure of the full canonical native factor therefore produces two cofinal
refinements on which, at every synchronized index, either the spatial leg or
the temporal leg carries a fixed positive half-gap.
-/
theorem not_nativeComplementHasCanonicalFactor_split_spatial_temporal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x) :
    ∃ ε : ℝ,
      0 < ε
        ∧
      ∃ k₁ k₂ : ℕ → ℕ,
        Tendsto k₁ atTop atTop
          ∧
        Tendsto k₂ atTop atTop
          ∧
        ∀ j : ℕ,
          (
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
          )
            ∨
          (
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
          ) := by

  have hGap :
      H3TerminalComplementGradientCofinalGap
        u p τ x :=
    (
      not_nativeComplementHasCanonicalFactor_iff_complementGradientCofinalGap
        u p τ x
    ).1 hNoFactor

  exact
    complementGradientCofinalGap_split_spatial_temporal
      hGap

end

end Euclidean
end Bridge
end PrimeTensor
