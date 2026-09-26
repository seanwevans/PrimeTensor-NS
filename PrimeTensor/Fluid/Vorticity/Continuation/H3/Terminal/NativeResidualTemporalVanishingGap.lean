import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualPersistentSpatialTemporalGap

/-!
# Vanishing-time temporal obstruction for the terminal residual

The persistent spatial-or-temporal split isolates two possible mechanisms for
failure of the full canonical native residual factor.

The temporal branch can be sharpened further without any new PDE estimate.

On every terminal sequence used in the continuation argument,

    τ n → T.

Therefore every two cofinal refinements `τ (k₁ j)` and `τ (k₂ j)` also tend to
`T`, and their mutual time distance tends to zero.

Consequently, a persistent same-point temporal complementary-gradient gap is
not merely a temporal mismatch: it is a fixed positive value gap across time
increments whose lengths vanish.

This is exactly the failure mode that any uniform-in-space terminal temporal
modulus would have to exclude.

No such modulus is assumed or manufactured here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Generic cofinal terminal-time synchronization -/

/--
Two cofinal refinements of a sequence converging to the same real terminal
time have mutual time distance tending to zero.
-/
theorem terminalCofinalTimes_dist_tendsto_zero
    {τ : ℕ → ℝ}
    {T : ℝ}
    {k₁ k₂ : ℕ → ℕ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hk₁ :
      Tendsto k₁ atTop atTop)
    (hk₂ :
      Tendsto k₂ atTop atTop) :
    Tendsto
      (
        fun j : ℕ =>
          dist
            (τ (k₁ j))
            (τ (k₂ j))
      )
      atTop
      (𝓝 0) := by

  have h₁ :
      Tendsto
        (fun j : ℕ => τ (k₁ j))
        atTop
        (𝓝 T) :=
    hTau.comp hk₁

  have h₂ :
      Tendsto
        (fun j : ℕ => τ (k₂ j))
        atTop
        (𝓝 T) :=
    hTau.comp hk₂

  simpa using
    h₁.dist h₂

/-! ## Vanishing-time temporal gap -/

/--
A fixed positive complementary-gradient value gap at one moving spatial point,
while the two compared times approach each other.
-/
def H3TerminalComplementGradientPersistentTemporalVanishingTimeGap
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
      Tendsto
        (
          fun j : ℕ =>
            dist
              (τ (k₁ j))
              (τ (k₂ j))
        )
        atTop
        (𝓝 0)
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

/--
On a terminal time sequence, every persistent temporal cofinal gap
automatically has vanishing time separation.
-/
theorem persistentTemporalVanishingTimeGap_of_persistentTemporalGap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hTemporal :
      H3TerminalComplementGradientPersistentTemporalCofinalGap
        u p τ x) :
    H3TerminalComplementGradientPersistentTemporalVanishingTimeGap
      u p τ x := by

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
    hTemporal

  have hTime :
      Tendsto
        (
          fun j : ℕ =>
            dist
              (τ (k₁ j))
              (τ (k₂ j))
        )
        atTop
        (𝓝 0) :=
    terminalCofinalTimes_dist_tendsto_zero
      hTau
      hk₁Top
      hk₂Top

  exact
    ⟨
      δ,
      hδ,
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      hTime,
      hGap
    ⟩

/-! ## Refined failure alternative -/

/--
For a terminal time sequence, failure of the full canonical native factor
forces either

* a persistent same-time spatial complementary-gradient gap; or
* a persistent same-point temporal complementary-gradient gap occurring across
  vanishing time increments.

Thus the temporal branch is identified explicitly as a failure of a uniform
terminal temporal modulus along the moving selected spatial points.
-/
theorem not_nativeComplementHasCanonicalFactor_forces_persistentSpatial_or_temporalVanishingTimeGap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x) :
    H3TerminalComplementGradientPersistentSpatialCofinalGap
        u p τ x
      ∨
    H3TerminalComplementGradientPersistentTemporalVanishingTimeGap
        u p τ x := by

  rcases
    not_nativeComplementHasCanonicalFactor_forces_persistentSpatial_or_temporalGap
      hNoFactor
    with
    hSpatial | hTemporal

  · exact
      Or.inl hSpatial

  · exact
      Or.inr
        (
          persistentTemporalVanishingTimeGap_of_persistentTemporalGap
            hTau
            hTemporal
        )

/-! ## Uniform temporal modulus frontier -/

/--
A uniform terminal temporal modulus on the selected spatial points is exactly
the kind of estimate that excludes the vanishing-time temporal obstruction.
This proposition is kept separate from the existing preterminal separate
continuity statements.
-/
def H3TerminalComplementGradientSelectedTemporalUniformModulus
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
        dist (τ m) (τ n) < η →
        dist
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ m)
              (x n)
          )
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ n)
              (x n)
          )
          < ε

/--
The selected uniform temporal modulus rules out a persistent temporal gap
across vanishing time increments.
-/
theorem not_persistentTemporalVanishingTimeGap_of_selectedTemporalUniformModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hModulus :
      H3TerminalComplementGradientSelectedTemporalUniformModulus
        u p τ x) :
    ¬
      H3TerminalComplementGradientPersistentTemporalVanishingTimeGap
        u p τ x := by

  rintro
    ⟨
      δ,
      hδ,
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      hTime,
      hGap
    ⟩

  obtain
    ⟨
      η,
      hη,
      hUniform
    ⟩ :=
    hModulus
      δ
      hδ

  have hEventuallyTime :
      ∀ᶠ j : ℕ in atTop,
        dist
          (τ (k₁ j))
          (τ (k₂ j))
          < η := by

    exact
      hTime.eventually_lt
        tendsto_const_nhds
        hη

  rw [eventually_atTop] at hEventuallyTime

  obtain
    ⟨
      J,
      hJ
    ⟩ :=
    hEventuallyTime

  have hSmall :
      dist
        (
          h3TerminalComplementGradientFieldForPair
            u p
            (τ (k₁ J))
            (x (k₂ J))
        )
        (
          h3TerminalComplementGradientFieldForPair
            u p
            (τ (k₂ J))
            (x (k₂ J))
        )
        < δ :=
    hUniform
      (k₁ J)
      (k₂ J)
      (hJ J le_rfl)

  exact
    (
      not_lt_of_ge
        (hGap J)
    )
      hSmall

/--
If a selected uniform temporal modulus is available, failure of the canonical
factor can only persist through the spatial branch.
-/
theorem persistentSpatialGap_of_noCanonicalFactor_of_selectedTemporalUniformModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hModulus :
      H3TerminalComplementGradientSelectedTemporalUniformModulus
        u p τ x)
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x) :
    H3TerminalComplementGradientPersistentSpatialCofinalGap
      u p τ x := by

  rcases
    not_nativeComplementHasCanonicalFactor_forces_persistentSpatial_or_temporalVanishingTimeGap
      hTau
      hNoFactor
    with
    hSpatial | hTemporal

  · exact hSpatial

  · exact
      False.elim
        (
          not_persistentTemporalVanishingTimeGap_of_selectedTemporalUniformModulus
            hModulus
            hTemporal
        )

end

end Euclidean
end Bridge
end PrimeTensor
