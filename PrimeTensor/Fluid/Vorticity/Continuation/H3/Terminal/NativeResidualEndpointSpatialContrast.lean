import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualTemporalEquicontinuityFrontier

/-!
# Endpoint temporal modulus and terminal spatial contrast

The bounded noncanonical branch has been reduced to fixed selected spatial
anchors carrying a persistent complementary-gradient gap.

A full three-index temporal equicontinuity modulus is sufficient to construct
finite fixed-anchor limits, but it is stronger than what is needed to identify
the actual terminal obstruction.

The exact endpoint property is:

    whenever a selected time `τ n` approaches `T`,
    the complementary gradient at every selected spatial point `x r`
    approaches its actual value at time `T`,
    with one temporal modulus uniform in `r`.

This endpoint modulus has two consequences.

First, together with `τ n → T`, it directly excludes the persistent
same-point temporal vanishing-gap branch.  No global temporal equicontinuity
between arbitrary selected times is needed.

Second, once spatial equicontinuity freezes the bounded spatial branch to two
fixed selected anchors, the persistent late-time gap passes to the actual
terminal values at those anchors.

Thus, under bounded spatial selection, spatial equicontinuity, and the endpoint
temporal modulus, failure of the canonical native factor forces a genuine
positive spatial contrast of the complementary first derivative at time `T`.

This is a classification, not a contradiction: a nonconstant terminal
derivative field may have such a contrast.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Uniform endpoint temporal modulus -/

/--
Uniform convergence in time to the actual terminal complementary-gradient
value over the selected spatial family.
-/
def H3TerminalComplementGradientSelectedEndpointTemporalModulus
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ η : ℝ,
      0 < η
        ∧
      ∀ r n : ℕ,
        dist (τ n) T < η →
        dist
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ n)
              (x r)
          )
          (
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x r)
          )
          < ε

/--
The endpoint temporal modulus identifies the limit at every fixed selected
anchor along every cofinal selected terminal-time refinement.
-/
theorem fixedSelectedAnchor_tendsto_terminalValue_of_endpointTemporalModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    {k : ℕ → ℕ}
    (hEndpoint :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u p τ x T)
    (hTime :
      Tendsto
        (fun j : ℕ => τ (k j))
        atTop
        (𝓝 T))
    (r : ℕ) :
    Tendsto
      (
        fun j : ℕ =>
          h3TerminalComplementGradientFieldForPair
            u p
            (τ (k j))
            (x r)
      )
      atTop
      (
        𝓝
          (
            h3TerminalComplementGradientFieldForPair
              u p
              T
              (x r)
          )
      ) := by

  rw [Metric.tendsto_atTop]

  intro ε hε

  obtain
    ⟨
      η,
      hη,
      hUniform
    ⟩ :=
    hEndpoint
      ε
      hε

  rw [Metric.tendsto_atTop] at hTime

  obtain
    ⟨
      N,
      hN
    ⟩ :=
    hTime
      η
      hη

  refine
    ⟨
      N,
      ?_
    ⟩

  intro j hj

  exact
    hUniform
      r
      (k j)
      (hN j hj)

/-! ## Endpoint control excludes the temporal obstruction -/

/--
Terminal-time convergence plus the uniform endpoint temporal modulus rules out
a persistent same-point value gap across vanishing terminal time increments.
-/
theorem not_persistentTemporalVanishingTimeGap_of_endpointTemporalModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hEndpoint :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u p τ x T) :
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
      _hTimeDistance,
      hGap
    ⟩

  have hThirdPos :
      0 < δ / 3 := by
    linarith

  obtain
    ⟨
      η,
      hη,
      hUniform
    ⟩ :=
    hEndpoint
      (δ / 3)
      hThirdPos

  have hTime₁ :
      Tendsto
        (fun j : ℕ => τ (k₁ j))
        atTop
        (𝓝 T) :=
    hTau.comp
      hk₁Top

  have hTime₂ :
      Tendsto
        (fun j : ℕ => τ (k₂ j))
        atTop
        (𝓝 T) :=
    hTau.comp
      hk₂Top

  rw [Metric.tendsto_atTop] at hTime₁
  rw [Metric.tendsto_atTop] at hTime₂

  obtain
    ⟨
      N₁,
      hN₁
    ⟩ :=
    hTime₁
      η
      hη

  obtain
    ⟨
      N₂,
      hN₂
    ⟩ :=
    hTime₂
      η
      hη

  let J : ℕ :=
    max N₁ N₂

  have hN₁J :
      N₁ ≤ J :=
    le_max_left
      N₁ N₂

  have hN₂J :
      N₂ ≤ J :=
    le_max_right
      N₁ N₂

  have hNearTime₁ :
      dist
          (τ (k₁ J))
          T
        < η :=
    hN₁
      J
      hN₁J

  have hNearTime₂ :
      dist
          (τ (k₂ J))
          T
        < η :=
    hN₂
      J
      hN₂J

  let A : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      (τ (k₁ J))
      (x (k₂ J))

  let B : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      (τ (k₂ J))
      (x (k₂ J))

  let C : ℝ :=
    h3TerminalComplementGradientFieldForPair
      u p
      T
      (x (k₂ J))

  have hAC :
      dist A C < δ / 3 := by

    dsimp only [A, C]

    exact
      hUniform
        (k₂ J)
        (k₁ J)
        hNearTime₁

  have hBC :
      dist B C < δ / 3 := by

    dsimp only [B, C]

    exact
      hUniform
        (k₂ J)
        (k₂ J)
        hNearTime₂

  have hCB :
      dist C B < δ / 3 := by

    simpa only [dist_comm] using
      hBC

  have hTriangle :
      dist A B
        ≤
      dist A C + dist C B :=
    dist_triangle
      A C B

  have hLarge :
      δ ≤ dist A B := by

    dsimp only [A, B]

    exact
      hGap J

  linarith

/--
With endpoint temporal control, failure of the canonical factor must persist
through the spatial branch.
-/
theorem persistentSpatialGap_of_noCanonicalFactor_of_endpointTemporalModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hEndpoint :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u p τ x T)
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
          not_persistentTemporalVanishingTimeGap_of_endpointTemporalModulus
            hTau
            hEndpoint
            hTemporal
        )

/-! ## Actual terminal spatial contrast -/

/--
The actual complementary-gradient field at time `T` has a positive gap between
two fixed selected spatial anchors.
-/
def H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrast
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ a b : ℕ,
      a ≠ b
        ∧
      δ
        ≤
      dist
        (
          h3TerminalComplementGradientFieldForPair
            u p
            T
            (x a)
        )
        (
          h3TerminalComplementGradientFieldForPair
            u p
            T
            (x b)
        )

/--
A fixed late-time anchor gap passes to the actual terminal field under the
endpoint temporal modulus.
-/
theorem positiveSelectedTerminalSpatialContrast_of_fixedPairGap_of_endpointTemporalModulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hEndpoint :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u p τ x T)
    (hFixedGap :
      H3TerminalComplementGradientHasFixedSelectedSpatialPairGapAtTerminal
        u p τ x T) :
    H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrast
      u p x T := by

  obtain
    ⟨
      δ,
      hδ,
      a,
      b,
      k,
      _hkTop,
      hTime,
      hGap
    ⟩ :=
    hFixedGap

  have hA :
      Tendsto
        (
          fun j : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u p
              (τ (k j))
              (x a)
        )
        atTop
        (
          𝓝
            (
              h3TerminalComplementGradientFieldForPair
                u p
                T
                (x a)
            )
        ) :=
    fixedSelectedAnchor_tendsto_terminalValue_of_endpointTemporalModulus
      hEndpoint
      hTime
      a

  have hB :
      Tendsto
        (
          fun j : ℕ =>
            h3TerminalComplementGradientFieldForPair
              u p
              (τ (k j))
              (x b)
        )
        atTop
        (
          𝓝
            (
              h3TerminalComplementGradientFieldForPair
                u p
                T
                (x b)
            )
        ) :=
    fixedSelectedAnchor_tendsto_terminalValue_of_endpointTemporalModulus
      hEndpoint
      hTime
      b

  have hDistance :
      Tendsto
        (
          fun j : ℕ =>
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
        )
        atTop
        (
          𝓝
            (
              dist
                (
                  h3TerminalComplementGradientFieldForPair
                    u p
                    T
                    (x a)
                )
                (
                  h3TerminalComplementGradientFieldForPair
                    u p
                    T
                    (x b)
                )
            )
        ) :=
    hA.dist
      hB

  have hTerminalGap :
      δ
        ≤
      dist
        (
          h3TerminalComplementGradientFieldForPair
            u p
            T
            (x a)
        )
        (
          h3TerminalComplementGradientFieldForPair
            u p
            T
            (x b)
        ) := by

    apply
      ge_of_tendsto
        hDistance

    exact
      hGap

  have hab :
      a ≠ b := by

    intro habEq

    have hδZero :
        δ ≤ 0 := by

      simpa [habEq] using
        hTerminalGap

    linarith

  exact
    ⟨
      δ,
      hδ,
      a,
      b,
      hab,
      hTerminalGap
    ⟩

/-! ## Bounded noncanonical branch at the actual terminal field -/

/--
Under terminal-time convergence, bounded selected points, spatial
equicontinuity, and the endpoint temporal modulus, failure of the canonical
native residual factor forces a positive spatial contrast in the actual
terminal complementary-gradient field.

This conclusion is descriptive: such a spatial contrast is not ruled out by
continuity or H³ regularity alone.
-/
theorem positiveSelectedTerminalSpatialContrast_of_noCanonicalFactor_of_endpointModulus_of_spatialEquicontinuity_of_bounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hEndpoint :
      H3TerminalComplementGradientSelectedEndpointTemporalModulus
        u p τ x T)
    (hSpatialEquicontinuity :
      H3TerminalComplementGradientSelectedSpatialEquicontinuity
        u p τ x)
    (hBounded :
      Bornology.IsBounded (Set.range x))
    (hNoFactor :
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x) :
    H3TerminalComplementGradientHasPositiveSelectedTerminalSpatialContrast
      u p x T := by

  have hSpatial :
      H3TerminalComplementGradientPersistentSpatialCofinalGap
        u p τ x :=
    persistentSpatialGap_of_noCanonicalFactor_of_endpointTemporalModulus
      hTau
      hEndpoint
      hNoFactor

  have hSpatialModulus :
      H3TerminalComplementGradientSelectedSpatialUniformModulus
        u p τ x :=
    selectedSpatialUniformModulus_of_selectedSpatialEquicontinuity
      hSpatialEquicontinuity

  have hProfiles :
      H3TerminalComplementGradientHasTwoDistinctSpatialClusterProfiles
        u p τ x T :=
    complementGradientHasTwoDistinctSpatialClusterProfiles_of_bounded_of_persistentSpatialGap
      hTau
      hBounded
      hSpatialModulus
      hSpatial

  have hFixedGap :
      H3TerminalComplementGradientHasFixedSelectedSpatialPairGapAtTerminal
        u p τ x T :=
    fixedSelectedSpatialPairGapAtTerminal_of_clusterProfiles_of_spatialEquicontinuity
      hSpatialEquicontinuity
      hProfiles

  exact
    positiveSelectedTerminalSpatialContrast_of_fixedPairGap_of_endpointTemporalModulus
      hEndpoint
      hFixedGap

end

end Euclidean
end Bridge
end PrimeTensor
