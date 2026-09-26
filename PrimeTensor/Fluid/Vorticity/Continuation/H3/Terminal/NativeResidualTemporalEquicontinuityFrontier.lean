import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSpatialEquicontinuityFrontier

/-!
# Temporal equicontinuity frontier and fixed-anchor terminal limits

The bounded noncanonical branch has now been reduced, under spatial
equicontinuity, to two fixed selected spatial anchors whose complementary
gradient values remain separated along a cofinal time sequence converging to
the terminal time.

The previously defined selected temporal modulus is still diagonal: it compares

    F(τ m, x n)  and  F(τ n, x n),

so the spatial point is tied to one of the two time indices.

To obtain an actual terminal limit at a fixed selected spatial anchor, the
needed property is the temporal analogue of spatial equicontinuity:

    one temporal modulus works for every selected spatial point `x r`,
    independently of the two time indices `m,n`.

Under this three-index temporal equicontinuity, every fixed-anchor value
sequence along a terminal time sequence is Cauchy.  Since the values are real,
it converges.  Therefore a persistent fixed-anchor gap yields two distinct
finite terminal scalar limits.

This identifies the remaining bounded branch with a genuine two-value terminal
profile at fixed spatial anchors.  No claim is made here that the existing H³
hypotheses already imply the required temporal equicontinuity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Three-index selected temporal equicontinuity -/

/--
Uniform temporal continuity of the complementary first derivative over all
selected spatial points.

The spatial index `r` is independent of the two selected time indices `m,n`.
-/
def H3TerminalComplementGradientSelectedTemporalEquicontinuity
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
        dist (τ m) (τ n) < η →
        dist
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ m)
              (x r)
          )
          (
            h3TerminalComplementGradientFieldForPair
              u p
              (τ n)
              (x r)
          )
          < ε

/--
The three-index temporal equicontinuity property implies the earlier diagonal
selected temporal modulus.
-/
theorem selectedTemporalUniformModulus_of_selectedTemporalEquicontinuity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hEquicontinuous :
      H3TerminalComplementGradientSelectedTemporalEquicontinuity
        u p τ x) :
    H3TerminalComplementGradientSelectedTemporalUniformModulus
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
          n
          m
          n
          hmn
    ⟩

/-! ## Fixed-anchor terminal scalar limits -/

/--
Two fixed selected spatial anchors have two distinct finite terminal
complementary-gradient limits along one cofinal selected time refinement.

The positive number `δ` records a quantitative lower bound on the distance
between the two terminal scalar limits.
-/
def H3TerminalComplementGradientHasTwoDistinctFixedAnchorLimits
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (T : ℝ) : Prop :=
  ∃ δ : ℝ,
    0 < δ
      ∧
    ∃ a b : ℕ,
      ∃ L₁ L₂ : ℝ,
        δ ≤ dist L₁ L₂
          ∧
        ∃ k : ℕ → ℕ,
          Tendsto k atTop atTop
            ∧
          Tendsto
            (fun j : ℕ => τ (k j))
            atTop
            (𝓝 T)
            ∧
          Tendsto
            (
              fun j : ℕ =>
                h3TerminalComplementGradientFieldForPair
                  u p
                  (τ (k j))
                  (x a)
            )
            atTop
            (𝓝 L₁)
            ∧
          Tendsto
            (
              fun j : ℕ =>
                h3TerminalComplementGradientFieldForPair
                  u p
                  (τ (k j))
                  (x b)
            )
            atTop
            (𝓝 L₂)

/-! ## Temporal equicontinuity turns a fixed gap into two limits -/

/--
A persistent fixed-anchor terminal gap plus selected temporal equicontinuity
produces two distinct finite terminal scalar limits at those fixed anchors.
-/
theorem twoDistinctFixedAnchorLimits_of_fixedSelectedSpatialPairGap_of_temporalEquicontinuity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTemporalEquicontinuity :
      H3TerminalComplementGradientSelectedTemporalEquicontinuity
        u p τ x)
    (hFixedGap :
      H3TerminalComplementGradientHasFixedSelectedSpatialPairGapAtTerminal
        u p τ x T) :
    H3TerminalComplementGradientHasTwoDistinctFixedAnchorLimits
      u p τ x T := by

  obtain
    ⟨
      δ,
      hδ,
      a,
      b,
      k,
      hkTop,
      hTime,
      hGap
    ⟩ :=
    hFixedGap

  let A : ℕ → ℝ :=
    fun j : ℕ =>
      h3TerminalComplementGradientFieldForPair
        u p
        (τ (k j))
        (x a)

  let B : ℕ → ℝ :=
    fun j : ℕ =>
      h3TerminalComplementGradientFieldForPair
        u p
        (τ (k j))
        (x b)

  have hTimeCauchy :
      CauchySeq
        (fun j : ℕ => τ (k j)) :=
    hTime.cauchySeq

  have hACauchy :
      CauchySeq A := by

    rw [Metric.cauchySeq_iff]

    intro ε hε

    obtain
      ⟨
        η,
        hη,
        hUniform
      ⟩ :=
      hTemporalEquicontinuity
        ε
        hε

    obtain
      ⟨
        N,
        hN
      ⟩ :=
      (
        Metric.cauchySeq_iff.1
          hTimeCauchy
      )
        η
        hη

    refine
      ⟨
        N,
        ?_
      ⟩

    intro m hm n hn

    dsimp only [A]

    exact
      hUniform
        a
        (k m)
        (k n)
        (
          hN
            m hm
            n hn
        )

  have hBCauchy :
      CauchySeq B := by

    rw [Metric.cauchySeq_iff]

    intro ε hε

    obtain
      ⟨
        η,
        hη,
        hUniform
      ⟩ :=
      hTemporalEquicontinuity
        ε
        hε

    obtain
      ⟨
        N,
        hN
      ⟩ :=
      (
        Metric.cauchySeq_iff.1
          hTimeCauchy
      )
        η
        hη

    refine
      ⟨
        N,
        ?_
      ⟩

    intro m hm n hn

    dsimp only [B]

    exact
      hUniform
        b
        (k m)
        (k n)
        (
          hN
            m hm
            n hn
        )

  obtain
    ⟨
      L₁,
      hALimit
    ⟩ :=
    cauchySeq_tendsto_of_complete
      hACauchy

  obtain
    ⟨
      L₂,
      hBLimit
    ⟩ :=
    cauchySeq_tendsto_of_complete
      hBCauchy

  have hDistanceLimit :
      Tendsto
        (
          fun j : ℕ =>
            dist
              (A j)
              (B j)
        )
        atTop
        (𝓝 (dist L₁ L₂)) :=
    hALimit.dist
      hBLimit

  have hLimitGap :
      δ ≤ dist L₁ L₂ := by

    apply
      ge_of_tendsto
        hDistanceLimit

    simpa only [A, B] using
      hGap

  exact
    ⟨
      δ,
      hδ,
      a,
      b,
      L₁,
      L₂,
      hLimitGap,
      k,
      hkTop,
      hTime,
      hALimit,
      hBLimit
    ⟩

/-! ## Bounded noncanonical branch under both equicontinuity frontiers -/

/--
Under selected spatial and temporal equicontinuity, bounded selected points,
and terminal-time convergence, failure of the canonical native residual factor
forces two distinct finite terminal complementary-gradient values at two fixed
selected spatial anchors.
-/
theorem twoDistinctFixedAnchorLimits_of_noCanonicalFactor_of_equicontinuity_of_bounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    {T : ℝ}
    (hTau :
      Tendsto τ atTop (𝓝 T))
    (hTemporalEquicontinuity :
      H3TerminalComplementGradientSelectedTemporalEquicontinuity
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
    H3TerminalComplementGradientHasTwoDistinctFixedAnchorLimits
      u p τ x T := by

  have hTemporalModulus :
      H3TerminalComplementGradientSelectedTemporalUniformModulus
        u p τ x :=
    selectedTemporalUniformModulus_of_selectedTemporalEquicontinuity
      hTemporalEquicontinuity

  have hFixedGap :
      H3TerminalComplementGradientHasFixedSelectedSpatialPairGapAtTerminal
        u p τ x T :=
    fixedSelectedSpatialPairGapAtTerminal_of_noCanonicalFactor_of_equicontinuity_of_bounded
      hTau
      hTemporalModulus
      hSpatialEquicontinuity
      hBounded
      hNoFactor

  exact
    twoDistinctFixedAnchorLimits_of_fixedSelectedSpatialPairGap_of_temporalEquicontinuity
      hTemporalEquicontinuity
      hFixedGap

end

end Euclidean
end Bridge
end PrimeTensor
