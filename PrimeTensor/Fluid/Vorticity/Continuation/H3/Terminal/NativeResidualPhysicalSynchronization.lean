import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualCofinalSynchronization

/-!
# Physical complementary-gradient form of the native residual frontier

The terminal residual has so far been expressed through the completed
multiplicative state

    ratio selectedGradient selectedSignedCurl

and its canonical logarithmic coordinate.

For the fixed structural pair, however, that logarithmic residual is exactly
the ordinary real complementary first derivative of the logged velocity:

    logValue residual
      =
    h3TerminalComplementGradientFieldForPair u p t x.

This file transports the exact Cauchy / cofinal-synchronization frontier back
to that physical real derivative.

Consequently, a full canonical native residual factor on a fixed terminal
spacetime sequence exists exactly when every two cofinal refinements of the
ordinary complementary derivative values synchronize.

Failure is equivalently witnessed by two cofinal refinements whose ordinary
complementary derivative values remain separated by one fixed positive gap.

This identifies the next genuinely PDE-specific issue.  The existing
preterminal regularity gives strong spatial smoothness at each strict time,
but no joint terminal modulus is assumed here that would force values at
possibly unrelated selected spatial points to synchronize.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Exact physical identity -/

/--
The logarithmic coordinate of the exact native complementary residual on the
selected sequence is literally the corresponding real complementary first
derivative of the logged velocity.
-/
theorem h3TerminalNativeComplementResidualLogSequence_eq_complementGradientField
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (n : ℕ) :
    h3TerminalNativeComplementResidualLogSequence
        u p τ x n
      =
    h3TerminalComplementGradientFieldForPair
      u p
      (τ n)
      (x n) := by

  unfold
    h3TerminalNativeComplementResidualLogSequence

  rw [
    ← h3TerminalNativeComplementGradientForPair_eq_residualRatio,
    logValue_h3TerminalNativeComplementGradientForPair
  ]

/-! ## Physical cofinal synchronization -/

/--
Every two cofinal refinements of the ordinary complementary derivative values
synchronize.
-/
def H3TerminalComplementGradientCofinalSynchronization
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
                (τ (k₂ j))
                (x (k₂ j))
            )
      )
      atTop
      (𝓝 0)

/--
Native residual synchronization is exactly synchronization of the ordinary
real complementary derivative.
-/
theorem nativeComplementResidualCofinalSynchronization_iff_complementGradient
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) :
    H3TerminalNativeComplementResidualCofinalSynchronization
        u p τ x
      ↔
    H3TerminalComplementGradientCofinalSynchronization
        u p τ x := by

  constructor

  · intro hSync
    intro k₁ k₂ hk₁Top hk₂Top

    have h :=
      hSync
        k₁ k₂
        hk₁Top hk₂Top

    simpa only [
      h3TerminalNativeComplementResidualLogSequence_eq_complementGradientField
    ] using h

  · intro hSync
    intro k₁ k₂ hk₁Top hk₂Top

    have h :=
      hSync
        k₁ k₂
        hk₁Top hk₂Top

    simpa only [
      h3TerminalNativeComplementResidualLogSequence_eq_complementGradientField
    ] using h

/--
A full canonical native complementary factor exists exactly when the physical
complementary derivative values synchronize on every two cofinal refinements.
-/
theorem nativeComplementHasCanonicalFactor_iff_complementGradientCofinalSynchronization
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) :
    H3TerminalNativeComplementHasCanonicalFactor
        u p τ x
      ↔
    H3TerminalComplementGradientCofinalSynchronization
        u p τ x := by

  rw [
    nativeComplementHasCanonicalFactor_iff_cofinalSynchronization,
    nativeComplementResidualCofinalSynchronization_iff_complementGradient
  ]

/-! ## Physical cofinal gap -/

/--
Two cofinal refinements of the ordinary complementary derivative retain one
fixed positive synchronized gap.
-/
def H3TerminalComplementGradientCofinalGap
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) : Prop :=
  ∃ ε : ℝ,
    0 < ε
      ∧
    ∃ k₁ k₂ : ℕ → ℕ,
      Tendsto k₁ atTop atTop
        ∧
      Tendsto k₂ atTop atTop
        ∧
      ∀ j : ℕ,
        ε
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
              (τ (k₂ j))
              (x (k₂ j))
          )

/--
The native cofinal-gap obstruction is exactly the same obstruction stated on
the ordinary complementary derivative field.
-/
theorem nativeComplementResidualCofinalGap_iff_complementGradientCofinalGap
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) :
    H3TerminalNativeComplementResidualCofinalGap
        u p τ x
      ↔
    H3TerminalComplementGradientCofinalGap
        u p τ x := by

  constructor

  · rintro
      ⟨
        ε,
        hε,
        k₁,
        k₂,
        hk₁Top,
        hk₂Top,
        hGap
      ⟩

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

    simpa only [
      h3TerminalNativeComplementResidualLogSequence_eq_complementGradientField
    ] using
      (hGap j)

  · rintro
      ⟨
        ε,
        hε,
        k₁,
        k₂,
        hk₁Top,
        hk₂Top,
        hGap
      ⟩

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

    simpa only [
      h3TerminalNativeComplementResidualLogSequence_eq_complementGradientField
    ] using
      (hGap j)

/--
Failure of the full canonical native factor is exactly a positive synchronized
cofinal gap in the ordinary real complementary derivative.
-/
theorem not_nativeComplementHasCanonicalFactor_iff_complementGradientCofinalGap
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3) :
    (
      ¬
        H3TerminalNativeComplementHasCanonicalFactor
          u p τ x
    )
      ↔
    H3TerminalComplementGradientCofinalGap
      u p τ x := by

  rw [
    not_nativeComplementHasCanonicalFactor_iff_cofinalGap,
    nativeComplementResidualCofinalGap_iff_complementGradientCofinalGap
  ]

/-! ## Physical finite-variation criterion -/

/--
Summable consecutive variation of the ordinary complementary derivative along
the selected terminal sequence is sufficient for a full canonical native
factor.
-/
theorem nativeComplementHasCanonicalFactor_of_complementGradientFiniteVariation
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (τ : ℕ → ℝ)
    (x : ℕ → Point3)
    (hVariation :
      Summable
        (
          fun n : ℕ =>
            dist
              (
                h3TerminalComplementGradientFieldForPair
                  u p
                  (τ n)
                  (x n)
              )
              (
                h3TerminalComplementGradientFieldForPair
                  u p
                  (τ n.succ)
                  (x n.succ)
              )
        )) :
    H3TerminalNativeComplementHasCanonicalFactor
      u p τ x := by

  apply
    nativeComplementHasCanonicalFactor_of_complementLogFiniteVariation
      u p τ x

  simpa only [
    logValue_h3TerminalNativeComplementGradientForPair
  ] using hVariation

/-! ## Distinct clusters force a physical derivative gap -/

/--
Two distinct finite native residual cluster factors force a positive
synchronized gap between ordinary complementary derivative values.
-/
theorem nativeComplement_twoDistinctClusterFactors_force_complementGradientGap
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {τ : ℕ → ℝ}
    {x : ℕ → Point3}
    (hTwo :
      H3TerminalNativeComplementHasTwoDistinctClusterFactors
        u p τ x) :
    ∃ k₁ k₂ : ℕ → ℕ,
      Tendsto k₁ atTop atTop
        ∧
      Tendsto k₂ atTop atTop
        ∧
      ∃ δ : ℝ,
        0 < δ
          ∧
        ∀ᶠ j : ℕ in atTop,
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
                (τ (k₂ j))
                (x (k₂ j))
            ) := by

  obtain
    ⟨
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      δ,
      hδ,
      hGap
    ⟩ :=
    nativeComplement_twoDistinctClusterFactors_force_eventual_complementLogGap
      hTwo

  refine
    ⟨
      k₁,
      k₂,
      hk₁Top,
      hk₂Top,
      δ,
      hδ,
      ?_
    ⟩

  simpa only [
    logValue_h3TerminalNativeComplementGradientForPair
  ] using hGap

end

end Euclidean
end Bridge
end PrimeTensor
