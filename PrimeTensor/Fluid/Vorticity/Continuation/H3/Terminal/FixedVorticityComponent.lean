import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.ComponentAmplitude

/-!
# A fixed terminal vorticity component is cofinally unbounded

The preceding terminal component-amplitude theorem says that, under
hypothetical nonextension, every strict terminal tail contains a spacetime
point where at least one of the three real vorticity components exceeds any
prescribed finite threshold.

A priori the large component could vary between `x`, `y`, and `z`.

Because there are only three components, that rotation cannot hide all three
behind separate finite terminal bounds.  If each component were eventually
bounded on some terminal tail, then on the latest of those three tails all
three would admit one common finite bound, contradicting the terminal
component-amplitude theorem.

Hence at least one fixed vorticity component is cofinally unbounded all the
way to the terminal time.

This remains a necessary consequence conditional on hypothetical failure of
smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Fixed-component cofinal unboundedness predicates -/

def H3TerminalVorticityXCofinallyUnbounded
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  ∀
    c : ℝ,
      c ∈ Set.Ioo a T →
      ∀ M : ℝ,
        ∃
          t : ℝ,
            t ∈ Set.Ioo c T
              ∧
            ∃ x : Point3,
              M
                <
              abs
                (
                  realVorticityX
                    (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                    t x
                )

def H3TerminalVorticityYCofinallyUnbounded
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  ∀
    c : ℝ,
      c ∈ Set.Ioo a T →
      ∀ M : ℝ,
        ∃
          t : ℝ,
            t ∈ Set.Ioo c T
              ∧
            ∃ x : Point3,
              M
                <
              abs
                (
                  realVorticityY
                    (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                    t x
                )

def H3TerminalVorticityZCofinallyUnbounded
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  ∀
    c : ℝ,
      c ∈ Set.Ioo a T →
      ∀ M : ℝ,
        ∃
          t : ℝ,
            t ∈ Set.Ioo c T
              ∧
            ∃ x : Point3,
              M
                <
              abs
                (
                  realVorticityZ
                    (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                    t x
                )

/-! ## Finite-coordinate persistence -/

/--
Under hypothetical nonextension, at least one fixed real vorticity component
is cofinally unbounded on the terminal H³ energy-class tail.
-/
theorem fixed_vorticityComponent_cofinallyUnbounded_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalVorticityXCofinallyUnbounded u a T
      ∨
    H3TerminalVorticityYCofinallyUnbounded u a T
      ∨
    H3TerminalVorticityZCofinallyUnbounded u a T := by

  classical

  by_cases hX :
      H3TerminalVorticityXCofinallyUnbounded u a T

  · exact
      Or.inl hX

  by_cases hY :
      H3TerminalVorticityYCofinallyUnbounded u a T

  · exact
      Or.inr
        (Or.inl hY)

  by_cases hZ :
      H3TerminalVorticityZCofinallyUnbounded u a T

  · exact
      Or.inr
        (Or.inr hZ)

  exfalso

  have hXBound := hX
  have hYBound := hY
  have hZBound := hZ

  unfold H3TerminalVorticityXCofinallyUnbounded at hXBound
  unfold H3TerminalVorticityYCofinallyUnbounded at hYBound
  unfold H3TerminalVorticityZCofinallyUnbounded at hZBound

  push_neg at hXBound
  push_neg at hYBound
  push_neg at hZBound

  obtain
    ⟨
      cX,
      hcX,
      MX,
      hBoundX
    ⟩ :=
    hXBound

  obtain
    ⟨
      cY,
      hcY,
      MY,
      hBoundY
    ⟩ :=
    hYBound

  obtain
    ⟨
      cZ,
      hcZ,
      MZ,
      hBoundZ
    ⟩ :=
    hZBound

  let c : ℝ :=
    max cX (max cY cZ)

  have hcLower :
      a < c := by

    dsimp only [c]

    exact
      lt_of_lt_of_le
        hcX.1
        (le_max_left _ _)

  have hcUpper :
      c < T := by

    dsimp only [c]

    exact
      max_lt
        hcX.2
        (
          max_lt
            hcY.2
            hcZ.2
        )

  have hc :
      c ∈ Set.Ioo a T :=
    ⟨
      hcLower,
      hcUpper
    ⟩

  let M : ℝ :=
    max MX (max MY MZ)

  obtain
    ⟨
      t,
      ht,
      x,
      hAmp
    ⟩ :=
    exists_vorticityComponent_gt_on_every_strictSubtail_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      c
      hc
      M

  have hcXc :
      cX ≤ c := by

    dsimp only [c]

    exact
      le_max_left _ _

  have hcYc :
      cY ≤ c := by

    dsimp only [c]

    exact
      le_trans
        (le_max_left _ _)
        (le_max_right _ _)

  have hcZc :
      cZ ≤ c := by

    dsimp only [c]

    exact
      le_trans
        (le_max_right _ _)
        (le_max_right _ _)

  have htX :
      t ∈ Set.Ioo cX T :=
    ⟨
      lt_of_le_of_lt
        hcXc
        ht.1,
      ht.2
    ⟩

  have htY :
      t ∈ Set.Ioo cY T :=
    ⟨
      lt_of_le_of_lt
        hcYc
        ht.1,
      ht.2
    ⟩

  have htZ :
      t ∈ Set.Ioo cZ T :=
    ⟨
      lt_of_le_of_lt
        hcZc
        ht.1,
      ht.2
    ⟩

  have hMX :
      MX ≤ M := by

    dsimp only [M]

    exact
      le_max_left _ _

  have hMY :
      MY ≤ M := by

    dsimp only [M]

    exact
      le_trans
        (le_max_left _ _)
        (le_max_right _ _)

  have hMZ :
      MZ ≤ M := by

    dsimp only [M]

    exact
      le_trans
        (le_max_right _ _)
        (le_max_right _ _)

  rcases hAmp with hAmpX | hAmpY | hAmpZ

  · have hAtX :=
      hBoundX
        t
        htX
        x

    linarith

  · have hAtY :=
      hBoundY
        t
        htY
        x

    linarith

  · have hAtZ :=
      hBoundZ
        t
        htZ
        x

    linarith

/-! ## Neutral package -/

/--
Neutral terminal formulation: either the H³ path extends smoothly, or one
fixed vorticity component is cofinally unbounded toward the terminal time.
-/
theorem smoothContinuationExtension_or_fixed_vorticityComponent_cofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      H3TerminalVorticityXCofinallyUnbounded u a T
        ∨
      H3TerminalVorticityYCofinallyUnbounded u a T
        ∨
      H3TerminalVorticityZCofinallyUnbounded u a T
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl hExtension

  · exact
      Or.inr
        (
          fixed_vorticityComponent_cofinallyUnbounded_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
