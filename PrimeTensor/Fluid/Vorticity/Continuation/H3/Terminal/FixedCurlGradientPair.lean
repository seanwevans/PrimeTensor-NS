import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.FixedGradientComponent

/-!
# Persistent fixed curl / constituent-gradient pair

The existing terminal persistence theorems show separately that hypothetical
nonextension forces

* one fixed vorticity component to be cofinally unbounded, and
* one fixed first velocity derivative entry to be cofinally unbounded.

This file retains the structural relation between those two facts.

Each fixed curl component is a difference of exactly two fixed first
derivatives:

    ωₓ = ∂y u_z - ∂z u_y,
    ωᵧ = ∂z u_x - ∂x u_z,
    ω_z = ∂x u_y - ∂y u_x.

A generic terminal lemma proves that if `H = F - G` is cofinally unbounded,
then at least one of `F` or `G` is cofinally unbounded.  Applying it to the
three curl identities shows that the persistent gradient entry may be chosen
from the two derivatives that actually constitute the persistent curl
component.

This does not yet assert that the curl and derivative are simultaneously large
at the same selected spacetime points.

All statements remain necessary consequences conditional on hypothetical
failure of smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Generic scalar terminal persistence -/

def H3TerminalScalarComponentCofinallyUnbounded
    (a T : ℝ)
    (F : ℝ → Point3 → ℝ) : Prop :=
  ∀
    c : ℝ,
      c ∈ Set.Ioo a T →
      ∀ M : ℝ,
        ∃
          t : ℝ,
            t ∈ Set.Ioo c T
              ∧
            ∃ x : Point3,
              M < abs (F t x)

/--
If a fixed scalar terminal component `H` is the pointwise difference `F - G`
and `H` is cofinally unbounded, then at least one of the two fixed constituents
is cofinally unbounded.
-/
theorem terminalScalarComponent_one_of_sub_pair_cofinallyUnbounded
    {a T : ℝ}
    {F G H : ℝ → Point3 → ℝ}
    (hH :
      H3TerminalScalarComponentCofinallyUnbounded
        a T H)
    (hEq :
      ∀ t : ℝ,
        ∀ x : Point3,
          H t x = F t x - G t x) :
    H3TerminalScalarComponentCofinallyUnbounded
        a T F
      ∨
    H3TerminalScalarComponentCofinallyUnbounded
        a T G := by

  classical

  by_cases hF :
      H3TerminalScalarComponentCofinallyUnbounded
        a T F

  · exact
      Or.inl hF

  by_cases hG :
      H3TerminalScalarComponentCofinallyUnbounded
        a T G

  · exact
      Or.inr hG

  exfalso

  have hFBound := hF
  have hGBound := hG

  unfold H3TerminalScalarComponentCofinallyUnbounded at hFBound
  unfold H3TerminalScalarComponentCofinallyUnbounded at hGBound

  push_neg at hFBound
  push_neg at hGBound

  obtain
    ⟨cF, hcF, MF, hBoundF⟩ :=
    hFBound

  obtain
    ⟨cG, hcG, MG, hBoundG⟩ :=
    hGBound

  let c : ℝ :=
    max cF cG

  have hc :
      c ∈ Set.Ioo a T := by

    constructor

    · dsimp only [c]

      exact
        lt_of_lt_of_le
          hcF.1
          (le_max_left _ _)

    · dsimp only [c]

      exact
        max_lt
          hcF.2
          hcG.2

  let M : ℝ :=
    MF + MG

  obtain
    ⟨t, ht, x, hLarge⟩ :=
    hH
      c hc M

  have htF :
      t ∈ Set.Ioo cF T := by

    exact
      ⟨
        lt_of_le_of_lt
          (by
            dsimp only [c]
            exact le_max_left cF cG)
          ht.1,
        ht.2
      ⟩

  have htG :
      t ∈ Set.Ioo cG T := by

    exact
      ⟨
        lt_of_le_of_lt
          (by
            dsimp only [c]
            exact le_max_right cF cG)
          ht.1,
        ht.2
      ⟩

  have hAtF :=
    hBoundF
      t htF x

  have hAtG :=
    hBoundG
      t htG x

  have hUpper :
      abs (H t x) ≤ M := by

    rw [hEq t x]

    calc
      abs (F t x - G t x)
          ≤
        abs (F t x) + abs (G t x) :=
        abs_sub _ _

      _ ≤
        MF + MG :=
        add_le_add hAtF hAtG

      _ = M := by
        rfl

  exact
    (not_lt_of_ge hUpper)
      hLarge

/-! ## The three curl specializations -/

private theorem fixed_vorticityX_with_constituentGradient
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hX :
      H3TerminalVorticityXCofinallyUnbounded
        u a T) :
    H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T yAxis zAxis
      ∨
    H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T zAxis yAxis := by

  let F : ℝ → Point3 → ℝ :=
    fun t x =>
      spatial3.d
        yAxis
        (
          fun y =>
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u t y
            ).component zAxis
        )
        x

  let G : ℝ → Point3 → ℝ :=
    fun t x =>
      spatial3.d
        zAxis
        (
          fun y =>
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u t y
            ).component yAxis
        )
        x

  let H : ℝ → Point3 → ℝ :=
    fun t x =>
      realVorticityX
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x

  have hH :
      H3TerminalScalarComponentCofinallyUnbounded
        a T H := by

    simpa only [
      H,
      H3TerminalScalarComponentCofinallyUnbounded,
      H3TerminalVorticityXCofinallyUnbounded
    ] using hX

  have hEq :
      ∀ t : ℝ,
        ∀ x : Point3,
          H t x = F t x - G t x := by

    intro t x

    rfl

  rcases
      terminalScalarComponent_one_of_sub_pair_cofinallyUnbounded
        hH hEq
    with hF | hG

  · exact
      Or.inl
        (
          by
            simpa only [
              F,
              H3TerminalScalarComponentCofinallyUnbounded,
              H3TerminalVelocityGradientComponentCofinallyUnbounded
            ] using hF
        )

  · exact
      Or.inr
        (
          by
            simpa only [
              G,
              H3TerminalScalarComponentCofinallyUnbounded,
              H3TerminalVelocityGradientComponentCofinallyUnbounded
            ] using hG
        )

private theorem fixed_vorticityY_with_constituentGradient
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hY :
      H3TerminalVorticityYCofinallyUnbounded
        u a T) :
    H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T zAxis xAxis
      ∨
    H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T xAxis zAxis := by

  let F : ℝ → Point3 → ℝ :=
    fun t x =>
      spatial3.d
        zAxis
        (
          fun y =>
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u t y
            ).component xAxis
        )
        x

  let G : ℝ → Point3 → ℝ :=
    fun t x =>
      spatial3.d
        xAxis
        (
          fun y =>
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u t y
            ).component zAxis
        )
        x

  let H : ℝ → Point3 → ℝ :=
    fun t x =>
      realVorticityY
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x

  have hH :
      H3TerminalScalarComponentCofinallyUnbounded
        a T H := by

    simpa only [
      H,
      H3TerminalScalarComponentCofinallyUnbounded,
      H3TerminalVorticityYCofinallyUnbounded
    ] using hY

  have hEq :
      ∀ t : ℝ,
        ∀ x : Point3,
          H t x = F t x - G t x := by

    intro t x

    rfl

  rcases
      terminalScalarComponent_one_of_sub_pair_cofinallyUnbounded
        hH hEq
    with hF | hG

  · exact
      Or.inl
        (
          by
            simpa only [
              F,
              H3TerminalScalarComponentCofinallyUnbounded,
              H3TerminalVelocityGradientComponentCofinallyUnbounded
            ] using hF
        )

  · exact
      Or.inr
        (
          by
            simpa only [
              G,
              H3TerminalScalarComponentCofinallyUnbounded,
              H3TerminalVelocityGradientComponentCofinallyUnbounded
            ] using hG
        )

private theorem fixed_vorticityZ_with_constituentGradient
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hZ :
      H3TerminalVorticityZCofinallyUnbounded
        u a T) :
    H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T xAxis yAxis
      ∨
    H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T yAxis xAxis := by

  let F : ℝ → Point3 → ℝ :=
    fun t x =>
      spatial3.d
        xAxis
        (
          fun y =>
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u t y
            ).component yAxis
        )
        x

  let G : ℝ → Point3 → ℝ :=
    fun t x =>
      spatial3.d
        yAxis
        (
          fun y =>
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u t y
            ).component xAxis
        )
        x

  let H : ℝ → Point3 → ℝ :=
    fun t x =>
      realVorticityZ
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x

  have hH :
      H3TerminalScalarComponentCofinallyUnbounded
        a T H := by

    simpa only [
      H,
      H3TerminalScalarComponentCofinallyUnbounded,
      H3TerminalVorticityZCofinallyUnbounded
    ] using hZ

  have hEq :
      ∀ t : ℝ,
        ∀ x : Point3,
          H t x = F t x - G t x := by

    intro t x

    rfl

  rcases
      terminalScalarComponent_one_of_sub_pair_cofinallyUnbounded
        hH hEq
    with hF | hG

  · exact
      Or.inl
        (
          by
            simpa only [
              F,
              H3TerminalScalarComponentCofinallyUnbounded,
              H3TerminalVelocityGradientComponentCofinallyUnbounded
            ] using hF
        )

  · exact
      Or.inr
        (
          by
            simpa only [
              G,
              H3TerminalScalarComponentCofinallyUnbounded,
              H3TerminalVelocityGradientComponentCofinallyUnbounded
            ] using hG
        )

/-! ## Persistent structurally coupled pair -/

/--
Under hypothetical nonextension, one fixed vorticity component is cofinally
unbounded and one of the two fixed first derivatives constituting that same
curl component is also cofinally unbounded.
-/
theorem fixed_curlComponent_with_constituentGradientComponent_cofinallyUnbounded_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      H3TerminalVorticityXCofinallyUnbounded u a T
        ∧
      (
        H3TerminalVelocityGradientComponentCofinallyUnbounded
            u a T yAxis zAxis
          ∨
        H3TerminalVelocityGradientComponentCofinallyUnbounded
            u a T zAxis yAxis
      )
    )
      ∨
    (
      H3TerminalVorticityYCofinallyUnbounded u a T
        ∧
      (
        H3TerminalVelocityGradientComponentCofinallyUnbounded
            u a T zAxis xAxis
          ∨
        H3TerminalVelocityGradientComponentCofinallyUnbounded
            u a T xAxis zAxis
      )
    )
      ∨
    (
      H3TerminalVorticityZCofinallyUnbounded u a T
        ∧
      (
        H3TerminalVelocityGradientComponentCofinallyUnbounded
            u a T xAxis yAxis
          ∨
        H3TerminalVelocityGradientComponentCofinallyUnbounded
            u a T yAxis xAxis
      )
    ) := by

  rcases
      fixed_vorticityComponent_cofinallyUnbounded_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
    with hX | hY | hZ

  · exact
      Or.inl
        ⟨
          hX,
          fixed_vorticityX_with_constituentGradient hX
        ⟩

  · exact
      Or.inr
        (
          Or.inl
            ⟨
              hY,
              fixed_vorticityY_with_constituentGradient hY
            ⟩
        )

  · exact
      Or.inr
        (
          Or.inr
            ⟨
              hZ,
              fixed_vorticityZ_with_constituentGradient hZ
            ⟩
        )

/-! ## Neutral package -/

/--
Neutral terminal formulation preserving the curl/gradient structural pairing.
-/
theorem smoothContinuationExtension_or_fixed_curl_with_constituentGradient_cofinallyUnbounded
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
      (
        H3TerminalVorticityXCofinallyUnbounded u a T
          ∧
        (
          H3TerminalVelocityGradientComponentCofinallyUnbounded
              u a T yAxis zAxis
            ∨
          H3TerminalVelocityGradientComponentCofinallyUnbounded
              u a T zAxis yAxis
        )
      )
        ∨
      (
        H3TerminalVorticityYCofinallyUnbounded u a T
          ∧
        (
          H3TerminalVelocityGradientComponentCofinallyUnbounded
              u a T zAxis xAxis
            ∨
          H3TerminalVelocityGradientComponentCofinallyUnbounded
              u a T xAxis zAxis
        )
      )
        ∨
      (
        H3TerminalVorticityZCofinallyUnbounded u a T
          ∧
        (
          H3TerminalVelocityGradientComponentCofinallyUnbounded
              u a T xAxis yAxis
            ∨
          H3TerminalVelocityGradientComponentCofinallyUnbounded
              u a T yAxis xAxis
        )
      )
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
          fixed_curlComponent_with_constituentGradientComponent_cofinallyUnbounded_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
