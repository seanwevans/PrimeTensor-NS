import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.FixedVorticityComponent

/-!
# A fixed terminal velocity-gradient component is cofinally unbounded

The fixed-vorticity-component theorem removes the possibility that terminal
vorticity growth merely rotates among `ωₓ`, `ωᵧ`, and `ω_z`.

Each fixed curl component is the difference of two fixed first velocity
derivatives:

    ωₓ = ∂y u_z - ∂z u_y,
    ωᵧ = ∂z u_x - ∂x u_z,
    ω_z = ∂x u_y - ∂y u_x.

If both derivatives in one of these pairs were eventually bounded on terminal
tails, then on the later of those tails their difference would also be
bounded.  Therefore cofinal unboundedness of a fixed curl component forces
cofinal unboundedness of at least one fixed derivative entry.

Combining this with the previous theorem yields a fixed pair of axes `(i,j)`
such that `|∂ᵢ uⱼ|` exceeds every finite threshold arbitrarily close to the
terminal time.

This remains a necessary consequence conditional on hypothetical failure of
smooth continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Fixed gradient-component predicate -/

def H3TerminalVelocityGradientComponentCofinallyUnbounded
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (i j : PrimeTensor.Axis Depth.three) : Prop :=
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
                  spatial3.d
                    i
                    (
                      fun y =>
                        (
                          PrimeTensor.Bridge.logSpaceTimeVectorField
                            u t y
                        ).component j
                    )
                    x
                )

/-! ## Fixed curl component forces one fixed derivative component -/

private theorem fixed_gradientComponent_of_fixed_vorticityX
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hX : H3TerminalVorticityXCofinallyUnbounded u a T) :
    H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T yAxis zAxis
      ∨
    H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T zAxis yAxis := by

  classical

  by_cases hyz :
      H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T yAxis zAxis

  · exact Or.inl hyz

  by_cases hzy :
      H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T zAxis yAxis

  · exact Or.inr hzy

  exfalso

  have hyzBound := hyz
  have hzyBound := hzy

  unfold H3TerminalVelocityGradientComponentCofinallyUnbounded at hyzBound
  unfold H3TerminalVelocityGradientComponentCofinallyUnbounded at hzyBound

  push_neg at hyzBound
  push_neg at hzyBound

  obtain ⟨cyz, hcyz, Myz, hBoundYZ⟩ := hyzBound
  obtain ⟨czy, hczy, Mzy, hBoundZY⟩ := hzyBound

  let c : ℝ := max cyz czy

  have hc :
      c ∈ Set.Ioo a T := by

    constructor

    · dsimp only [c]

      exact
        lt_of_lt_of_le
          hcyz.1
          (le_max_left _ _)

    · dsimp only [c]

      exact
        max_lt
          hcyz.2
          hczy.2

  let M : ℝ := Myz + Mzy

  obtain ⟨t, ht, x, hLarge⟩ :=
    hX c hc M

  have htYZ' :
      cyz < t := by

    exact
      lt_of_le_of_lt
        (by
          dsimp only [c]
          exact le_max_left cyz czy)
        ht.1

  have htZY' :
      czy < t := by

    exact
      lt_of_le_of_lt
        (by
          dsimp only [c]
          exact le_max_right cyz czy)
        ht.1

  have hYZ :=
    hBoundYZ
      t
      ⟨htYZ', ht.2⟩
      x

  have hZY :=
    hBoundZY
      t
      ⟨htZY', ht.2⟩
      x

  have hUpper :
      abs
        (
          realVorticityX
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t x
        )
        ≤
      M := by

    unfold realVorticityX

    calc
      abs
          (
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
              -
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
          )
          ≤
        abs
            (
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
            )
          +
        abs
            (
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
            ) :=
        abs_sub _ _

      _ ≤ Myz + Mzy :=
        add_le_add hYZ hZY

      _ = M := by
        rfl

  exact
    (not_lt_of_ge hUpper)
      hLarge

private theorem fixed_gradientComponent_of_fixed_vorticityY
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hY : H3TerminalVorticityYCofinallyUnbounded u a T) :
    H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T zAxis xAxis
      ∨
    H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T xAxis zAxis := by

  classical

  by_cases hzx :
      H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T zAxis xAxis

  · exact Or.inl hzx

  by_cases hxz :
      H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T xAxis zAxis

  · exact Or.inr hxz

  exfalso

  have hzxBound := hzx
  have hxzBound := hxz

  unfold H3TerminalVelocityGradientComponentCofinallyUnbounded at hzxBound
  unfold H3TerminalVelocityGradientComponentCofinallyUnbounded at hxzBound

  push_neg at hzxBound
  push_neg at hxzBound

  obtain ⟨czx, hczx, Mzx, hBoundZX⟩ := hzxBound
  obtain ⟨cxz, hcxz, Mxz, hBoundXZ⟩ := hxzBound

  let c : ℝ := max czx cxz

  have hc :
      c ∈ Set.Ioo a T := by

    constructor

    · dsimp only [c]

      exact
        lt_of_lt_of_le
          hczx.1
          (le_max_left _ _)

    · dsimp only [c]

      exact
        max_lt
          hczx.2
          hcxz.2

  let M : ℝ := Mzx + Mxz

  obtain ⟨t, ht, x, hLarge⟩ :=
    hY c hc M

  have htZX :
      t ∈ Set.Ioo czx T :=
    ⟨
      lt_of_le_of_lt
        (by
          dsimp only [c]
          exact le_max_left czx cxz)
        ht.1,
      ht.2
    ⟩

  have htXZ :
      t ∈ Set.Ioo cxz T :=
    ⟨
      lt_of_le_of_lt
        (by
          dsimp only [c]
          exact le_max_right czx cxz)
        ht.1,
      ht.2
    ⟩

  have hZX :=
    hBoundZX
      t
      htZX
      x

  have hXZ :=
    hBoundXZ
      t
      htXZ
      x

  have hUpper :
      abs
        (
          realVorticityY
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t x
        )
        ≤
      M := by

    unfold realVorticityY

    calc
      abs
          (
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
              -
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
          )
          ≤
        abs
            (
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
            )
          +
        abs
            (
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
            ) :=
        abs_sub _ _

      _ ≤ Mzx + Mxz :=
        add_le_add hZX hXZ

      _ = M := by
        rfl

  exact
    (not_lt_of_ge hUpper)
      hLarge

private theorem fixed_gradientComponent_of_fixed_vorticityZ
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hZ : H3TerminalVorticityZCofinallyUnbounded u a T) :
    H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T xAxis yAxis
      ∨
    H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T yAxis xAxis := by

  classical

  by_cases hxy :
      H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T xAxis yAxis

  · exact Or.inl hxy

  by_cases hyx :
      H3TerminalVelocityGradientComponentCofinallyUnbounded
        u a T yAxis xAxis

  · exact Or.inr hyx

  exfalso

  have hxyBound := hxy
  have hyxBound := hyx

  unfold H3TerminalVelocityGradientComponentCofinallyUnbounded at hxyBound
  unfold H3TerminalVelocityGradientComponentCofinallyUnbounded at hyxBound

  push_neg at hxyBound
  push_neg at hyxBound

  obtain ⟨cxy, hcxy, Mxy, hBoundXY⟩ := hxyBound
  obtain ⟨cyx, hcyx, Myx, hBoundYX⟩ := hyxBound

  let c : ℝ := max cxy cyx

  have hc :
      c ∈ Set.Ioo a T := by

    constructor

    · dsimp only [c]

      exact
        lt_of_lt_of_le
          hcxy.1
          (le_max_left _ _)

    · dsimp only [c]

      exact
        max_lt
          hcxy.2
          hcyx.2

  let M : ℝ := Mxy + Myx

  obtain ⟨t, ht, x, hLarge⟩ :=
    hZ c hc M

  have htXY :
      t ∈ Set.Ioo cxy T :=
    ⟨
      lt_of_le_of_lt
        (by
          dsimp only [c]
          exact le_max_left cxy cyx)
        ht.1,
      ht.2
    ⟩

  have htYX :
      t ∈ Set.Ioo cyx T :=
    ⟨
      lt_of_le_of_lt
        (by
          dsimp only [c]
          exact le_max_right cxy cyx)
        ht.1,
      ht.2
    ⟩

  have hXY :=
    hBoundXY
      t
      htXY
      x

  have hYX :=
    hBoundYX
      t
      htYX
      x

  have hUpper :
      abs
        (
          realVorticityZ
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t x
        )
        ≤
      M := by

    unfold realVorticityZ

    calc
      abs
          (
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
              -
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
          )
          ≤
        abs
            (
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
            )
          +
        abs
            (
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
            ) :=
        abs_sub _ _

      _ ≤ Mxy + Myx :=
        add_le_add hXY hYX

      _ = M := by
        rfl

  exact
    (not_lt_of_ge hUpper)
      hLarge

/-! ## Fixed gradient entry under hypothetical nonextension -/

/--
Under hypothetical nonextension, at least one fixed first velocity derivative
component is cofinally unbounded toward the terminal time.
-/
theorem exists_fixed_velocityGradientComponent_cofinallyUnbounded_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃
      i j : PrimeTensor.Axis Depth.three,
        H3TerminalVelocityGradientComponentCofinallyUnbounded
          u a T i j := by

  rcases
      fixed_vorticityComponent_cofinallyUnbounded_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
    with hX | hY | hZ

  · rcases
      fixed_gradientComponent_of_fixed_vorticityX hX
    with hyz | hzy

    · exact
        ⟨
          yAxis,
          zAxis,
          hyz
        ⟩

    · exact
        ⟨
          zAxis,
          yAxis,
          hzy
        ⟩

  · rcases
      fixed_gradientComponent_of_fixed_vorticityY hY
    with hzx | hxz

    · exact
        ⟨
          zAxis,
          xAxis,
          hzx
        ⟩

    · exact
        ⟨
          xAxis,
          zAxis,
          hxz
        ⟩

  · rcases
      fixed_gradientComponent_of_fixed_vorticityZ hZ
    with hxy | hyx

    · exact
        ⟨
          xAxis,
          yAxis,
          hxy
        ⟩

    · exact
        ⟨
          yAxis,
          xAxis,
          hyx
        ⟩

/-! ## Neutral package -/

/--
Neutral terminal formulation: either the H³ path extends smoothly, or one
fixed first velocity derivative component is cofinally unbounded toward the
terminal time.
-/
theorem smoothContinuationExtension_or_fixed_velocityGradientComponent_cofinallyUnbounded
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
      ∃
        i j : PrimeTensor.Axis Depth.three,
          H3TerminalVelocityGradientComponentCofinallyUnbounded
            u a T i j
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        (
          exists_fixed_velocityGradientComponent_cofinallyUnbounded_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
