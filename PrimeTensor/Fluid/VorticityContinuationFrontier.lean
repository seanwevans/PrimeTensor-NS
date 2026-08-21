import PrimeTensor.Fluid.VorticityContinuationCascade
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The analytic continuation frontier

The multiplicative cascade chain has been reduced to a classical continuation
input.  This file states that input with the global function-space hypothesis
made explicit.

The preterminal PDE predicate `LoggedPreterminalNavierStokesAdmissible` records
local differentiability and the equations on `(0,T)`, but by itself it does not
assert finite spatial energy or membership in a high Sobolev class.

For continuation through `T`, the correct additional datum is a finite
high-order spatial-energy seed at one interior time `a ∈ (0,T)`.  The
vorticity criterion then propagates that seed forward and yields a uniform
bound only on the terminal tail `[a,T)`.  No bound near `0` is needed.

Mathlib currently has no project-level Sobolev abstraction used here, so the
order-three spatial L² control is written explicitly: every logged velocity
component and every ordered coordinate derivative through order three has
square-integrable spatial profile.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable local instance axisFintypeContinuationFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
A scalar spatial field is square-integrable and its squared L² integral is
bounded by `M`.
-/
def SpatialL2SquareBound
    (f : ScalarField3)
    (M : ℝ) : Prop :=
  MeasureTheory.Integrable
      (fun x : Point3 => (f x) ^ 2)
    ∧
  (∫ x : Point3, (f x) ^ 2) ≤ M

/-- The `j`th logged velocity component at fixed time. -/
noncomputable def loggedVelocityComponent
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    (
      PrimeTensor.Bridge.logSpaceTimeVectorField
        u t x
    ).component j

/--
Concrete order-three Sobolev-type spatial control at one time.

For every velocity component, the component itself and every ordered coordinate
partial through order three has squared L² integral at most `M`.
-/
def VelocityH3BoundAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t M : ℝ) : Prop :=
  ∀ j : PrimeTensor.Axis Depth.three,
    let f :=
      loggedVelocityComponent u t j
    SpatialL2SquareBound f M
      ∧
    (
      ∀ a : PrimeTensor.Axis Depth.three,
        SpatialL2SquareBound
          (spatial3.d a f)
          M
    )
      ∧
    (
      ∀
        a b : PrimeTensor.Axis Depth.three,
        SpatialL2SquareBound
          (
            spatial3.d a
              (spatial3.d b f)
          )
          M
    )
      ∧
    (
      ∀
        a b c : PrimeTensor.Axis Depth.three,
        SpatialL2SquareBound
          (
            spatial3.d a
              (
                spatial3.d b
                  (spatial3.d c f)
              )
          )
          M
    )

/--
A finite order-three spatial-energy seed at one strictly preterminal time.

This is the function-space datum absent from
`LoggedPreterminalNavierStokesAdmissible`.
-/
def PreterminalH3Seed
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ) : Prop :=
  ∃ (a M : ℝ),
    a ∈ Set.Ioo (0 : ℝ) T
      ∧
    0 ≤ M
      ∧
    VelocityH3BoundAt
      u a M

/--
Uniform order-three spatial-energy control on some terminal tail `[a,T)`.

This is the quantity needed for continuation through `T`; unlike the previous
draft it deliberately imposes no uniform bound as `t → 0⁺`.
-/
def TerminalTailH3Control
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ) : Prop :=
  ∃ (a M : ℝ),
    a ∈ Set.Ioo (0 : ℝ) T
      ∧
    0 ≤ M
      ∧
    ∀ t : ℝ,
      t ∈ Set.Ico a T →
        VelocityH3BoundAt
          u t M

/--
First classical analytic link:

    one finite H³ seed
      + ∫₀ᵀ ||ω(t)||∞ dt < ∞
      -> uniform H³-type control on a terminal tail.

This is a known-style continuation estimate, but it is not yet formalized in
the project.
-/
def VorticityL1LinfProducesH3Control : Prop :=
  ∀
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ),
      LoggedPreterminalNavierStokesAdmissible
          u T
        →
      PreterminalH3Seed
          u T
        →
      VorticityL1LinfControl
          u T
        →
      TerminalTailH3Control
          u T

/--
Second classical analytic link:

    uniform H³-type control on a terminal tail
      -> a smooth continuation through T.

This packages the local-well-posedness / restart portion separately from the
a-priori vorticity estimate.
-/
def H3ControlProducesExtension : Prop :=
  ∀
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ),
      LoggedPreterminalNavierStokesAdmissible
          u T
        →
      TerminalTailH3Control
          u T
        →
      ∃
        v :
          PrimeTensor.SpaceTimeVectorField
            ℝ ℝ PrimeTensor.MulReal Depth.three,
        SmoothContinuationExtension
          u v T

/--
The standard seeded continuation statement corresponding to the concrete
vorticity criterion.
-/
def SeededVorticityL1LinfProducesExtension : Prop :=
  ∀
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ),
      LoggedPreterminalNavierStokesAdmissible
          u T
        →
      PreterminalH3Seed
          u T
        →
      VorticityL1LinfControl
          u T
        →
      ∃
        v :
          PrimeTensor.SpaceTimeVectorField
            ℝ ℝ PrimeTensor.MulReal Depth.three,
        SmoothContinuationExtension
          u v T

/--
The two classical links compose to the honest seeded continuation criterion.
-/
theorem seededVorticityL1LinfProducesExtension_of_H3Factorization
    (
      hVorticityToH3 :
        VorticityL1LinfProducesH3Control
    )
    (
      hH3ToExtension :
        H3ControlProducesExtension
    ) :
    SeededVorticityL1LinfProducesExtension := by

  intro u T hAdmissible hSeed hControl

  have hH3 :
      TerminalTailH3Control
        u T :=
    hVorticityToH3
      u T
      hAdmissible
      hSeed
      hControl

  exact
    hH3ToExtension
      u T
      hAdmissible
      hH3

/--
The genuinely dangerous a-priori statement, restricted to the high-energy
solution class relevant to continuation.

This is *not* asserted as a theorem.
-/
def SeededPreterminalNavierStokesForcesVorticityL1Linf : Prop :=
  ∀
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ),
      LoggedPreterminalNavierStokesAdmissible
          u T
        →
      PreterminalH3Seed
          u T
        →
      VorticityL1LinfControl
          u T

/--
Abstract global-continuation conclusion at the level of the seeded preterminal
solution interface.
-/
def EverySeededPreterminalNavierStokesSolutionExtends : Prop :=
  ∀
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ),
      LoggedPreterminalNavierStokesAdmissible
          u T
        →
      PreterminalH3Seed
          u T
        →
      ∃
        v :
          PrimeTensor.SpaceTimeVectorField
            ℝ ℝ PrimeTensor.MulReal Depth.three,
        SmoothContinuationExtension
          u v T

/--
If the seeded continuation criterion is available, then the open a-priori
vorticity estimate gives continuation of every seeded preterminal solution.
-/
theorem everySeededPreterminalSolutionExtends_of_vorticityCriterion
    (
      hContinuation :
        SeededVorticityL1LinfProducesExtension
    )
    (
      hApriori :
        SeededPreterminalNavierStokesForcesVorticityL1Linf
    ) :
    EverySeededPreterminalNavierStokesSolutionExtends := by

  intro u T hAdmissible hSeed

  exact
    hContinuation
      u T
      hAdmissible
      hSeed
      (
        hApriori
          u T
          hAdmissible
          hSeed
      )

/--
Contrapositive form of the seeded continuation criterion.
-/
theorem not_vorticityL1LinfControl_of_noSeededExtension
    (
      hContinuation :
        SeededVorticityL1LinfProducesExtension
    )
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T : ℝ}
    (
      hAdmissible :
        LoggedPreterminalNavierStokesAdmissible
          u T
    )
    (
      hSeed :
        PreterminalH3Seed
          u T
    )
    (
      hNoExtension :
        ¬ ∃
          v :
            PrimeTensor.SpaceTimeVectorField
              ℝ ℝ PrimeTensor.MulReal Depth.three,
          SmoothContinuationExtension
            u v T
    ) :
    ¬ VorticityL1LinfControl
        u T := by

  intro hControl

  exact
    hNoExtension
      (
        hContinuation
          u T
          hAdmissible
          hSeed
          hControl
      )

end Euclidean
end Bridge
end PrimeTensor
