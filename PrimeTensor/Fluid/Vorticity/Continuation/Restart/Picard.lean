import Mathlib.Topology.MetricSpace.Contracting
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.LocalWellPosedness

/-!
# Picard construction for the H³ restart problem

This file is the first genuinely constructive step on the local-existence side.
Instead of assuming that a restart solution exists, we package the analytic
Picard problem on a complete invariant subset and obtain its solution from
Mathlib's Banach fixed-point theorem.

The Navier--Stokes-specific work left after this file is therefore concrete:
construct the mild Picard map, prove that it preserves the chosen complete
ball, prove the contraction estimate, and prove that a fixed point decodes to
an admissible real restart.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

universe u

/--
A Picard problem on a complete invariant subset of a metric space.

The ambient space itself need not be complete.  This is the form used in the
standard local Navier--Stokes argument, where the Picard map is contracting on
a closed ball of a path space rather than globally.
-/
structure RestartPicardProblem
    (X : Type u)
    [MetricSpace X] where
  map : X → X
  domain : Set X
  complete : IsComplete domain
  mapsTo : Set.MapsTo map domain domain
  contraction : NNReal
  contracting :
    ContractingWith
      contraction
      (Set.MapsTo.restrict map domain domain mapsTo)
  seed : X
  seed_mem : seed ∈ domain

namespace RestartPicardProblem

/-- The solution selected by Banach's fixed-point theorem. -/
noncomputable def solution
    {X : Type u}
    [MetricSpace X]
    (P : RestartPicardProblem X) : X :=
  ContractingWith.efixedPoint'
    P.map
    P.complete
    P.mapsTo
    P.contracting
    P.seed
    P.seed_mem
    (edist_ne_top _ _)

/-- The Banach fixed point remains in the complete invariant domain. -/
theorem solution_mem
    {X : Type u}
    [MetricSpace X]
    (P : RestartPicardProblem X) :
    P.solution ∈ P.domain := by
  simpa [solution] using
    ContractingWith.efixedPoint_mem'
      P.complete
      P.mapsTo
      P.contracting
      P.seed_mem
      (edist_ne_top P.seed (P.map P.seed))

/-- The selected point actually solves the Picard equation. -/
theorem solution_isFixedPt
    {X : Type u}
    [MetricSpace X]
    (P : RestartPicardProblem X) :
    Function.IsFixedPt P.map P.solution := by
  simpa [solution] using
    ContractingWith.efixedPoint_isFixedPt'
      P.complete
      P.mapsTo
      P.contracting
      P.seed_mem
      (edist_ne_top P.seed (P.map P.seed))

/-- Picard iteration from the chosen seed converges to the selected solution. -/
theorem tendsto_iterate_solution
    {X : Type u}
    [MetricSpace X]
    (P : RestartPicardProblem X) :
    Filter.Tendsto
      (fun n : ℕ => P.map^[n] P.seed)
      Filter.atTop
      (nhds P.solution) := by
  simpa [solution] using
    ContractingWith.tendsto_iterate_efixedPoint'
      P.complete
      P.mapsTo
      P.contracting
      P.seed_mem
      (edist_ne_top P.seed (P.map P.seed))

end RestartPicardProblem

/--
A constructive Picard input for canonical-H³ restart.

One fixed metric space `X` is used as the ambient path space.  At each energy
ceiling `E`, a positive common time window `τ` is selected.  For every restart
slice below that ceiling, the input must then build a complete invariant
Picard problem and decoders from a fixed point to the real velocity, pressure,
and terminal time.

Crucially, the decoder is only asked to prove the Navier--Stokes restart
properties *assuming its input is a fixed point*.  Existence of that fixed
point is not an assumption: it is supplied by `RestartPicardProblem.solution`.
-/
def CanonicalH3RealPicardConstruction
    (X : Type u)
    [MetricSpace X] : Prop :=
  ∀ E : ℝ,
    1 ≤ E →
      ∃ τ : ℝ,
        0 < τ
          ∧
        ∀
          (
            u :
              PrimeTensor.SpaceTimeVectorField
                ℝ ℝ PrimeTensor.MulReal Depth.three
          )
          (T t : ℝ),
            LoggedPreterminalNavierStokesAdmissible
                u T
              →
            t ∈ Set.Ioo (0 : ℝ) T
              →
            VelocityH3IntegrableAt
                u t
              →
            velocityH3EnergyAt u t ≤ E
              →
            ∃
              (P : RestartPicardProblem X)
              (
                velocityOf :
                  X →
                    PrimeTensor.SpaceTimeVectorField
                      ℝ ℝ ℝ Depth.three
              )
              (
                pressureOf :
                  X →
                    PrimeTensor.SpaceTimeScalarField
                      ℝ ℝ ℝ Depth.three
              )
              (terminalOf : X → ℝ),
                ∀ x : X,
                  x ∈ P.domain →
                  Function.IsFixedPt P.map x →
                    t + τ < terminalOf x
                      ∧
                    RealRestartAgreesBeforeT
                      u (velocityOf x) T
                      ∧
                    PreterminalNavierStokes3
                      (velocityOf x)
                      (pressureOf x)
                      (terminalOf x)
                      ∧
                    RealVelocitySpatialC3
                      (velocityOf x)
                      ∧
                    RealVelocityThirdJetContinuousOn
                      (velocityOf x)
                      (terminalOf x)

/--
A Picard construction proves the per-energy canonical H³ local-well-posedness
statement.

This theorem is where existence is genuinely derived: Banach's theorem creates
the fixed point of each restart Picard map, after which the supplied decoder
turns that fixed point into the real Navier--Stokes continuation.
-/
theorem canonicalH3RealLocalWellPosedness_of_picardConstruction
    {X : Type u}
    [MetricSpace X]
    (
      hPicard :
        CanonicalH3RealPicardConstruction X
    ) :
    CanonicalH3RealLocalWellPosedness := by

  intro E hE

  rcases hPicard E hE with
    ⟨
      τ,
      hτ,
      hBuild
    ⟩

  refine
    ⟨
      τ,
      hτ,
      ?_
    ⟩

  intro
    u T t
    hAdmissible
    ht
    hIntegrable
    hEnergy

  rcases
    hBuild
      u T t
      hAdmissible
      ht
      hIntegrable
      hEnergy
    with
    ⟨
      P,
      velocityOf,
      pressureOf,
      terminalOf,
      hDecode
    ⟩

  let x : X :=
    P.solution

  have hxMem :
      x ∈ P.domain := by
    dsimp [x]
    exact P.solution_mem

  have hxFixed :
      Function.IsFixedPt P.map x := by
    dsimp [x]
    exact P.solution_isFixedPt

  have hDecoded :=
    hDecode
      x
      hxMem
      hxFixed

  exact
    ⟨
      velocityOf x,
      pressureOf x,
      terminalOf x,
      hDecoded
    ⟩

end Euclidean
end Bridge
end PrimeTensor
