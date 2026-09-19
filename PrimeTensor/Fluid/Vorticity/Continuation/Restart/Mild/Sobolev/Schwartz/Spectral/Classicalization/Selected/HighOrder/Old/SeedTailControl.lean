import PrimeTensor.Fluid.Vorticity.Continuation.Restart.EnergyLifespan
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.HighOrder.Old.SlidingEnergyClass

/-!
# Diagnose the seed-to-canonical-tail frontier

`SlidingEnergyClass` introduced the sufficient propagation hypothesis

    H3SeedProducesCanonicalH3Tail

and showed that it implies `H3SeedProducesEnergyClass`.

It is important not to mistake that proposition for a routine parabolic
smoothing lemma.  A canonical H³ terminal tail contains a *uniform* scalar H³
ceiling all the way to the candidate terminal time.

This file identifies its exact strength.

Using the finite-coordinate equivalence already proved in `EnergyLifespan`:

* a canonical scalar H³ tail gives `TerminalTailH3Control`;
* `TerminalTailH3Control` gives a canonical scalar H³ tail with ceiling
  `velocityH3CoordinateBudget M`.

Consequently

    H3SeedProducesCanonicalH3Tail

is equivalent to the vorticity-independent assertion that every finite H³ seed
already produces uniform terminal-tail H³ control.

So this proposition is deliberately *not* promoted as the remaining smoothing
target.  It is a strong sufficient route, essentially a tail-H³ propagation
theorem.  The actual local smoothing/overlap problem should be attacked below
this level.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set

noncomputable section

noncomputable local instance axisFintypeH3SeedTailControlEquivalence
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
A canonical scalar H³ tail supplies the componentwise terminal-tail H³ control
used by the continuation interface.
-/
theorem terminalTailH3Control_of_canonicalH3Tail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a E : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u a T E) :
    TerminalTailH3Control u T := by

  refine
    ⟨
      a,
      E,
      ha,
      by linarith,
      ?_
    ⟩

  intro s hs

  have hAt :=
    hTail s hs

  have hCanonical :
      VelocityH3BoundAt
        u s
        (velocityH3EnergyAt u s) :=
    velocityH3BoundAt_canonical
      u s hAt.1

  exact
    velocityH3BoundAt_mono
      hCanonical
      hAt.2

/--
Conversely, componentwise terminal-tail H³ control gives a canonical scalar H³
tail after replacing the componentwise bound by its finite coordinate budget.
-/
theorem canonicalH3Tail_of_terminalTailH3Control
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hControl : TerminalTailH3Control u T) :
    ∃
      (a E : ℝ),
        a ∈ Set.Ioo (0 : ℝ) T
          ∧
        1 ≤ E
          ∧
        CanonicalH3TailDataFrom u a T E := by

  rcases hControl with
    ⟨
      a,
      M,
      ha,
      hM,
      hBound
    ⟩

  let E : ℝ :=
    velocityH3CoordinateBudget M

  have hE :
      1 ≤ E := by
    dsimp only [E]
    exact
      one_le_velocityH3CoordinateBudget hM

  refine
    ⟨
      a,
      E,
      ha,
      hE,
      ?_
    ⟩

  intro s hs

  have hsBound :
      VelocityH3BoundAt u s M :=
    hBound s hs

  exact
    ⟨
      velocityH3IntegrableAt_of_bound
        hsBound,
      by
        dsimp only [E]
        exact
          velocityH3EnergyAt_le_coordinateBudget_of_bound
            hsBound
    ⟩

/--
Seed-to-terminal-tail H³ control, with no vorticity hypothesis.

This definition exists only to state the strength comparison cleanly.
-/
def H3SeedProducesTerminalTailH3Control : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalNavierStokesAdmissible u T →
      PreterminalH3Seed u T →
      TerminalTailH3Control u T

/--
The canonical-tail propagation proposition is exactly equivalent to
vorticity-independent seed-to-terminal-tail H³ control.
-/
theorem h3SeedProducesCanonicalH3Tail_iff_terminalTailH3Control :
    H3SeedProducesCanonicalH3Tail
      ↔
    H3SeedProducesTerminalTailH3Control := by

  constructor

  · intro hCanonical
    intro u T hNS hSeed

    rcases
      hCanonical u T hNS hSeed
    with
      ⟨
        a,
        E,
        ha,
        hE,
        hTail
      ⟩

    exact
      terminalTailH3Control_of_canonicalH3Tail
        ha
        hE
        hTail

  · intro hControl
    intro u T hNS hSeed

    exact
      canonicalH3Tail_of_terminalTailH3Control
        (hControl u T hNS hSeed)

/--
As a corollary, vorticity-independent terminal-tail H³ propagation is more
than enough to discharge the old high-order smoothing interface.

This theorem is a strength comparison, not a claim that the propagation
hypothesis has been proved.
-/
theorem h3SeedProducesEnergyClass_of_terminalTailH3Control
    (hControl : H3SeedProducesTerminalTailH3Control) :
    H3SeedProducesEnergyClass := by

  apply
    h3SeedProducesEnergyClass_of_canonicalH3Tail

  exact
    h3SeedProducesCanonicalH3Tail_iff_terminalTailH3Control.mpr
      hControl

end

end Euclidean
end Bridge
end PrimeTensor
