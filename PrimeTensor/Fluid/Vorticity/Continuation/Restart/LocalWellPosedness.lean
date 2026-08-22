import PrimeTensor.Fluid.Vorticity.Continuation.Restart.EnergyLifespan

/-!
# Per-energy local well-posedness form of the H³ restart frontier

`UniformCanonicalH3RealRestartLifespan` packages the remaining classical
restart input by first choosing a global function

    lifespan : ℝ → ℝ.

That function is not mathematical content.  The actual local-well-posedness
statement is pointwise in the H³ energy ceiling: for every normalized ceiling
`E`, there is one positive time window which works uniformly for every
admissible restart slice whose canonical H³ energy is at most `E`.

This file removes the global choice function from the analytic frontier.  It
proves that the per-energy local-well-posedness statement is equivalent to the
existing canonical restart-lifespan interface.  Thus any eventual classical
Navier--Stokes local-existence proof can target the per-energy proposition
without reproducing continuation bookkeeping.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/--
A fixed restart window at one canonical H³ energy ceiling.

The number `τ` is uniform over the original preterminal solution, terminal
time, and interior restart time.  Only the scalar energy ceiling `E` is held
fixed.
-/
def CanonicalH3RealRestartWindow
    (E τ : ℝ) : Prop :=
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
        (
          v :
            PrimeTensor.SpaceTimeVectorField
              ℝ ℝ ℝ Depth.three
        )
        (
          p :
            PrimeTensor.SpaceTimeScalarField
              ℝ ℝ ℝ Depth.three
        )
        (S : ℝ),
          t + τ < S
            ∧
          RealRestartAgreesBeforeT
            u v T
            ∧
          PreterminalNavierStokes3
            v p S
            ∧
          RealVelocitySpatialC3
            v
            ∧
          RealVelocityThirdJetContinuousOn
            v S

/--
The remaining local-well-posedness input, with no global choice function.

For every normalized canonical H³ ceiling `E ≥ 1`, there is a positive restart
window `τ` that works uniformly for all admissible restart slices below that
ceiling.
-/
def CanonicalH3RealLocalWellPosedness : Prop :=
  ∀ E : ℝ,
    1 ≤ E →
      ∃ τ : ℝ,
        0 < τ
          ∧
        CanonicalH3RealRestartWindow
          E τ

/--
A canonical restart-lifespan function immediately gives the per-energy local
well-posedness statement by evaluating it at the supplied ceiling.
-/
theorem canonicalH3RealLocalWellPosedness_of_uniformLifespan
    (
      hUniform :
        UniformCanonicalH3RealRestartLifespan
    ) :
    CanonicalH3RealLocalWellPosedness := by

  rcases hUniform with
    ⟨
      lifespan,
      hPositive,
      hRestart
    ⟩

  intro E hE

  refine
    ⟨
      lifespan E,
      hPositive E hE,
      ?_
    ⟩

  intro
    u T t
    hAdmissible
    ht
    hIntegrable
    hEnergy

  exact
    hRestart
      u T t E
      hAdmissible
      ht
      hE
      hIntegrable
      hEnergy

/--
Conversely, per-energy local well-posedness supplies the existing uniform
canonical restart interface by classical choice.

For energies below the normalized range `E ≥ 1`, the chosen function is
irrelevant; the interface never asks either positivity or restart behavior
there.
-/
theorem uniformCanonicalH3RealRestartLifespan_of_localWellPosedness
    (
      hLocal :
        CanonicalH3RealLocalWellPosedness
    ) :
    UniformCanonicalH3RealRestartLifespan := by

  classical

  have hChoice :
      ∀ E : ℝ,
        ∃ τ : ℝ,
          (
            1 ≤ E →
              0 < τ
          )
            ∧
          (
            1 ≤ E →
              CanonicalH3RealRestartWindow
                E τ
          ) := by

    intro E

    by_cases hE : 1 ≤ E

    · rcases hLocal E hE with
        ⟨
          τ,
          hτ,
          hWindow
        ⟩

      exact
        ⟨
          τ,
          (fun _ => hτ),
          (fun _ => hWindow)
        ⟩

    · exact
        ⟨
          1,
          (fun h => False.elim (hE h)),
          (fun h => False.elim (hE h))
        ⟩

  let lifespan : ℝ → ℝ :=
    fun E => Classical.choose (hChoice E)

  have hLifespanSpec :
      ∀ E : ℝ,
        (
          1 ≤ E →
            0 < lifespan E
        )
          ∧
        (
          1 ≤ E →
            CanonicalH3RealRestartWindow
              E (lifespan E)
        ) := by

    intro E

    exact
      Classical.choose_spec
        (hChoice E)

  refine
    ⟨
      lifespan,
      ?_,
      ?_
    ⟩

  · intro E hE

    exact
      (hLifespanSpec E).1 hE

  · intro
      u T t E
      hAdmissible
      ht
      hE
      hIntegrable
      hEnergy

    have hWindow :
        CanonicalH3RealRestartWindow
          E (lifespan E) :=
      (hLifespanSpec E).2 hE

    exact
      hWindow
        u T t
        hAdmissible
        ht
        hIntegrable
        hEnergy

/--
The per-energy local-well-posedness statement and the global canonical
lifespan packaging contain exactly the same mathematical information.
-/
theorem canonicalH3RealLocalWellPosedness_iff_uniformLifespan :
    CanonicalH3RealLocalWellPosedness
      ↔
    UniformCanonicalH3RealRestartLifespan := by

  constructor

  · exact
      uniformCanonicalH3RealRestartLifespan_of_localWellPosedness

  · exact
      canonicalH3RealLocalWellPosedness_of_uniformLifespan

/--
Per-energy local well posedness therefore discharges the H³ continuation
frontier through the already-proved restart reduction.
-/
theorem h3ControlProducesExtension_of_localWellPosedness
    (
      hLocal :
        CanonicalH3RealLocalWellPosedness
    ) :
    H3ControlProducesExtension := by

  exact
    h3ControlProducesExtension_of_canonicalEnergyLifespan
      (
        uniformCanonicalH3RealRestartLifespan_of_localWellPosedness
          hLocal
      )

end Euclidean
end Bridge
end PrimeTensor
