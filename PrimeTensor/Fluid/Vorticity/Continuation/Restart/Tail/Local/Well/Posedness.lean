import PrimeTensor.Fluid.Vorticity.Continuation.Restart.LocalWellPosedness

/-!
# Tail-aware H³ local well-posedness

The existing `CanonicalH3RealLocalWellPosedness` interface asks a local restart
theorem to work from one H³-integrable slice of an otherwise merely classical
preterminal solution.

On the unbounded spatial domain `ℝ³`, that is stronger than the continuation
argument actually needs.  The caller `H3ControlProducesExtension` already has
`TerminalTailH3Control`: a uniform H³ bound on an entire terminal tail.

This file retains that information in the local restart interface.

For one canonical energy ceiling `E`, `CanonicalH3TailDataFrom u t T E`
asserts H³ integrability and the canonical energy bound at every time in
`[t,T)`.  A tail-aware restart window may use that full strong-solution class
when proving uniqueness/gluing with the newly selected local mild solution.

The key reduction proves that tail-aware local well-posedness is sufficient for
the original `H3ControlProducesExtension` frontier.  Thus classicalization no
longer needs the unnecessarily strong statement that one isolated H³ slice
controls every arbitrary classical preterminal continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/-- Canonical H³ strong-solution data on the old terminal tail `[t,T)`. -/
def CanonicalH3TailDataFrom
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t T E : ℝ) : Prop :=
  ∀ s : ℝ,
    s ∈ Set.Ico t T →
      VelocityH3IntegrableAt u s
        ∧
      velocityH3EnergyAt u s ≤ E

/-- A fixed restart window at one canonical H³ ceiling, retaining the old
solution's H³ class throughout the overlap with the preterminal interval. -/
def CanonicalH3RealTailRestartWindow
    (E τ : ℝ) : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ),
      LoggedPreterminalNavierStokesAdmissible u T
        →
      t ∈ Set.Ioo (0 : ℝ) T
        →
      CanonicalH3TailDataFrom u t T E
        →
      ∃
        (v : SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
        (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
        (S : ℝ),
          t + τ < S
            ∧
          RealRestartAgreesBeforeT u v T
            ∧
          PreterminalNavierStokes3 v p S
            ∧
          RealVelocitySpatialC3 v
            ∧
          RealVelocityThirdJetContinuousOn v S

/-- Per-energy local well-posedness in the actual strong-solution class
available to the continuation caller. -/
def CanonicalH3RealTailLocalWellPosedness : Prop :=
  ∀ E : ℝ,
    1 ≤ E →
      ∃ τ : ℝ,
        0 < τ
          ∧
        CanonicalH3RealTailRestartWindow E τ

/-- The older single-slice local-well-posedness interface implies the
tail-aware one by forgetting all tail information except the anchor slice. -/
theorem canonicalH3RealTailLocalWellPosedness_of_localWellPosedness
    (hLocal : CanonicalH3RealLocalWellPosedness) :
    CanonicalH3RealTailLocalWellPosedness := by
  intro E hE

  rcases hLocal E hE with
    ⟨τ, hτ, hWindow⟩

  refine
    ⟨
      τ,
      hτ,
      ?_
    ⟩

  intro
    u T t
    hNS
    ht
    hTail

  have htTail :
      t ∈ Set.Ico t T :=
    ⟨le_rfl, ht.2⟩

  have hAt :=
    hTail t htTail

  exact
    hWindow
      u T t
      hNS
      ht
      hAt.1
      hAt.2

/-- Tail-aware canonical local well-posedness already suffices to construct the
real restart crossing the candidate terminal time.

The proof is the same terminal-time selection used by the existing uniform
lifespan reduction, except that the uniform old-tail H³ bound is retained and
passed to the local uniqueness/gluing theorem. -/
theorem h3ControlProducesRealRestart_of_tailLocalWellPosedness
    (hLocal : CanonicalH3RealTailLocalWellPosedness) :
    H3ControlProducesRealRestart := by
  intro
    u T
    hAdmissible
    hTail

  rcases hTail with
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
    exact
      one_le_velocityH3CoordinateBudget hM

  rcases hLocal E hE with
    ⟨
      τ,
      hτ,
      hWindow
    ⟩

  have hTM :
      0 < T - a := by
    linarith [ha.2]

  let ε : ℝ :=
    min
      ((T - a) / 2)
      (τ / 2)

  have hHalfTail :
      0 < (T - a) / 2 := by
    linarith

  have hHalfLife :
      0 < τ / 2 := by
    linarith

  have hε :
      0 < ε := by
    dsimp [ε]
    exact lt_min hHalfTail hHalfLife

  have hεTail :
      ε ≤ (T - a) / 2 := by
    dsimp [ε]
    exact min_le_left _ _

  have hεLife :
      ε ≤ τ / 2 := by
    dsimp [ε]
    exact min_le_right _ _

  let t₀ : ℝ :=
    T - ε

  have ht₀Lower :
      a ≤ t₀ := by
    dsimp [t₀]
    linarith

  have ht₀Upper :
      t₀ < T := by
    dsimp [t₀]
    linarith

  have ht₀Positive :
      0 < t₀ := by
    exact
      lt_of_lt_of_le
        ha.1
        ht₀Lower

  have ht₀Old :
      t₀ ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      ht₀Positive,
      ht₀Upper
    ⟩

  have hCanonicalTail :
      CanonicalH3TailDataFrom
        u t₀ T E := by
    intro s hs

    have hsOldTail :
        s ∈ Set.Ico a T := by
      exact
        ⟨
          le_trans ht₀Lower hs.1,
          hs.2
        ⟩

    have hsBound :
        VelocityH3BoundAt u s M :=
      hBound s hsOldTail

    exact
      ⟨
        velocityH3IntegrableAt_of_bound
          hsBound,
        velocityH3EnergyAt_le_coordinateBudget_of_bound
          hsBound
      ⟩

  have hCross :
      T < t₀ + τ := by
    dsimp [t₀]
    linarith

  obtain
    ⟨
      v,
      p,
      S,
      hReach,
      hAgree,
      hPDE,
      hSpatial,
      hThirdOn
    ⟩ :=
      hWindow
        u T t₀
        hAdmissible
        ht₀Old
        hCanonicalTail

  have hTS :
      T < S :=
    lt_trans hCross hReach

  have hTInterior :
      T ∈ Set.Ioo (0 : ℝ) S := by
    exact
      ⟨
        lt_trans ha.1 ha.2,
        hTS
      ⟩

  refine
    ⟨
      v,
      p,
      S,
      hTS,
      hAgree,
      hPDE,
      hSpatial,
      ?_
    ⟩

  intro x

  exact
    hThirdOn
      T
      hTInterior
      x

/-- Tail-aware local well-posedness closes the same H³ continuation frontier
as the stronger single-slice interface. -/
theorem h3ControlProducesExtension_of_tailLocalWellPosedness
    (hLocal : CanonicalH3RealTailLocalWellPosedness) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_realRestart
      (h3ControlProducesRealRestart_of_tailLocalWellPosedness
        hLocal)

end Euclidean
end Bridge
end PrimeTensor
