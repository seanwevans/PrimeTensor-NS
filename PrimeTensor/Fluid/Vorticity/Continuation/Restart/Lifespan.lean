import PrimeTensor.Fluid.Vorticity.Continuation.Restart

/-!
# Uniform H³ restart lifespan

The remaining classical continuation input can be sharpened to the standard
uniform-lifespan statement.

If the H³ size at an interior restart time is bounded by `M`, local
well-posedness should provide a positive lifespan depending only on `M`.
Given uniform H³ control on a terminal tail, choose the restart time close
enough to `T` that this lifespan crosses the terminal time.

This file formalizes exactly that reduction.  No Navier--Stokes existence
theorem is asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/--
Time continuity of the complete real third spatial jet throughout the open
existence interval `(0,S)`.
-/
def RealVelocityThirdJetContinuousOn
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (S : ℝ) : Prop :=
  ∀
    (t : ℝ),
      t ∈ Set.Ioo (0 : ℝ) S →
      ∀ x : Point3,
        RealVelocityThirdJetContinuousAt
          v t x

/--
Uniform local H³ restart lifespan.

There is a positive lifespan `lifespan M`, depending only on the common H³
bound `M`, such that restarting at any interior time `t` with
`VelocityH3BoundAt u t M` produces a real Navier--Stokes continuation at least
until `t + lifespan M`.

The output field is required to agree with the original logged solution on the
whole old interval `(0,T)`.  Analytically, this is the usual local existence
plus uniqueness/gluing statement.

`RealVelocitySpatialC3` is total-field packaging for the current continuation
API.  The genuinely local high-order smoothing statement is
`RealVelocityThirdJetContinuousOn v S`.
-/
def UniformH3RealRestartLifespan : Prop :=
  ∃ lifespan : ℝ → ℝ,
    (
      ∀ M : ℝ,
        0 ≤ M →
          0 < lifespan M
    )
      ∧
    ∀
      (
        u :
          PrimeTensor.SpaceTimeVectorField
            ℝ ℝ PrimeTensor.MulReal Depth.three
      )
      (T t M : ℝ),
        LoggedPreterminalNavierStokesAdmissible
            u T
          →
        t ∈ Set.Ioo (0 : ℝ) T
          →
        0 ≤ M
          →
        VelocityH3BoundAt
            u t M
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
            t + lifespan M < S
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
A uniform positive H³ restart lifespan implies the real-coordinate restart
frontier.

The proof is the standard terminal-time argument: choose a restart time
`t₀ ∈ [a,T)` so close to `T` that

    T - t₀ < lifespan M.

The uniform tail bound supplies the H³ hypothesis at `t₀`, and the guaranteed
restart then extends strictly beyond `T`.
-/
theorem h3ControlProducesRealRestart_of_uniformLifespan
    (
      hUniform :
        UniformH3RealRestartLifespan
    ) :
    H3ControlProducesRealRestart := by

  rcases hUniform with
    ⟨
      lifespan,
      hLifespanPositive,
      hRestart
    ⟩

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

  have hTM :
      0 < T - a := by
    linarith [ha.2]

  have hLife :
      0 < lifespan M :=
    hLifespanPositive
      M
      hM

  let ε : ℝ :=
    min
      ((T - a) / 2)
      ((lifespan M) / 2)

  have hHalfTail :
      0 < (T - a) / 2 := by
    linarith

  have hHalfLife :
      0 < (lifespan M) / 2 := by
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
      ε ≤ (lifespan M) / 2 := by
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
    exact lt_of_lt_of_le
      ha.1
      ht₀Lower

  have ht₀Old :
      t₀ ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      ht₀Positive,
      ht₀Upper
    ⟩

  have ht₀Tail :
      t₀ ∈ Set.Ico a T :=
    ⟨
      ht₀Lower,
      ht₀Upper
    ⟩

  have hAt :
      VelocityH3BoundAt
        u t₀ M :=
    hBound
      t₀
      ht₀Tail

  have hCross :
      T < t₀ + lifespan M := by
    dsimp [t₀]
    linarith

  obtain
    ⟨
      v,
      p,
      S,
      hReach,
      hAgree,
      s,
      hSpatial,
      hThirdOn
    ⟩ :=
      hRestart
        u
        T
        t₀
        M
        hAdmissible
        ht₀Old
        hM
        hAt

  have hTS :
      T < S :=
    lt_trans
      hCross
      hReach

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
      s,
      hSpatial,
      ?_
    ⟩

  intro x

  exact
    hThirdOn
      T
      hTInterior
      x

/--
Consequently, the uniform-lifespan theorem also discharges the original
tail-H³ continuation frontier.
-/
theorem h3ControlProducesExtension_of_uniformLifespan
    (
      hUniform :
        UniformH3RealRestartLifespan
    ) :
    H3ControlProducesExtension := by

  apply
    h3ControlProducesExtension_of_realRestart

  exact
    h3ControlProducesRealRestart_of_uniformLifespan
      hUniform

end Euclidean
end Bridge
end PrimeTensor
