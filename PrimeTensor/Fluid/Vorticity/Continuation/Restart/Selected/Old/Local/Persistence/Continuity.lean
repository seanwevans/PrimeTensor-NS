import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Selected.Old.Local.Persistence

/-!
# Reduce local H³ persistence to integrability persistence plus right continuity

`Old.LocalPersistence` isolated the canonical short-time statement

    VelocityH3IntegrableAt u t
      ->
    ∃ S > t,
      CanonicalH3TailDataFrom
        u t S (2 * velocityH3EnergyAt u t).

This file splits that statement at its natural analytic seam.

There are two logically different issues:

1. **qualitative persistence**:
   every sufficiently nearby future slice remains H³-integrable;

2. **quantitative control**:
   the normalized canonical H³ energy is right-continuous at the anchor.

Because `velocityH3EnergyAt u t ≥ 1`, right continuity with
`ε = velocityH3EnergyAt u t` gives

    velocityH3EnergyAt u s < 2 * velocityH3EnergyAt u t

on a sufficiently short right neighborhood.

Intersecting that neighborhood with the qualitative H³-persistence interval
gives exactly `H3IntegrableSliceProducesLocalCanonicalH3Tail`.

No PDE estimate is proved here.  The point is to replace one opaque local
persistence proposition by two standard analytic targets with different proof
mechanisms: preservation of spatial integrability and continuity of the finite
H³ energy.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set

noncomputable section

noncomputable local instance axisFintypeH3LocalPersistenceContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Qualitative short-time persistence of H³ integrability from one interior H³
slice.

No quantitative energy ceiling is included.
-/
def H3IntegrableSlicePersistsLocally : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ),
      LoggedPreterminalNavierStokesAdmissible u T →
      t ∈ Set.Ioo (0 : ℝ) T →
      VelocityH3IntegrableAt u t →
      ∃ S : ℝ,
        t < S
          ∧
        S < T
          ∧
        ∀ s : ℝ,
          s ∈ Set.Ico t S →
          VelocityH3IntegrableAt u s

/--
Epsilon formulation of right continuity of the canonical H³ energy at every
H³-integrable interior slice.

Only future times are requested because that is the direction used by restart
and continuation.
-/
def H3EnergyRightContinuousAtIntegrableSlice : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ),
      LoggedPreterminalNavierStokesAdmissible u T →
      t ∈ Set.Ioo (0 : ℝ) T →
      VelocityH3IntegrableAt u t →
      ∀ ε : ℝ,
        0 < ε →
        ∃ δ : ℝ,
          0 < δ
            ∧
          ∀ s : ℝ,
            t ≤ s →
            s < T →
            s < t + δ →
            |velocityH3EnergyAt u s - velocityH3EnergyAt u t| < ε

/--
Qualitative H³-integrability persistence together with right continuity of the
canonical energy yields the exact `2E` local canonical H³ tail used by the
selected restart.

The factor two is not an additional estimate: it follows by taking
`ε = E(t)` in the right-continuity statement.
-/
theorem h3IntegrableSliceProducesLocalCanonicalH3Tail_of_persistence_of_energyRightContinuous
    (hPersist : H3IntegrableSlicePersistsLocally)
    (hContinuous : H3EnergyRightContinuousAtIntegrableSlice) :
    H3IntegrableSliceProducesLocalCanonicalH3Tail := by

  intro u T t hNS ht hInt

  rcases
    hPersist u T t hNS ht hInt
  with
    ⟨
      S₀,
      htS₀,
      hS₀T,
      hIntTail
    ⟩

  let E : ℝ :=
    velocityH3EnergyAt u t

  have hEOne :
      1 ≤ E := by
    dsimp only [E]
    exact
      one_le_velocityH3EnergyAt u t

  have hEPos :
      0 < E :=
    lt_of_lt_of_le zero_lt_one hEOne

  rcases
    hContinuous u T t hNS ht hInt E hEPos
  with
    ⟨
      δ,
      hδ,
      hEnergyNear
    ⟩

  let S : ℝ :=
    min S₀ (t + δ / 2)

  have htHalf :
      t < t + δ / 2 := by
    linarith

  have htS :
      t < S := by
    dsimp only [S]
    exact
      lt_min htS₀ htHalf

  have hSS₀ :
      S ≤ S₀ := by
    dsimp only [S]
    exact
      min_le_left _ _

  have hSHalf :
      S ≤ t + δ / 2 := by
    dsimp only [S]
    exact
      min_le_right _ _

  have hST :
      S < T :=
    lt_of_le_of_lt hSS₀ hS₀T

  refine
    ⟨
      S,
      htS,
      hST,
      ?_
    ⟩

  intro s hs

  have hsS₀ :
      s < S₀ :=
    lt_of_lt_of_le hs.2 hSS₀

  have hsInt :
      VelocityH3IntegrableAt u s :=
    hIntTail s
      ⟨
        hs.1,
        hsS₀
      ⟩

  have hsHalf :
      s < t + δ / 2 :=
    lt_of_lt_of_le hs.2 hSHalf

  have hsDelta :
      s < t + δ := by
    linarith

  have hsT :
      s < T :=
    lt_trans hs.2 hST

  have hAbs :
      |velocityH3EnergyAt u s - velocityH3EnergyAt u t| < E :=
    hEnergyNear
      s
      hs.1
      hsT
      hsDelta

  have hDiff :
      velocityH3EnergyAt u s - velocityH3EnergyAt u t < E :=
    lt_of_le_of_lt
      (le_abs_self
        (velocityH3EnergyAt u s - velocityH3EnergyAt u t))
      hAbs

  have hEnergy :
      velocityH3EnergyAt u s
        ≤
      2 * velocityH3EnergyAt u t := by
    dsimp only [E] at hDiff
    linarith

  exact
    ⟨
      hsInt,
      hEnergy
    ⟩

/--
The same two local analytic inputs therefore already imply local old-branch
high-order regularization from every H³ seed.
-/
theorem h3SeedProducesLocalEnergyClass_of_persistence_of_energyRightContinuous
    (hPersist : H3IntegrableSlicePersistsLocally)
    (hContinuous : H3EnergyRightContinuousAtIntegrableSlice) :
    H3SeedProducesLocalEnergyClass := by

  exact
    h3SeedProducesLocalEnergyClass_of_localCanonicalH3Persistence
      (h3IntegrableSliceProducesLocalCanonicalH3Tail_of_persistence_of_energyRightContinuous
        hPersist
        hContinuous)

end

end Euclidean
end Bridge
end PrimeTensor
