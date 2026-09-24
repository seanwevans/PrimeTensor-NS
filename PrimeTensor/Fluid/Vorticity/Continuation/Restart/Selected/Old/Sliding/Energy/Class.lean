import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Selected.Old.Energy.Class

/-!
# Canonical H³ tail gives an old energy class by sliding the restart anchor

`Old.EnergyClass` previously packaged a canonical H³ tail into
`PreterminalH3EnergyClass` only when one fixed selected restart radius covered
the whole remaining lifetime.

That coverage condition is unnecessary.

If

    CanonicalH3TailDataFrom u a T E

holds, then every later old slice in `[a,T)` carries the same canonical H³
ceiling `E`.  The unit-viscosity restart radius

    R = h3FinHeatLerayRestartRadius 1 E

is therefore the same positive number at every such slice.

For each target time `s` on a slightly later tail, choose a fresh anchor
`t₀ < s` with

    0 < s - t₀ < R

and `a ≤ t₀`.  Restrict the canonical H³ tail to `t₀`, launch the already
closed selected/old overlap machinery there, and transfer:

* selected velocity spatial `C⁵` to the old velocity at `s`;
* selected pressure spatial `C⁴` to the old pressure witness at `s`.

Because the anchor is allowed to slide with `s`, no single restart interval
needs to cover `[a,T)`.

The final section isolates the true remaining seed-side proposition:
propagation of one H³ seed into a canonical H³ terminal tail.  Once that
propagation is available, the high-order energy class follows automatically.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SlidingEnergyClass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical H³ tail data restricts to every later tail start. -/
theorem canonicalH3TailDataFrom_mono_start
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a t T E : ℝ}
    (hat : a ≤ t)
    (htT : t < T)
    (hTail : CanonicalH3TailDataFrom u a T E) :
    CanonicalH3TailDataFrom u t T E := by
  intro s hs
  exact
    hTail s
      ⟨
        le_trans hat hs.1,
        hs.2
      ⟩

/--
Any canonical H³ terminal tail produces an actual old
`PreterminalH3EnergyClass` after moving the left endpoint once.

No hypothesis compares the remaining lifetime with one restart radius.
-/
theorem h3Preterminal_energyClass_of_canonicalTail
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ha : a ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u a T E) :
    ∃ b : ℝ,
      PreterminalH3EnergyClass u b T := by

  let b : ℝ :=
    (a + T) / 2

  have hab :
      a < b := by
    dsimp only [b]
    linarith [ha.2]

  have hbT :
      b < T := by
    dsimp only [b]
    linarith [ha.2]

  have hb0 :
      0 < b :=
    lt_trans ha.1 hab

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  have hR :
      0 < R := by
    dsimp only [R]
    exact
      h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
        (one_pos : (0 : ℝ) < 1)
        hE

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  have hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T := by
    dsimp only [pOld]
    exact Classical.choose_spec hNS

  refine
    ⟨
      b,
      {
        terminal_start := ⟨hb0, hbT⟩
        velocity_spatial_five := ?_
        pressure_witness := ?_
      }
    ⟩

  · intro s hs j i k

    change
      SpatialC3
        (spatial3.d i
          (spatial3.d k
            (loggedVelocityComponent u s j)))

    have has :
        a < s := by
      exact
        lt_of_lt_of_le
          hab
          hs.1

    have hHalfGap :
        0 < (s - a) / 2 := by
      linarith

    have hHalfR :
        0 < R / 2 := by
      linarith

    let q : ℝ :=
      min (R / 2) ((s - a) / 2)

    have hq0 :
        0 < q := by
      dsimp only [q]
      exact
        lt_min hHalfR hHalfGap

    have hqHalfR :
        q ≤ R / 2 := by
      dsimp only [q]
      exact
        min_le_left _ _

    have hqHalfGap :
        q ≤ (s - a) / 2 := by
      dsimp only [q]
      exact
        min_le_right _ _

    have hHalfRLt :
        R / 2 < R := by
      linarith

    have hqRlt :
        q < R :=
      lt_of_le_of_lt
        hqHalfR
        hHalfRLt

    have hqR :
        q ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E := by
      dsimp only [R] at hqRlt
      exact le_of_lt hqRlt

    let t₀ : ℝ :=
      s - q

    have hat₀ :
        a ≤ t₀ := by
      dsimp only [t₀]
      linarith [hqHalfGap]

    have ht₀s :
        t₀ < s := by
      dsimp only [t₀]
      linarith

    have ht₀T :
        t₀ < T :=
      lt_trans ht₀s hs.2

    have ht₀0 :
        0 < t₀ :=
      lt_of_lt_of_le
        ha.1
        hat₀

    have ht₀ :
        t₀ ∈ Set.Ioo (0 : ℝ) T :=
      ⟨ht₀0, ht₀T⟩

    have hTail₀ :
        CanonicalH3TailDataFrom u t₀ T E :=
      canonicalH3TailDataFrom_mono_start
        hat₀
        ht₀T
        hTail

    have htq :
        t₀ + q = s := by
      dsimp only [t₀]
      ring

    have hEnd :
        t₀ + q < T := by
      simpa only [htq] using hs.2

    have hOld :=
      h3Preterminal_oldVelocity_secondPartial_spatialC3_of_canonicalTail
        (q := q)
        hNS
        ht₀
        hE
        hTail₀
        hq0
        hqR
        hEnd
        j i k

    simpa only [htq] using hOld

  · refine
      ⟨
        pOld,
        hPDE,
        ?_
      ⟩

    intro s hs i

    dsimp only [pOld]

    have has :
        a < s := by
      exact
        lt_of_lt_of_le
          hab
          hs.1

    have hHalfGap :
        0 < (s - a) / 2 := by
      linarith

    have hHalfR :
        0 < R / 2 := by
      linarith

    let q : ℝ :=
      min (R / 2) ((s - a) / 2)

    have hq0 :
        0 < q := by
      dsimp only [q]
      exact
        lt_min hHalfR hHalfGap

    have hqHalfR :
        q ≤ R / 2 := by
      dsimp only [q]
      exact
        min_le_left _ _

    have hqHalfGap :
        q ≤ (s - a) / 2 := by
      dsimp only [q]
      exact
        min_le_right _ _

    have hHalfRLt :
        R / 2 < R := by
      linarith

    have hqR :
        q < h3FinHeatLerayRestartRadius (1 : ℝ) E := by
      have hqR' :
          q < R :=
        lt_of_le_of_lt
          hqHalfR
          hHalfRLt
      simpa only [R] using hqR'

    let t₀ : ℝ :=
      s - q

    have hat₀ :
        a ≤ t₀ := by
      dsimp only [t₀]
      linarith [hqHalfGap]

    have ht₀s :
        t₀ < s := by
      dsimp only [t₀]
      linarith

    have ht₀T :
        t₀ < T :=
      lt_trans ht₀s hs.2

    have ht₀0 :
        0 < t₀ :=
      lt_of_lt_of_le
        ha.1
        hat₀

    have ht₀ :
        t₀ ∈ Set.Ioo (0 : ℝ) T :=
      ⟨ht₀0, ht₀T⟩

    have hTail₀ :
        CanonicalH3TailDataFrom u t₀ T E :=
      canonicalH3TailDataFrom_mono_start
        hat₀
        ht₀T
        hTail

    have htq :
        t₀ + q = s := by
      dsimp only [t₀]
      ring

    have hEnd :
        t₀ + q < T := by
      simpa only [htq] using hs.2

    have hOld :=
      h3Preterminal_oldPressure_spatialDerivative_spatialC3_of_canonicalTail
        (q := q)
        hNS
        ht₀
        hE
        hTail₀
        hq0
        hqR
        hEnd
        i

    simpa only [htq] using hOld

/-!
## The actual remaining seed-side propagation frontier
-/

/--
A single H³ seed propagates to some uniformly bounded canonical H³ terminal
tail.

This is strictly an H³ propagation statement.  High-order C5/C4 smoothing is
no longer part of this frontier: `h3Preterminal_energyClass_of_canonicalTail`
derives that regularity afterward by sliding local selected restarts.
-/
def H3SeedProducesCanonicalH3Tail : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalNavierStokesAdmissible u T →
      PreterminalH3Seed u T →
      ∃
        (a E : ℝ),
          a ∈ Set.Ioo (0 : ℝ) T
            ∧
          1 ≤ E
            ∧
          CanonicalH3TailDataFrom u a T E

/--
Canonical H³ tail propagation from the seed implies the old
`H3SeedProducesEnergyClass` interface.

Thus the former "smoothing" hypothesis factors through a purely H³ propagation
frontier.
-/
theorem h3SeedProducesEnergyClass_of_canonicalH3Tail
    (hPropagate : H3SeedProducesCanonicalH3Tail) :
    H3SeedProducesEnergyClass := by

  intro u T hNS hSeed

  rcases
    hPropagate u T hNS hSeed
  with
    ⟨
      a,
      E,
      ha,
      hE,
      hTail
    ⟩

  exact
    h3Preterminal_energyClass_of_canonicalTail
      hNS
      ha
      hE
      hTail

end

end Euclidean
end Bridge
end PrimeTensor
