import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.HighOrder.Old.LocalPersistenceEnergyDerivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureWitness

/-!
# The standard preterminal H³ path class closes the high-order energy class

The recent seed-level reductions exposed a mismatch in the original
preterminal solution interface.

`LoggedPreterminalNavierStokesAdmissible u T` is a pointwise classical
Navier--Stokes notion:

* every strict-time velocity slice is spatially `C³`;
* the velocity is `C¹` in time pointwise;
* the equation holds on `(0,T)`.

It does **not** say that the whole-space velocity remains in `H³` at nearby
times, nor that its H³ norm is continuous.  Those are normally part of the
maximal strong-solution class used in the BKM theorem.

Without some whole-space admissibility condition, a single H³ slice cannot be
expected to control spatial behavior at infinity at later times merely from
pointwise `C³` regularity.

This file therefore introduces the minimal H³-path refinement needed by the
current formalization:

    LoggedPreterminalH3PathAdmissible u T

consists of

1. the existing logged preterminal Navier--Stokes witness;
2. `VelocityH3IntegrableAt u s` at every strict preterminal time;
3. continuity of the scalar canonical H³ energy at every strict preterminal
   time.

This is weaker than asserting a full Banach-valued `C((0,T);H³)` path, but it
records exactly the two consequences of that standard strong-solution
hypothesis used here.

The key point is that **no uniform H³ terminal-tail bound is required**.

At each target time `s<T`:

* continuity bounds H³ energy on a small two-sided neighborhood of `s`;
* choose an anchor `t₀<s` inside that neighborhood;
* make `s-t₀` smaller than the positive restart radius for that local ceiling;
* restrict the old PDE to a short terminal time `S>s`;
* apply the already-closed selected/old transfer on `[t₀,S)`.

The restart window is allowed to depend on `s`.  This gives old velocity `C⁵`
and old pressure `C⁴` at every point of a fixed late tail, hence an actual
`PreterminalH3EnergyClass`.

Thus the old global `H3SeedProducesEnergyClass` smoothing axiom is unnecessary
once the preterminal solution is placed in the standard H³ path class.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3PathAdmissible
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Minimal strong H³ path admissibility -/

/--
Minimal H³-path refinement of the pointwise classical preterminal
Navier--Stokes interface.

`velocity_h3_integrable` is the qualitative whole-space requirement.
`energy_continuousAt` is the scalar norm-continuity consequence used to choose
uniformly bounded local restart windows.
-/
structure LoggedPreterminalH3PathAdmissible
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) : Prop where

  navier_stokes :
    LoggedPreterminalNavierStokesAdmissible u T

  velocity_h3_integrable :
    ∀ s : ℝ,
      s ∈ Set.Ioo (0 : ℝ) T →
      VelocityH3IntegrableAt u s

  energy_continuousAt :
    ∀ s : ℝ,
      s ∈ Set.Ioo (0 : ℝ) T →
      ContinuousAt
        (velocityH3EnergyAt u)
        s

/--
Every strict slice of an H³-path-admissible solution is a valid old H³ seed.
-/
theorem LoggedPreterminalH3PathAdmissible.preterminalH3Seed_at
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    PreterminalH3Seed u T := by

  exact
    preterminalH3Seed_of_velocityH3IntegrableAt
      hs
      (hH3.velocity_h3_integrable s hs)

/-! ## A local canonical restart window around every strict time -/

/--
Around every strict time of an H³-path-admissible solution there is a short
canonical H³ restart window whose left anchor lies strictly before the target,
whose right endpoint lies strictly after it, and whose target elapsed time is
strictly inside the corresponding unit-viscosity restart radius.
-/
theorem LoggedPreterminalH3PathAdmissible.exists_localCanonicalRestartWindowAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    ∃
      (t₀ S E : ℝ),
        t₀ ∈ Set.Ioo (0 : ℝ) S
          ∧
        S < T
          ∧
        1 ≤ E
          ∧
        CanonicalH3TailDataFrom u t₀ S E
          ∧
        0 < s - t₀
          ∧
        s - t₀ <
          h3FinHeatLerayRestartRadius (1 : ℝ) E
          ∧
        t₀ + (s - t₀) = s
          ∧
        s < S := by

  let E₀ : ℝ :=
    velocityH3EnergyAt u s

  let E : ℝ :=
    2 * E₀

  have hE₀One :
      1 ≤ E₀ := by
    dsimp only [E₀]
    exact one_le_velocityH3EnergyAt u s

  have hE₀Pos :
      0 < E₀ :=
    lt_of_lt_of_le zero_lt_one hE₀One

  have hE :
      1 ≤ E := by
    dsimp only [E]
    linarith

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  have hR :
      0 < R := by
    dsimp only [R]
    exact
      h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
        (one_pos : (0 : ℝ) < 1)
        hE

  rcases
    (Metric.continuousAt_iff.mp
      (hH3.energy_continuousAt s hs))
      E₀ hE₀Pos
  with
    ⟨
      δ,
      hδ,
      hNear
    ⟩

  let ε : ℝ :=
    min
      (s / 2)
      (min
        ((T - s) / 2)
        (min
          (δ / 2)
          (R / 2)))

  have hsHalf :
      0 < s / 2 := by
    linarith [hs.1]

  have hTailHalf :
      0 < (T - s) / 2 := by
    linarith [hs.2]

  have hδHalf :
      0 < δ / 2 := by
    linarith

  have hRHalf :
      0 < R / 2 := by
    linarith

  have hε :
      0 < ε := by
    dsimp only [ε]
    exact
      lt_min
        hsHalf
        (lt_min
          hTailHalf
          (lt_min hδHalf hRHalf))

  have hεS :
      ε ≤ s / 2 := by
    dsimp only [ε]
    exact min_le_left _ _

  have hεTail :
      ε ≤ (T - s) / 2 := by
    dsimp only [ε]
    exact
      le_trans
        (min_le_right _ _)
        (min_le_left _ _)

  have hεδ :
      ε ≤ δ / 2 := by
    dsimp only [ε]
    exact
      le_trans
        (min_le_right _ _)
        (le_trans
          (min_le_right _ _)
          (min_le_left _ _))

  have hεR :
      ε ≤ R / 2 := by
    dsimp only [ε]
    exact
      le_trans
        (min_le_right _ _)
        (le_trans
          (min_le_right _ _)
          (min_le_right _ _))

  have hεLtδ :
      ε < δ := by
    have hδHalfLt :
        δ / 2 < δ := by
      linarith
    exact
      lt_of_le_of_lt hεδ hδHalfLt

  have hεLtR :
      ε < R := by
    have hRHalfLt :
        R / 2 < R := by
      linarith
    exact
      lt_of_le_of_lt hεR hRHalfLt

  let t₀ : ℝ :=
    s - ε

  let S : ℝ :=
    s + ε

  have ht₀0 :
      0 < t₀ := by
    dsimp only [t₀]
    linarith [hεS, hs.1]

  have ht₀S :
      t₀ < S := by
    dsimp only [t₀, S]
    linarith

  have hST :
      S < T := by
    dsimp only [S]
    linarith [hεTail, hs.2]

  have hsS :
      s < S := by
    dsimp only [S]
    linarith

  have hTail :
      CanonicalH3TailDataFrom u t₀ S E := by
    intro r hr

    have hr0 :
        0 < r := by
      exact
        lt_of_lt_of_le
          ht₀0
          hr.1

    have hrT :
        r < T :=
      lt_trans hr.2 hST

    have hrAbs :
        r ∈ Set.Ioo (0 : ℝ) T :=
      ⟨hr0, hrT⟩

    have hrInt :
        VelocityH3IntegrableAt u r :=
      hH3.velocity_h3_integrable r hrAbs

    have hdist :
        dist r s < δ := by
      rw [Real.dist_eq]
      apply abs_lt.mpr
      constructor
      · dsimp only [t₀] at hr
        linarith [hr.1, hεLtδ]
      · dsimp only [S] at hr
        linarith [hr.2, hεLtδ]

    have hEnergyDist :
        dist
            (velocityH3EnergyAt u r)
            (velocityH3EnergyAt u s)
          <
        E₀ :=
      hNear hdist

    have hAbs :
        |velocityH3EnergyAt u r -
            velocityH3EnergyAt u s|
          <
        E₀ := by
      simpa only [Real.dist_eq] using hEnergyDist

    have hUpper :
        velocityH3EnergyAt u r -
            velocityH3EnergyAt u s
          <
        E₀ :=
      lt_of_le_of_lt
        (le_abs_self
          (velocityH3EnergyAt u r -
            velocityH3EnergyAt u s))
        hAbs

    have hEnergy :
        velocityH3EnergyAt u r ≤ E := by
      dsimp only [E, E₀] at hUpper ⊢
      linarith

    exact
      ⟨
        hrInt,
        hEnergy
      ⟩

  refine
    ⟨
      t₀,
      S,
      E,
      ⟨ht₀0, ht₀S⟩,
      hST,
      hE,
      hTail,
      ?_,
      ?_,
      ?_,
      hsS
    ⟩

  · dsimp only [t₀]
    linarith

  · dsimp only [t₀, R] at hεLtR ⊢
    linarith

  · dsimp only [t₀]
    ring

/-! ## Pressure transfer to an explicit pressure witness -/

/--
The local pressure-C4 transfer can be expressed for any pressure witness for
the same preterminal velocity, not only `Classical.choose hNS`.

Pressure-gradient uniqueness transports the already-proved C3 regularity of
the chosen pressure gradient to the supplied witness.
-/
theorem h3Preterminal_pressureWitness_spatialDerivative_spatialC3_of_canonicalTail
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hq0 : 0 < q)
    (hqR :
      q < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hEnd : t + q < T)
    (i : PrimeTensor.Axis Depth.three) :
    SpatialC3
      (spatial3.d
        i
        (p (t + q))) := by

  have hChosen :
      SpatialC3
        (spatial3.d
          i
          ((Classical.choose hNS :
            SpaceTimeScalarField ℝ ℝ ℝ Depth.three) (t + q))) :=
    h3Preterminal_oldPressure_spatialDerivative_spatialC3_of_canonicalTail
      hNS
      ht
      hE
      hTail
      hq0
      hqR
      hEnd
      i

  have hAbs :
      t + q ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith [ht.1, hq0]
    · exact hEnd

  have hGradientEq :
      spatial3.d
          i
          ((Classical.choose hNS :
            SpaceTimeScalarField ℝ ℝ ℝ Depth.three) (t + q))
        =
      spatial3.d
          i
          (p (t + q)) := by
    funext x
    exact
      preterminalNavierStokes3_pressureGradient_eq
        (Classical.choose_spec hNS)
        hPDE
        hAbs
        x
        i

  rw [← hGradientEq]

  exact hChosen

/-! ## H³ path admissibility -> old high-order energy class -/

/--
A standard preterminal H³ path already produces the old high-order energy
class.

No uniform H³ bound toward the terminal time is assumed.  Each target slice
uses its own bounded local neighborhood and its own selected restart.
-/
theorem h3Preterminal_energyClass_of_h3PathAdmissible
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) :
    ∃ b : ℝ,
      PreterminalH3EnergyClass u b T := by

  let hNS :
      LoggedPreterminalNavierStokesAdmissible u T :=
    hH3.navier_stokes

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  have hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T := by
    dsimp only [pOld, hNS]
    exact
      Classical.choose_spec hH3.navier_stokes

  have hT :
      0 < T :=
    hPDE.positive_terminal

  let b : ℝ :=
    T / 2

  have hb0 :
      0 < b := by
    dsimp only [b]
    linarith

  have hbT :
      b < T := by
    dsimp only [b]
    linarith

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

    have hsAbs :
        s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨
        lt_of_lt_of_le hb0 hs.1,
        hs.2
      ⟩

    rcases
      hH3.exists_localCanonicalRestartWindowAt hsAbs
    with
      ⟨
        t₀,
        S,
        E,
        ht₀,
        hST,
        hE,
        hTail,
        hq0,
        hqR,
        hts,
        hsS
      ⟩

    have hS :
        0 < S :=
      lt_trans ht₀.1 ht₀.2

    have hNSShort :
        LoggedPreterminalNavierStokesAdmissible u S :=
      loggedPreterminalNavierStokesAdmissible_mono_terminal
        hNS
        hS
        (le_of_lt hST)

    have hOld :=
      h3Preterminal_oldVelocity_secondPartial_spatialC3_of_canonicalTail
        (q := s - t₀)
        hNSShort
        ht₀
        hE
        hTail
        hq0
        (le_of_lt hqR)
        (by simpa only [hts] using hsS)
        j i k

    simpa only [hts] using hOld

  · refine
      ⟨
        pOld,
        hPDE,
        ?_
      ⟩

    intro s hs i

    have hsAbs :
        s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨
        lt_of_lt_of_le hb0 hs.1,
        hs.2
      ⟩

    rcases
      hH3.exists_localCanonicalRestartWindowAt hsAbs
    with
      ⟨
        t₀,
        S,
        E,
        ht₀,
        hST,
        hE,
        hTail,
        hq0,
        hqR,
        hts,
        hsS
      ⟩

    have hS :
        0 < S :=
      lt_trans ht₀.1 ht₀.2

    have hPDEShort :
        PreterminalNavierStokes3
          (logSpaceTimeVectorField u)
          pOld
          S :=
      hPDE.mono_terminal
        hS
        (le_of_lt hST)

    let hNSShort :
        LoggedPreterminalNavierStokesAdmissible u S :=
      ⟨pOld, hPDEShort⟩

    have hOld :=
      h3Preterminal_pressureWitness_spatialDerivative_spatialC3_of_canonicalTail
        (q := s - t₀)
        hNSShort
        pOld
        hPDEShort
        ht₀
        hE
        hTail
        hq0
        hqR
        (by simpa only [hts] using hsS)
        i

    simpa only [hts] using hOld

/--
Global interface corresponding to the standard H³ strong-solution class.
-/
def H3PathAdmissibleProducesEnergyClass : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∃ b : ℝ,
        PreterminalH3EnergyClass u b T

/--
The H³-path-admissible energy-class interface is closed by the local
sliding-window restart argument.
-/
theorem h3PathAdmissibleProducesEnergyClass :
    H3PathAdmissibleProducesEnergyClass := by

  intro u T hH3

  exact
    h3Preterminal_energyClass_of_h3PathAdmissible
      hH3

end

end Euclidean
end Bridge
end PrimeTensor
