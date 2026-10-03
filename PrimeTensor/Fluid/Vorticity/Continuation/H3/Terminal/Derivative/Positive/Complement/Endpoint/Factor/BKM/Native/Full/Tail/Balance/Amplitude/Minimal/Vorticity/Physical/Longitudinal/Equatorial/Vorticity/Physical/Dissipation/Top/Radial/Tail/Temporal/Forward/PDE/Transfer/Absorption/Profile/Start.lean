import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Local

/-!
# Arbitrary strict starts for the physical H³ energy class

`LoggedPreterminalH3PathAdmissible` already closes the high-order energy class
by a sliding local restart argument.  The original packaging chose `T / 2` as
one convenient terminal-tail start, but nothing in that argument depends on
that particular value.

This file records the stronger form actually proved by the same local
construction:

    every b ∈ (0,T) supports PreterminalH3EnergyClass u b T.

Consequently, for any existing energy-class start `a`, there is another
energy-class start strictly earlier than `a`.

This is the structural input needed to remove the artificial left-endpoint
ambiguity from the cubic forcing mass obstruction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalTopTailArbitraryEnergyStart
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2200000

/--
A standard preterminal H³ path produces the old high-order energy class from
every strict physical start `b ∈ (0,T)`.
-/
theorem h3Preterminal_energyClass_from_of_h3PathAdmissible
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hb : b ∈ Set.Ioo (0 : ℝ) T) :
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

  refine
    {
      terminal_start := hb
      velocity_spatial_five := ?_
      pressure_witness := ?_
    }

  · intro s hs j i k

    change
      SpatialC3
        (spatial3.d i
          (spatial3.d k
            (loggedVelocityComponent u s j)))

    have hsAbs :
        s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨
        lt_of_lt_of_le hb.1 hs.1,
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
        lt_of_lt_of_le hb.1 hs.1,
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
Every existing strict energy-class start has another admissible energy-class
start strictly before it.
-/
theorem exists_earlier_preterminalH3EnergyClass_of_h3PathAdmissible
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ b : ℝ,
      b ∈ Set.Ioo (0 : ℝ) a
        ∧
      PreterminalH3EnergyClass u b T := by

  let b : ℝ :=
    a / 2

  have ha0 :
      0 < a :=
    hClass.terminal_start.1

  have haT :
      a < T :=
    hClass.terminal_start.2

  have hb0 :
      0 < b := by
    dsimp only [b]
    linarith

  have hba :
      b < a := by
    dsimp only [b]
    linarith

  have hbT :
      b < T :=
    lt_trans hba haT

  have hb :
      b ∈ Set.Ioo (0 : ℝ) T :=
    ⟨hb0, hbT⟩

  refine
    ⟨
      b,
      ⟨hb0, hba⟩,
      ?_
    ⟩

  exact
    h3Preterminal_energyClass_from_of_h3PathAdmissible
      hH3 hb

end

end Euclidean
end Bridge
end PrimeTensor
