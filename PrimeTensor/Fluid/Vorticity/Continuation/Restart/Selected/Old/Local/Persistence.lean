import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Selected.Old.Seed.Tail.Control
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Preterminal.Seed.Bridge

/-!
# Isolate the genuinely local H³ persistence frontier

The previous reductions showed two different facts:

* one H³ anchor already launches the smooth selected spectral restart;
* a canonical H³ tail already transfers that smoothness back to the old branch.

What is still missing between them is not a global smoothing theorem.  It is the
short-time persistence needed to keep the old preterminal branch in the strong
H³ class long enough to run the overlap/uniqueness argument.

The canonical quantitative form is:

    VelocityH3IntegrableAt u t
      ->
    ∃ S > t,
      CanonicalH3TailDataFrom
        u t S (2 * velocityH3EnergyAt u t).

The factor `2` is exactly the normalization already used by the restart Picard
ball and by `H3PreterminalSpectralOverlapWitnessAt`.

This file does three bookkeeping jobs only:

1. restrict a preterminal Navier--Stokes witness from `(0,T)` to `(0,S)`;
2. state the local H³ persistence frontier precisely;
3. prove that this local persistence already yields a genuine local
   `PreterminalH3EnergyClass` for the old branch through the sliding-anchor
   regularity theorem.

No H³ persistence theorem is asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set

noncomputable section

noncomputable local instance axisFintypeH3LocalSeedPersistence
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Restrict preterminal PDE witnesses to a shorter terminal interval -/

/--
Preterminal regularity on `(0,T)` restricts to every shorter interval `(0,S)`.
-/
theorem PreterminalVorticityRegularity3.mono_terminal
    {v : SpaceTimeVectorField ℝ ℝ ℝ Depth.three}
    {p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three}
    {S T : ℝ}
    (hReg : PreterminalVorticityRegularity3 v p T)
    (hST : S ≤ T) :
    PreterminalVorticityRegularity3 v p S := by

  refine
    {
      velocity_spatial_three := ?_
      velocity_temporal_one := ?_
      pressure_spatial_two := ?_
      velocity_space_time_hasDerivAt := ?_
    }

  · intro t ht j
    exact
      hReg.velocity_spatial_three
        t
        ⟨
          ht.1,
          lt_of_lt_of_le ht.2 hST
        ⟩
        j

  · intro x j
    exact
      (hReg.velocity_temporal_one x j).mono
        (by
          intro t ht
          exact
            ⟨
              ht.1,
              lt_of_lt_of_le ht.2 hST
            ⟩)

  · intro t ht
    exact
      hReg.pressure_spatial_two
        t
        ⟨
          ht.1,
          lt_of_lt_of_le ht.2 hST
        ⟩

  · intro t ht x i j
    exact
      hReg.velocity_space_time_hasDerivAt
        t
        ⟨
          ht.1,
          lt_of_lt_of_le ht.2 hST
        ⟩
        x i j

/--
A preterminal Navier--Stokes solution on `(0,T)` is also one on every positive
shorter terminal interval `(0,S)`.
-/
theorem PreterminalNavierStokes3.mono_terminal
    {v : SpaceTimeVectorField ℝ ℝ ℝ Depth.three}
    {p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three}
    {S T : ℝ}
    (hPDE : PreterminalNavierStokes3 v p T)
    (hS : 0 < S)
    (hST : S ≤ T) :
    PreterminalNavierStokes3 v p S := by

  refine
    {
      positive_terminal := hS
      regularity :=
        hPDE.regularity.mono_terminal hST
      incompressible := ?_
      momentum := ?_
    }

  · intro t ht x
    exact
      hPDE.incompressible
        t
        ⟨
          ht.1,
          lt_of_lt_of_le ht.2 hST
        ⟩
        x

  · intro t ht x j
    exact
      hPDE.momentum
        t
        ⟨
          ht.1,
          lt_of_lt_of_le ht.2 hST
        ⟩
        x j

/--
Logged preterminal admissibility therefore restricts to every positive shorter
terminal time.
-/
theorem loggedPreterminalNavierStokesAdmissible_mono_terminal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {S T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hS : 0 < S)
    (hST : S ≤ T) :
    LoggedPreterminalNavierStokesAdmissible u S := by

  rcases hNS with
    ⟨p, hPDE⟩

  exact
    ⟨
      p,
      hPDE.mono_terminal hS hST
    ⟩

/-! ## The actual local H³ persistence frontier -/

/--
Short-time canonical H³ persistence from one H³-integrable interior slice.

The energy ceiling is the natural `2E` Picard ceiling already used throughout
the spectral restart construction.

This is the first genuinely analytic seed-side statement still missing from the
current project.
-/
def H3IntegrableSliceProducesLocalCanonicalH3Tail : Prop :=
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
        CanonicalH3TailDataFrom
          u
          t
          S
          (2 * velocityH3EnergyAt u t)

/--
Local high-order regularization generated from an H³ seed.

This intentionally asks only for a shorter terminal interval `S<T`; it makes
no global assertion near the original candidate terminal time.
-/
def H3SeedProducesLocalEnergyClass : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalNavierStokesAdmissible u T →
      PreterminalH3Seed u T →
      ∃
        (S b : ℝ),
          0 < S
            ∧
          S < T
            ∧
          PreterminalH3EnergyClass u b S

/--
The local H³ persistence frontier already implies local old-branch C5/C4
regularization.

The proof uses no new PDE estimate:

* convert the seed to one H³-integrable slice;
* persist that slice only to a shorter `S`;
* restrict the old PDE witness to `(0,S)`;
* apply the sliding-anchor canonical-tail -> energy-class theorem.
-/
theorem h3SeedProducesLocalEnergyClass_of_localCanonicalH3Persistence
    (hPersist : H3IntegrableSliceProducesLocalCanonicalH3Tail) :
    H3SeedProducesLocalEnergyClass := by

  intro u T hNS hSeed

  rcases
    preterminalH3Seed_iff_exists_velocityH3IntegrableAt.mp hSeed
  with
    ⟨
      t,
      ht,
      hInt
    ⟩

  rcases
    hPersist u T t hNS ht hInt
  with
    ⟨
      S,
      htS,
      hST,
      hTail
    ⟩

  have hS :
      0 < S :=
    lt_trans ht.1 htS

  have hNSShort :
      LoggedPreterminalNavierStokesAdmissible u S :=
    loggedPreterminalNavierStokesAdmissible_mono_terminal
      hNS
      hS
      (le_of_lt hST)

  have htShort :
      t ∈ Set.Ioo (0 : ℝ) S :=
    ⟨
      ht.1,
      htS
    ⟩

  have hEnergyOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hTwoEnergy :
      1 ≤ 2 * velocityH3EnergyAt u t := by
    linarith

  rcases
    h3Preterminal_energyClass_of_canonicalTail
      hNSShort
      htShort
      hTwoEnergy
      hTail
  with
    ⟨
      b,
      hClass
    ⟩

  exact
    ⟨
      S,
      b,
      hS,
      hST,
      hClass
    ⟩


end

end Euclidean
end Bridge
end PrimeTensor
