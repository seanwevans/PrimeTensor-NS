import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedPressureMomentumLocalFill
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedMixedClosedPDERemainderReduction

/-!
# Closure of the selected mixed H³ PDE remainder

Pressure spatial `C²` and the unit-viscosity momentum equation are now proved
for the canonical old/selected local fill.  The only remaining bookkeeping in
the mixed-closed PDE reduction is to choose an extension endpoint strictly
between the old terminal time and the end of the selected restart window.

If

    T - t < R,

then

    T < t + R.

We choose the midpoint

    S = (T + (t + R)) / 2.

Thus `T < S` and `S - t < R`.  The pressure local-fill regularity theorem and
the pressure-momentum local-fill theorem then provide exactly the two predicates
required by `SelectedMixedClosedPDERemainderReduction`.

No new analytic estimate or regularity hypothesis is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedMixedClosedPDEClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical piecewise pressure and midpoint endpoint furnish the complete
local PDE remainder required after selected mixed-derivative closure. -/
theorem h3PreterminalTailUnitViscositySelectedMixedClosedPDERemainder
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1)) :
    ∀
      (E : ℝ)
      (hE : 1 ≤ E)
      (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
      (T t : ℝ)
      (hNS : LoggedPreterminalNavierStokesAdmissible u T)
      (ht : t ∈ Set.Ioo (0 : ℝ) T)
      (hTail : CanonicalH3TailDataFrom u t T E),
        T - t < h3FinHeatLerayRestartRadius (1 : ℝ) E →
        ∃
          (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
          (S : ℝ),
            T < S
              ∧
            S - t < h3FinHeatLerayRestartRadius (1 : ℝ) E
              ∧
            H3PreterminalTailUnitViscosityPressureSpatialRegularityAt
              p S
              ∧
            H3PreterminalTailUnitViscosityMomentumAt
              hNS ht hE hTail p S := by
  intro E hE u T t hNS ht hTail
  intro hCross

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  let S : ℝ :=
    (T + (t + R)) / 2

  have hTUpper :
      T < t + R := by
    have h :=
      (sub_lt_iff_lt_add).1 hCross
    simpa only [R, add_comm] using h

  have hTS :
      T < S := by
    dsimp only [S]
    linarith

  have hSR :
      S - t < R := by
    dsimp only [S]
    linarith

  have hSR' :
      S - t <
        h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    simpa only [R] using hSR

  have hEvolutionAt :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ) E
        (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail :=
    hEvolution E hE u T t hNS ht hTail

  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3PreterminalTailCanonicalSelectedPressureLocalFill
      hNS ht hE hTail

  have hPressure :
      H3PreterminalTailUnitViscosityPressureSpatialRegularityAt
        p S := by
    dsimp only [p]
    exact
      h3PreterminalTailCanonicalSelectedPressureLocalFill_pressureSpatialRegularity
        hNS ht hE hTail hTS hSR'

  have hMomentum :
      H3PreterminalTailUnitViscosityMomentumAt
        hNS ht hE hTail p S := by
    dsimp only [p]
    exact
      h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_pressureMomentum
        hNS ht hE hTail hEvolutionAt hTS hSR'

  exact
    ⟨
      p,
      S,
      hTS,
      hSR',
      hPressure,
      hMomentum
    ⟩

/-- Unit-viscosity physical-tail evolution now implies the H³ continuation
target: the selected restart supplies its own pressure, mixed regularity, and
momentum remainder. -/
theorem h3ControlProducesExtension_of_unitViscositySelectedMixedClosedPDE
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1)) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscositySelectedMixedClosedPDERemainder
      hEvolution
      (h3PreterminalTailUnitViscositySelectedMixedClosedPDERemainder
        hEvolution)

end

end Euclidean
end Bridge
end PrimeTensor
