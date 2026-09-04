import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedPressureMomentumLocalFill
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedCanonicalMixedClosedPDERemainderReduction

/-!
# Closure of the canonical selected mixed H³ PDE remainder

The canonical mixed-derivative chain now removes the selected mixed spacetime
field from the continuation remainder.  Pressure spatial `C²` and the
unit-viscosity momentum equation are already available for the canonical
old/selected local fill.

The remaining bookkeeping is the same midpoint construction used by the
historical closure.  From

    T - t < R

we obtain `T < t + R` and choose

    S = (T + (t + R)) / 2.

Then `T < S` and `S - t < R`.  The pressure local-fill regularity theorem and
the pressure-momentum local-fill theorem furnish the two predicates required by
the canonical mixed-closed remainder reduction.

No new analytic estimate, regularity hypothesis, or PDE identity is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalMixedClosedPDEClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical piecewise pressure and midpoint endpoint furnish the complete
local PDE remainder required after canonical selected mixed-derivative closure. -/
theorem h3PreterminalTailUnitViscositySelectedCanonicalMixedClosedPDERemainder
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
target through the canonical mixed-derivative closure chain. -/
theorem h3ControlProducesExtension_of_unitViscositySelectedCanonicalMixedClosedPDE
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1)) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscositySelectedCanonicalMixedClosedPDERemainder
      hEvolution
      (h3PreterminalTailUnitViscositySelectedCanonicalMixedClosedPDERemainder
        hEvolution)

end

end Euclidean
end Bridge
end PrimeTensor
