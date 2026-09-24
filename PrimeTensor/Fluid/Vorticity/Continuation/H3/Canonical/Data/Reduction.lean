import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Selected.Old.H3.Path.Admissible
import PrimeTensor.Fluid.Vorticity.H3.Energy.Closure

/-!
# Reduce canonical H³ data on the preterminal H³ path class

The H³-path continuation route currently carries the old global interface

    EnergyClassProducesCanonicalH3Data.

That interface bundles three logically separate facts on an energy-class tail:

1. `VelocityH3IntegrableAt` at every time;
2. local `C¹` regularity of the canonical scalar H³ energy;
3. the differentiated-PDE / whole-space integration-by-parts package
   `H3EnergyEstimateAnalyticOnTail`.

For `LoggedPreterminalH3PathAdmissible`, item 1 is no longer an analytic
frontier at all: H³ integrability is already part of the solution class at
every strict preterminal time.

This file isolates the exact remaining content.

`H3PathEnergyClassProducesCanonicalAnalysis` asks only for items 2 and 3 on
energy-class tails belonging to an H³-path-admissible solution.

`H3PathProducesCanonicalH3Data` is the path-specific form of the older
canonical-data interface.

The two propositions are proved equivalent.  Thus, on the corrected strong
solution class, the remaining canonical-data problem is exactly

* local `C¹` of `velocityH3EnergyAt`;
* differentiation / pairing / pressure-IBP / diffusion-IBP analysis.

No spatial H³ persistence or integrability hypothesis remains hidden in that
frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory

noncomputable section

/--
The genuine remaining canonical H³ analysis on an H³-path-admissible
preterminal solution.

H³ integrability is intentionally absent: it is already supplied by
`LoggedPreterminalH3PathAdmissible`.
-/
def H3PathEnergyClassProducesCanonicalAnalysis : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        PreterminalH3EnergyClass u a T →
          EnergyLocallyC1OnTail
              a T
              (velocityH3EnergyAt u)
            ∧
          H3EnergyEstimateAnalyticOnTail
              u a T

/--
Path-specific canonical-data production.

Unlike `EnergyClassProducesCanonicalH3Data`, this proposition is only required
for old solutions already known to be preterminal H³ paths.
-/
def H3PathProducesCanonicalH3Data : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        PreterminalH3EnergyClass u a T →
          CanonicalH3EnergyDataOnTail
            u a T

/--
On an H³ path, local-C¹ plus the analytic tail package reconstruct the complete
canonical H³ data package.

The integrability field is discharged directly from the path admissibility.
-/
theorem h3PathProducesCanonicalH3Data_of_analysis
    (hAnalysis :
      H3PathEnergyClassProducesCanonicalAnalysis) :
    H3PathProducesCanonicalH3Data := by

  intro u T hH3 a hClass

  rcases
    hAnalysis
      u T hH3 a hClass
  with
    ⟨hC1, hAnalytic⟩

  refine
    ⟨
      ?_,
      hC1,
      hAnalytic
    ⟩

  intro t ht

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T := by
    exact
      ⟨
        lt_of_lt_of_le
          hClass.terminal_start.1
          ht.1,
        ht.2
      ⟩

  exact
    hH3.velocity_h3_integrable
      t htAbs

/--
Conversely, path-specific canonical H³ data contains exactly the local-C¹ and
analytic-tail fields isolated above.
-/
theorem h3PathEnergyClassProducesCanonicalAnalysis_of_data
    (hData :
      H3PathProducesCanonicalH3Data) :
    H3PathEnergyClassProducesCanonicalAnalysis := by

  intro u T hH3 a hClass

  have hCanonical :
      CanonicalH3EnergyDataOnTail
        u a T :=
    hData
      u T hH3 a hClass

  exact
    ⟨
      hCanonical.2.1,
      hCanonical.2.2
    ⟩

/--
Exact characterization of the old canonical-data bundle on the corrected H³
strong-solution class.
-/
theorem h3PathProducesCanonicalH3Data_iff_analysis :
    H3PathProducesCanonicalH3Data
      ↔
    H3PathEnergyClassProducesCanonicalAnalysis := by

  constructor

  · exact
      h3PathEnergyClassProducesCanonicalAnalysis_of_data

  · exact
      h3PathProducesCanonicalH3Data_of_analysis

/--
The older global canonical-data interface remains a sufficient condition for
the new path-specific data interface.
-/
theorem h3PathProducesCanonicalH3Data_of_global
    (hCanonical :
      EnergyClassProducesCanonicalH3Data) :
    H3PathProducesCanonicalH3Data := by

  intro u T _hH3 a hClass

  exact
    hCanonical
      u a T hClass

/--
Compatibility corollary: the older global interface also supplies the reduced
path-specific analysis frontier.
-/
theorem h3PathEnergyClassProducesCanonicalAnalysis_of_global
    (hCanonical :
      EnergyClassProducesCanonicalH3Data) :
    H3PathEnergyClassProducesCanonicalAnalysis := by

  exact
    h3PathEnergyClassProducesCanonicalAnalysis_of_data
      (h3PathProducesCanonicalH3Data_of_global
        hCanonical)

end

end Euclidean
end Bridge
end PrimeTensor
