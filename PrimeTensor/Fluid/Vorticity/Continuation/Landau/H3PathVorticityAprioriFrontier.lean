import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathBKMClosure

/-!
# Isolate the remaining H³-path global a-priori frontier

The BKM continuation criterion on `LoggedPreterminalH3PathAdmissible` is now
closed outright:

    VorticityL1LinfControl u T
      -> SmoothContinuationExtension through T.

Accordingly, the remaining global-regularity issue at this interface is no
longer any energy differentiation, pressure, restart, mixed-commutation, or
BKM endpoint lemma.  It is precisely the a-priori assertion that every
preterminal H³ path has finite `L¹_t L∞_x` vorticity control.

This file names that frontier and records its two immediate consequences:

* if the frontier is proved, every preterminal H³ path extends;
* contrapositively, any non-extendible H³ path must fail
  `VorticityL1LinfControl`.

No a-priori vorticity estimate is asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable section

/-- The remaining a-priori vorticity statement at the H³-path interface. -/
def H3PathPreterminalNavierStokesForcesVorticityL1Linf : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      VorticityL1LinfControl u T

/-- Global continuation conclusion restricted to the standard preterminal H³
strong-path interface. -/
def EveryH3PathPreterminalNavierStokesSolutionExtends : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

/-- Once the remaining H³-path a-priori vorticity statement is supplied, the
closed BKM criterion extends every preterminal H³ path. -/
theorem everyH3PathPreterminalNavierStokesSolutionExtends_of_vorticityApriori
    (hApriori :
      H3PathPreterminalNavierStokesForcesVorticityL1Linf) :
    EveryH3PathPreterminalNavierStokesSolutionExtends := by

  intro u T hH3

  exact
    h3PathVorticityL1LinfProducesExtension_closed
      u T hH3
      (hApriori u T hH3)

/-- Contrapositive of the now-closed H³-path BKM criterion: if a preterminal
H³ path cannot be smoothly continued through `T`, then its
`L¹_t L∞_x` vorticity control must fail. -/
theorem not_vorticityL1LinfControl_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T) :
    ¬ VorticityL1LinfControl u T := by

  intro hControl

  exact
    hNoExtension
      (h3PathVorticityL1LinfProducesExtension_closed
        u T hH3 hControl)

/-- The closed continuation theorem reduces failure of global H³-path
continuation exactly to failure of the remaining a-priori vorticity frontier. -/
theorem not_everyH3PathExtension_implies_not_vorticityApriori
    (hNoGlobal :
      ¬ EveryH3PathPreterminalNavierStokesSolutionExtends) :
    ¬ H3PathPreterminalNavierStokesForcesVorticityL1Linf := by

  intro hApriori

  exact
    hNoGlobal
      (everyH3PathPreterminalNavierStokesSolutionExtends_of_vorticityApriori
        hApriori)

end

end Euclidean
end Bridge
end PrimeTensor
