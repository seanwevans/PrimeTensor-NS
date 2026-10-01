import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Strong.H3.Continuation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Native.Residual.Strong.H3.Endpoint.Path

/-!
# Sequence-free physical strong H³ endpoint criterion

The physical continuation criterion is currently stated through every strict
selected terminal sequence.  The pairwise endpoint development already has the
stronger pathwise formulation:

* one terminal spectral H³ state;
* representing the actual terminal velocity component; and
* approached in H³ norm by the full strict-time path as `t ↑ T`.

For one fixed physical vorticity component, require that pathwise property for
the two constituent velocity components whose first derivatives form the curl
component.

This immediately specializes to the sequence-uniform physical criterion.
Requiring it for all three physical vorticity components covers all six
structural pairs and therefore forces smooth continuation.

The neutral contrapositive isolates the remaining pathwise obstruction:
hypothetical nonextension forces at least one physical vorticity component to
fail this sequence-free strong H³ endpoint condition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Pathwise physical strong H³ endpoint -/

/--
One physical vorticity component has a genuine pathwise strong H³ endpoint
when both constituent complementary velocity components have pathwise strong
H³ endpoints.
-/
def H3TerminalActualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (i : Fin 3) : Prop :=
  H3TerminalComplementGradientStrongH3EndpointPath
      hH3
      (h3TerminalActualVorticityPositiveComplementPair i)
    ∧
  H3TerminalComplementGradientStrongH3EndpointPath
      hH3
      (h3TerminalActualVorticityNegativeComplementPair i)

/-! ## Pathwise control specializes to every selected sequence -/

/--
The pathwise physical endpoint property implies the previously defined
sequence-uniform physical endpoint property.
-/
theorem actualVorticityStrongH3EndpointOnAllSelectedTerminalSequences_of_path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {i : Fin 3}
    (hPath :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i) :
    H3TerminalActualVorticityStrongH3EndpointOnAllSelectedTerminalSequences
      hH3 i := by

  intro τ hTauStrict _hTau

  exact
    ⟨
      selectedStrongH3Endpoint_of_strongH3EndpointPath
        hH3
        hTauStrict
        hPath.1,
      selectedStrongH3Endpoint_of_strongH3EndpointPath
        hH3
        hTauStrict
        hPath.2
    ⟩

/-! ## Three physical components cover every pathwise structural pair -/

/--
Pathwise strong H³ endpoint control for all three physical vorticity
components implies the pathwise endpoint criterion for all six structural
curl-gradient pairs.
-/
theorem allPairs_strongH3EndpointPath_of_allActualVorticityComponents_strongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hAllPhysical :
      ∀ i : Fin 3,
        H3TerminalActualVorticityStrongH3EndpointPath
          hH3 i) :
    ∀ p : H3TerminalCurlGradientPair,
      H3TerminalComplementGradientStrongH3EndpointPath
        hH3 p := by

  intro p

  cases p with

  | x_yz =>
      have hPhysical :=
        hAllPhysical
          (0 : Fin 3)

      simpa [
        H3TerminalActualVorticityStrongH3EndpointPath,
        h3TerminalActualVorticityPositiveComplementPair,
        h3TerminalActualVorticityNegativeComplementPair
      ] using
        hPhysical.2

  | x_zy =>
      have hPhysical :=
        hAllPhysical
          (0 : Fin 3)

      simpa [
        H3TerminalActualVorticityStrongH3EndpointPath,
        h3TerminalActualVorticityPositiveComplementPair,
        h3TerminalActualVorticityNegativeComplementPair
      ] using
        hPhysical.1

  | y_zx =>
      have hPhysical :=
        hAllPhysical
          (1 : Fin 3)

      simpa [
        H3TerminalActualVorticityStrongH3EndpointPath,
        h3TerminalActualVorticityPositiveComplementPair,
        h3TerminalActualVorticityNegativeComplementPair
      ] using
        hPhysical.2

  | y_xz =>
      have hPhysical :=
        hAllPhysical
          (1 : Fin 3)

      simpa [
        H3TerminalActualVorticityStrongH3EndpointPath,
        h3TerminalActualVorticityPositiveComplementPair,
        h3TerminalActualVorticityNegativeComplementPair
      ] using
        hPhysical.1

  | z_xy =>
      have hPhysical :=
        hAllPhysical
          (2 : Fin 3)

      simpa [
        H3TerminalActualVorticityStrongH3EndpointPath,
        h3TerminalActualVorticityPositiveComplementPair,
        h3TerminalActualVorticityNegativeComplementPair
      ] using
        hPhysical.2

  | z_yx =>
      have hPhysical :=
        hAllPhysical
          (2 : Fin 3)

      simpa [
        H3TerminalActualVorticityStrongH3EndpointPath,
        h3TerminalActualVorticityPositiveComplementPair,
        h3TerminalActualVorticityNegativeComplementPair
      ] using
        hPhysical.1

/-! ## Sequence-free physical continuation criterion -/

/--
If all three actual-vorticity components have pathwise strong H³ endpoints for
their two constituent velocity components, then the H³ path admits a smooth
continuation extension.
-/
theorem smoothContinuationExtension_of_allActualVorticityComponents_strongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hAllPhysical :
      ∀ i : Fin 3,
        H3TerminalActualVorticityStrongH3EndpointPath
          hH3 i) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension
        u v T := by

  exact
    smoothContinuationExtension_of_allPairs_strongH3EndpointPath
      hH3
      hClass
      (
        allPairs_strongH3EndpointPath_of_allActualVorticityComponents_strongH3EndpointPath
          hH3
          hAllPhysical
      )

/-! ## Neutral pathwise failure formulation -/

/--
Hypothetical nonextension forces failure of the pathwise strong H³ endpoint
property for at least one physical vorticity component.
-/
theorem exists_actualVorticityComponent_strongH3EndpointPathFailure_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hNoExtension :
      ¬
        ∃
          v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
          SmoothContinuationExtension
            u v T)
    (hClass :
      PreterminalH3EnergyClass
        u a T) :
    ∃ i : Fin 3,
      ¬
        H3TerminalActualVorticityStrongH3EndpointPath
          hH3 i := by

  by_contra hNoFailure

  have hAllPhysical :
      ∀ i : Fin 3,
        H3TerminalActualVorticityStrongH3EndpointPath
          hH3 i := by

    intro i

    by_contra hi

    exact
      hNoFailure
        ⟨
          i,
          hi
        ⟩

  exact
    hNoExtension
      (
        smoothContinuationExtension_of_allActualVorticityComponents_strongH3EndpointPath
          hH3
          hClass
          hAllPhysical
      )

/--
Neutral sequence-free alternative: either the H³ path continues smoothly, or
at least one physical vorticity component fails pathwise strong H³ endpoint
control.
-/
theorem smoothContinuationExtension_or_actualVorticityComponent_strongH3EndpointPathFailure
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension
          u v T
    )
      ∨
    (
      ∃ i : Fin 3,
        ¬
          H3TerminalActualVorticityStrongH3EndpointPath
            hH3 i
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension
          u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        (
          exists_actualVorticityComponent_strongH3EndpointPathFailure_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
