import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalStrongH3EndpointPath
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualVelocityStrongH3Endpoint

/-!
# Two physical vorticity components suffice for pathwise strong H³ continuation

The three-component physical endpoint criterion is redundant.

One physical vorticity component is formed from the other two velocity
coordinates.  Consequently, pathwise strong H³ endpoint control for physical
vorticity component `i` supplies pathwise strong H³ endpoint control for every
velocity coordinate `j ≠ i`.

Therefore any two distinct physical vorticity components cover all three
velocity coordinates.  The existing velocity-level strong-H³ endpoint theorem
then forces smooth continuation.

This yields a sharper neutral obstruction under hypothetical nonextension:
at most one physical vorticity component can satisfy the pathwise strong H³
endpoint property.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Recover one velocity-component endpoint from one structural pair -/

/--
A pair-specific pathwise strong H³ endpoint is exactly a pathwise strong H³
endpoint for the velocity coordinate selected by the pair.
-/
theorem velocityComponentStrongH3EndpointPath_of_pair
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (p : H3TerminalCurlGradientPair)
    (hPair :
      H3TerminalComplementGradientStrongH3EndpointPath
        hH3 p) :
    H3TerminalVelocityComponentStrongH3EndpointPath
      hH3
      (
        h3ClassicalizationFinOfAxis
          (h3TerminalComplementComponentAxisForPair p)
      ) := by

  obtain
    ⟨
      Ginf,
      hTerminalRep,
      hModulus
    ⟩ :=
    hPair

  refine
    ⟨
      Ginf,
      ?_,
      ?_
    ⟩

  · simpa only [
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
    ] using
      hTerminalRep

  · intro ε hε

    obtain
      ⟨
        η,
        hη,
        hNear
      ⟩ :=
      hModulus
        ε hε

    refine
      ⟨
        η,
        hη,
        ?_
      ⟩

    intro t ht hTime

    have h :=
      hNear
        t
        ht
        hTime

    rw [
      h3TerminalComplementSpectralStateAt_eq_velocityComponent
        hH3 p t ht
    ] at h

    exact
      h

/-! ## One physical curl component controls the two transverse velocities -/

/--
If physical vorticity component `i` has a pathwise strong H³ endpoint, then
every distinct velocity coordinate `j ≠ i` has a pathwise strong H³ endpoint.

This is the coordinate form of the elementary fact that the `i`-th curl
component uses precisely the other two velocity coordinates.
-/
theorem velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {i j : Fin 3}
    (hji :
      j ≠ i)
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i) :
    H3TerminalVelocityComponentStrongH3EndpointPath
      hH3 j := by

  fin_cases i <;> fin_cases j

  · exact
      (hji rfl).elim

  · change
      H3TerminalComplementGradientStrongH3EndpointPath
          hH3 .x_zy
        ∧
      H3TerminalComplementGradientStrongH3EndpointPath
          hH3 .x_yz
      at hPhysical

    have hVelocity :=
      velocityComponentStrongH3EndpointPath_of_pair
        hH3
        .x_yz
        hPhysical.2

    have hCoord :
        h3ClassicalizationFinOfAxis
            (h3TerminalComplementComponentAxisForPair .x_yz)
          =
        (1 : Fin 3) := by
      rfl

    rw [hCoord] at hVelocity

    exact
      hVelocity

  · change
      H3TerminalComplementGradientStrongH3EndpointPath
          hH3 .x_zy
        ∧
      H3TerminalComplementGradientStrongH3EndpointPath
          hH3 .x_yz
      at hPhysical

    have hVelocity :=
      velocityComponentStrongH3EndpointPath_of_pair
        hH3
        .x_zy
        hPhysical.1

    have hCoord :
        h3ClassicalizationFinOfAxis
            (h3TerminalComplementComponentAxisForPair .x_zy)
          =
        (2 : Fin 3) := by
      rfl

    rw [hCoord] at hVelocity

    exact
      hVelocity

  · change
      H3TerminalComplementGradientStrongH3EndpointPath
          hH3 .y_xz
        ∧
      H3TerminalComplementGradientStrongH3EndpointPath
          hH3 .y_zx
      at hPhysical

    have hVelocity :=
      velocityComponentStrongH3EndpointPath_of_pair
        hH3
        .y_xz
        hPhysical.1

    simpa [
      h3TerminalComplementComponentAxisForPair,
      h3ClassicalizationFinOfAxis,
      xAxis,
      yAxis,
      zAxis
    ] using
      hVelocity

  · exact
      (hji rfl).elim

  · change
      H3TerminalComplementGradientStrongH3EndpointPath
          hH3 .y_xz
        ∧
      H3TerminalComplementGradientStrongH3EndpointPath
          hH3 .y_zx
      at hPhysical

    have hVelocity :=
      velocityComponentStrongH3EndpointPath_of_pair
        hH3
        .y_zx
        hPhysical.2

    have hCoord :
        h3ClassicalizationFinOfAxis
            (h3TerminalComplementComponentAxisForPair .y_zx)
          =
        (2 : Fin 3) := by
      rfl

    rw [hCoord] at hVelocity

    exact
      hVelocity

  · change
      H3TerminalComplementGradientStrongH3EndpointPath
          hH3 .z_yx
        ∧
      H3TerminalComplementGradientStrongH3EndpointPath
          hH3 .z_xy
      at hPhysical

    have hVelocity :=
      velocityComponentStrongH3EndpointPath_of_pair
        hH3
        .z_xy
        hPhysical.2

    simpa [
      h3TerminalComplementComponentAxisForPair,
      h3ClassicalizationFinOfAxis,
      xAxis,
      yAxis,
      zAxis
    ] using
      hVelocity

  · change
      H3TerminalComplementGradientStrongH3EndpointPath
          hH3 .z_yx
        ∧
      H3TerminalComplementGradientStrongH3EndpointPath
          hH3 .z_xy
      at hPhysical

    have hVelocity :=
      velocityComponentStrongH3EndpointPath_of_pair
        hH3
        .z_yx
        hPhysical.1

    have hCoord :
        h3ClassicalizationFinOfAxis
            (h3TerminalComplementComponentAxisForPair .z_yx)
          =
        (1 : Fin 3) := by
      rfl

    rw [hCoord] at hVelocity

    exact
      hVelocity

  · exact
      (hji rfl).elim

/-! ## Any two distinct physical components cover the full velocity -/

/--
Pathwise strong H³ endpoint control for any two distinct physical vorticity
components supplies pathwise strong H³ endpoint control for all three velocity
coordinates.
-/
theorem velocityStrongH3EndpointPath_of_twoDistinctActualVorticityComponents
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {i j : Fin 3}
    (hij :
      i ≠ j)
    (hI :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    (hJ :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 j) :
    H3TerminalVelocityStrongH3EndpointPath
      hH3 := by

  intro k

  by_cases hki :
      k = i

  · subst k

    exact
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        hij
        hJ

  · exact
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        hki
        hI

/-! ## Two-component continuation criterion -/

/--
Any two distinct physical vorticity components with pathwise strong H³
endpoint control force smooth continuation.
-/
theorem smoothContinuationExtension_of_twoDistinctActualVorticityComponents_strongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    {i j : Fin 3}
    (hij :
      i ≠ j)
    (hI :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    (hJ :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 j) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension
        u v T := by

  exact
    smoothContinuationExtension_of_velocityStrongH3EndpointPath
      hH3
      hClass
      (
        velocityStrongH3EndpointPath_of_twoDistinctActualVorticityComponents
          hH3
          hij
          hI
          hJ
      )

/-! ## Neutral obstruction under nonextension -/

/--
Under hypothetical nonextension, two physical vorticity components satisfying
the pathwise strong H³ endpoint property must be the same component.

Equivalently, at most one of the three physical vorticity components can have
that endpoint property.
-/
theorem actualVorticityStrongH3EndpointPath_eq_of_noH3PathExtension
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
        u a T)
    {i j : Fin 3}
    (hI :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    (hJ :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 j) :
    i = j := by

  by_contra hij

  exact
    hNoExtension
      (
        smoothContinuationExtension_of_twoDistinctActualVorticityComponents_strongH3EndpointPath
          hH3
          hClass
          hij
          hI
          hJ
      )

/--
Equivalent pairwise neutral formulation: under hypothetical nonextension, no
two distinct physical vorticity components can both have pathwise strong H³
endpoints.
-/
theorem not_both_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
        u a T)
    {i j : Fin 3}
    (hij :
      i ≠ j) :
    ¬
      (
        H3TerminalActualVorticityStrongH3EndpointPath
            hH3 i
          ∧
        H3TerminalActualVorticityStrongH3EndpointPath
            hH3 j
      ) := by

  intro hBoth

  exact
    hij
      (
        actualVorticityStrongH3EndpointPath_eq_of_noH3PathExtension
          hH3
          hNoExtension
          hClass
          hBoth.1
          hBoth.2
      )

end

end Euclidean
end Bridge
end PrimeTensor
