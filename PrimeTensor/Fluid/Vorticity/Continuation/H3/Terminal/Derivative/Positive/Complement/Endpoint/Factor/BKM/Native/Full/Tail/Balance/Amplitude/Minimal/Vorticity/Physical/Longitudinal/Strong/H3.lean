import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Two.Component.Strong.H3

/-!
# One physical vorticity component plus its longitudinal velocity endpoint

The two-component physical criterion can be sharpened structurally.

For one fixed coordinate `i`, pathwise strong H³ endpoint control of the
`i`-th physical vorticity component already gives pathwise strong H³ endpoint
control for the two transverse velocity coordinates `j ≠ i`.

Thus only one velocity coordinate remains uncontrolled: the same-index
longitudinal coordinate `i`.

Consequently,

    physical vorticity endpoint at i
    +
    velocity endpoint at i

already gives the full three-component velocity endpoint and hence smooth
continuation.

The neutral contrapositive isolates the exact remaining mixed obstruction:
under hypothetical nonextension, whenever one physical vorticity component has
a pathwise strong H³ endpoint, the same-index velocity component must fail its
pathwise strong H³ endpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Complete the velocity endpoint from one physical component -/

/--
For a fixed coordinate `i`, the physical vorticity endpoint supplies the two
transverse velocity endpoints.  Adding the same-index velocity endpoint gives
the full velocity strong H³ endpoint path.
-/
theorem velocityStrongH3EndpointPath_of_actualVorticity_and_longitudinalVelocity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    (hLongitudinal :
      H3TerminalVelocityComponentStrongH3EndpointPath
        hH3 i) :
    H3TerminalVelocityStrongH3EndpointPath
      hH3 := by

  intro j

  by_cases hji :
      j = i

  · subst j

    exact
      hLongitudinal

  · exact
      velocityComponentStrongH3EndpointPath_of_actualVorticityStrongH3EndpointPath
        hH3
        hji
        hPhysical

/-! ## One-component mixed continuation criterion -/

/--
A pathwise strong H³ endpoint for one physical vorticity component together
with the same-index velocity endpoint forces smooth continuation.
-/
theorem smoothContinuationExtension_of_actualVorticity_and_longitudinalVelocity_strongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i)
    (hLongitudinal :
      H3TerminalVelocityComponentStrongH3EndpointPath
        hH3 i) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension
        u v T := by

  exact
    smoothContinuationExtension_of_velocityStrongH3EndpointPath
      hH3
      hClass
      (
        velocityStrongH3EndpointPath_of_actualVorticity_and_longitudinalVelocity
          hH3
          hPhysical
          hLongitudinal
      )

/-! ## Neutral mixed obstruction under nonextension -/

/--
Under hypothetical nonextension, if physical vorticity component `i` has a
pathwise strong H³ endpoint, then the same-index velocity component cannot
also have a pathwise strong H³ endpoint.
-/
theorem longitudinalVelocityStrongH3EndpointPath_failure_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i) :
    ¬
      H3TerminalVelocityComponentStrongH3EndpointPath
        hH3 i := by

  intro hLongitudinal

  exact
    hNoExtension
      (
        smoothContinuationExtension_of_actualVorticity_and_longitudinalVelocity_strongH3EndpointPath
          hH3
          hClass
          hPhysical
          hLongitudinal
      )

/--
Under hypothetical nonextension, each coordinate has a mixed endpoint failure:
either its physical vorticity endpoint fails, or its same-index velocity
endpoint fails.
-/
theorem actualVorticity_or_longitudinalVelocity_strongH3EndpointPathFailure_of_noH3PathExtension
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
    ∀ i : Fin 3,
      (
        ¬
          H3TerminalActualVorticityStrongH3EndpointPath
            hH3 i
      )
        ∨
      (
        ¬
          H3TerminalVelocityComponentStrongH3EndpointPath
            hH3 i
      ) := by

  intro i

  by_cases hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i

  · exact
      Or.inr
        (
          longitudinalVelocityStrongH3EndpointPath_failure_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
            hH3
            hNoExtension
            hClass
            hPhysical
        )

  · exact
      Or.inl
        hPhysical

/--
Neutral sequence-free alternative: either the H³ path continues smoothly, or
every coordinate exhibits the mixed obstruction that at least one of its
physical-vorticity endpoint and same-index velocity endpoint fails.
-/
theorem smoothContinuationExtension_or_allCoordinates_mixedStrongH3EndpointPathFailure
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
      ∀ i : Fin 3,
        (
          ¬
            H3TerminalActualVorticityStrongH3EndpointPath
              hH3 i
        )
          ∨
        (
          ¬
            H3TerminalVelocityComponentStrongH3EndpointPath
              hH3 i
        )
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
          actualVorticity_or_longitudinalVelocity_strongH3EndpointPathFailure_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
