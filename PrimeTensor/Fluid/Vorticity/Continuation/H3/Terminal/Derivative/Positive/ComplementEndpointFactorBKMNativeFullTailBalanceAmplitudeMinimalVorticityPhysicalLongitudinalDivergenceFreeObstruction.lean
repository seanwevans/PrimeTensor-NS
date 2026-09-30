import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalStrongH3
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Preterminal.Incompressibility

/-!
# Place the longitudinal endpoint obstruction inside the divergence-free spectral path

The one-component physical reduction has isolated the following situation.

If physical vorticity component `i` has a pathwise strong H³ endpoint, then
the two transverse velocity coordinates have pathwise strong H³ endpoints.
Under hypothetical nonextension, the only remaining failure is therefore the
same-index longitudinal velocity coordinate.

This file records one additional fact that is already available from the
preterminal Navier--Stokes hypotheses: every strict-time full weighted H³
spectral state is Fourier divergence-free.

Thus the surviving longitudinal failure is not an arbitrary missing component.
It occurs inside a divergence-free three-component spectral path whose two
transverse coordinates already have strong H³ endpoints.

The final theorem packages the neutral trichotomy:

* smooth continuation; or
* every physical vorticity component fails its pathwise strong H³ endpoint; or
* one physical component has that endpoint, while its longitudinal velocity
  endpoint fails along an already divergence-free strict-time spectral path.

The next analytic target is therefore the possible concentration of the
longitudinal spectral defect near the coordinate plane `ξᵢ = 0`, where solving
the divergence identity for the `i`-th component becomes singular.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Canonical full strict-time H³ spectral state -/

/--
The full three-component weighted H³ spectral state at one strict preterminal
time, using exactly the same canonical integrability, measurability, and
Fourier-compatibility data as the component endpoint path.
-/
noncomputable def h3TerminalVelocitySpectralStateAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (t : ℝ)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T) :
    H3SpectralFinVectorState := by

  let hNS :
      LoggedPreterminalNavierStokesAdmissible
        u T :=
    hH3.navier_stokes

  let hInt :
      VelocityH3IntegrableAt
        u t :=
    hH3.velocity_h3_integrable
      t ht

  let hMeas :
      VelocityH3MeasurableAt
        u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS
      ht

  let hFourier :
      VelocityH3FourierCompatibleAt
        u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS
      ht
      hInt

  exact
    velocityH3SpectralStateAt
      u
      t
      hInt
      hMeas
      hFourier

/--
The `j`-th coordinate of the full strict-time spectral state is exactly the
component state used by the pathwise endpoint definitions.
-/
theorem h3TerminalVelocitySpectralStateAt_apply
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (t : ℝ)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T)
    (j : Fin 3) :
    h3TerminalVelocitySpectralStateAt
        hH3 t ht j
      =
    h3TerminalVelocityComponentSpectralStateAt
      hH3 j t ht := by

  rfl

/-! ## Strict-time spectral incompressibility -/

/--
Every canonical strict-time full H³ spectral state is Fourier
divergence-free.
-/
theorem h3TerminalVelocitySpectralStateAt_divergenceFree
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (t : ℝ)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T) :
    H3SpectralFinDivergenceFree
      (
        h3TerminalVelocitySpectralStateAt
          hH3 t ht
      ) := by

  unfold h3TerminalVelocitySpectralStateAt

  exact
    velocityH3SpectralStateAt_divergenceFree_of_loggedPreterminalNavierStokes
      hH3.navier_stokes
      ht
      (hH3.velocity_h3_integrable t ht)

/-! ## The surviving one-component obstruction -/

/--
For one coordinate, package exactly the spectral situation left after the
physical reduction:

* the physical vorticity endpoint exists;
* every strict-time full spectral state is divergence-free;
* the same-index longitudinal velocity endpoint fails.
-/
def H3TerminalActualVorticityLongitudinalDivergenceFreeObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (i : Fin 3) : Prop :=
  H3TerminalActualVorticityStrongH3EndpointPath
      hH3 i
    ∧
  (
    ∀
      (t : ℝ)
      (ht : t ∈ Set.Ioo (0 : ℝ) T),
      H3SpectralFinDivergenceFree
        (
          h3TerminalVelocitySpectralStateAt
            hH3 t ht
        )
  )
    ∧
  ¬
    H3TerminalVelocityComponentStrongH3EndpointPath
      hH3 i

/--
Under hypothetical nonextension, every surviving physical vorticity endpoint
produces the longitudinal divergence-free obstruction at the same coordinate.
-/
theorem actualVorticityLongitudinalDivergenceFreeObstruction_of_strongH3EndpointPath_of_noH3PathExtension
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
    H3TerminalActualVorticityLongitudinalDivergenceFreeObstruction
      hH3 i := by

  refine
    ⟨
      hPhysical,
      ?_,
      longitudinalVelocityStrongH3EndpointPath_failure_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hPhysical
    ⟩

  intro t ht

  exact
    h3TerminalVelocitySpectralStateAt_divergenceFree
      hH3
      t
      ht

/-! ## Neutral global classification -/

/--
Under hypothetical nonextension, either all three physical vorticity
components fail their pathwise strong H³ endpoint, or one coordinate carries
the longitudinal divergence-free obstruction.
-/
theorem allActualVorticityStrongH3EndpointsFail_or_exists_longitudinalDivergenceFreeObstruction_of_noH3PathExtension
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
    (
      ∀ i : Fin 3,
        ¬
          H3TerminalActualVorticityStrongH3EndpointPath
            hH3 i
    )
      ∨
    (
      ∃ i : Fin 3,
        H3TerminalActualVorticityLongitudinalDivergenceFreeObstruction
          hH3 i
    ) := by

  by_cases hAllFail :
      ∀ i : Fin 3,
        ¬
          H3TerminalActualVorticityStrongH3EndpointPath
            hH3 i

  · exact
      Or.inl
        hAllFail

  · push_neg at hAllFail

    obtain
      ⟨
        i,
        hPhysical
      ⟩ :=
      hAllFail

    exact
      Or.inr
        ⟨
          i,
          actualVorticityLongitudinalDivergenceFreeObstruction_of_strongH3EndpointPath_of_noH3PathExtension
            hH3
            hNoExtension
            hClass
            hPhysical
        ⟩

/--
Neutral terminal trichotomy:

* smooth continuation; or
* all physical-vorticity pathwise strong H³ endpoints fail; or
* one coordinate carries a surviving physical endpoint together with a
  longitudinal endpoint failure inside the divergence-free spectral path.
-/
theorem smoothContinuationExtension_or_allActualVorticityStrongH3EndpointsFail_or_longitudinalDivergenceFreeObstruction
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
      (
        ∀ i : Fin 3,
          ¬
            H3TerminalActualVorticityStrongH3EndpointPath
              hH3 i
      )
        ∨
      (
        ∃ i : Fin 3,
          H3TerminalActualVorticityLongitudinalDivergenceFreeObstruction
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
          allActualVorticityStrongH3EndpointsFail_or_exists_longitudinalDivergenceFreeObstruction_of_noH3PathExtension
            hH3
            hExtension
            hClass
        )

end

end Euclidean
end Bridge
end PrimeTensor
