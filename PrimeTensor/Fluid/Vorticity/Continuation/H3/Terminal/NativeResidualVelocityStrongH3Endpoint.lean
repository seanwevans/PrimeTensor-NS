import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualStrongH3EndpointPath

/-!
# Reduce six pairwise strong H³ endpoints to three velocity components

The pairwise endpoint criterion still carries six members of
`H3TerminalCurlGradientPair`, but its spectral state depends only on the
velocity component selected by the pair.

There are only three such components.

This file introduces the genuine strict-time scalar spectral H³ state of one
velocity coordinate `j : Fin 3` and the corresponding direct terminal endpoint
property.  For a terminal pair `p`, its complementary spectral state is exactly
the component state with

    j = h3ClassicalizationFinOfAxis
          (h3TerminalComplementComponentAxisForPair p).

Therefore strong H³ endpoints for all three velocity coordinates imply the
pairwise path endpoint for all six terminal pairs.  The previously proved
strong-H³ contradiction theorem then gives smooth continuation.

No new analytic estimate is introduced here.  This is a structural reduction
from six pair-indexed endpoint conditions to the three physical velocity
components.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalVelocityComponentEndpoint
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Actual strict-time scalar state of one velocity component -/

/--
The weighted scalar spectral H³ state of velocity coordinate `j` at one
strict preterminal time.
-/
noncomputable def h3TerminalVelocityComponentSpectralStateAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (j : Fin 3)
    (t : ℝ)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T) :
    H3SpectralScalarState := by

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
    (
      velocityH3SpectralStateAt
        u
        t
        hInt
        hMeas
        hFourier
    ) j

/--
The pair-specific complementary scalar state is exactly the scalar state of
its selected velocity coordinate.
-/
theorem h3TerminalComplementSpectralStateAt_eq_velocityComponent
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (p : H3TerminalCurlGradientPair)
    (t : ℝ)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T) :
    h3TerminalComplementSpectralStateAt
        hH3 p t ht
      =
    h3TerminalVelocityComponentSpectralStateAt
      hH3
      (
        h3ClassicalizationFinOfAxis
          (h3TerminalComplementComponentAxisForPair p)
      )
      t ht := by

  rfl

/-! ## Direct endpoint property for one physical velocity component -/

/--
One physical velocity coordinate has a strong weighted spectral H³ terminal
endpoint along the entire strict-time path.
-/
def H3TerminalVelocityComponentStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (j : Fin 3) : Prop :=
  ∃ Ginf : H3SpectralScalarState,
    h3SpectralScalarRealC1RepresentativeOnPoint3 Ginf
      =
    loggedVelocityComponent
      u T
      (h3AxisOfFin3 j)
      ∧
    ∀ ε : ℝ,
      0 < ε →
      ∃ η : ℝ,
        0 < η
          ∧
        ∀
          (t : ℝ)
          (ht : t ∈ Set.Ioo (0 : ℝ) T),
          dist t T < η →
            norm
              (
                h3TerminalVelocityComponentSpectralStateAt
                    hH3 j t ht
                  -
                Ginf
              )
              < ε

/--
The three physical velocity components all possess strong spectral H³
terminal endpoints.
-/
def H3TerminalVelocityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T) : Prop :=
  ∀ j : Fin 3,
    H3TerminalVelocityComponentStrongH3EndpointPath
      hH3 j

/-! ## One component endpoint supplies every pair using that component -/

/--
A strong endpoint for the physical velocity component selected by `p` gives
the pair-specific complementary strong endpoint.
-/
theorem strongH3EndpointPath_of_velocityComponent
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (p : H3TerminalCurlGradientPair)
    (hComponent :
      H3TerminalVelocityComponentStrongH3EndpointPath
        hH3
        (
          h3ClassicalizationFinOfAxis
            (h3TerminalComplementComponentAxisForPair p)
        )) :
    H3TerminalComplementGradientStrongH3EndpointPath
      hH3 p := by

  obtain
    ⟨
      Ginf,
      hTerminalRep,
      hModulus
    ⟩ :=
    hComponent

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
      hModulus ε hε

    refine
      ⟨
        η,
        hη,
        ?_
      ⟩

    intro t ht hTime

    have hAt :=
      hNear
        t
        ht
        hTime

    rw [
      h3TerminalComplementSpectralStateAt_eq_velocityComponent
        hH3 p t ht
    ]

    exact
      hAt

/-! ## Three component endpoints imply smooth continuation -/

/--
Strong H³ terminal endpoints for the three physical velocity components imply
the six pairwise path endpoints used by the terminal contradiction theorem.
-/
theorem allPairs_strongH3EndpointPath_of_velocityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hVelocity :
      H3TerminalVelocityStrongH3EndpointPath
        hH3) :
    ∀ p : H3TerminalCurlGradientPair,
      H3TerminalComplementGradientStrongH3EndpointPath
        hH3 p := by

  intro p

  exact
    strongH3EndpointPath_of_velocityComponent
      hH3
      p
      (
        hVelocity
          (
            h3ClassicalizationFinOfAxis
              (h3TerminalComplementComponentAxisForPair p)
          )
      )

/--
Three componentwise strong H³ terminal limits force smooth continuation.

This is the component-level form of the endpoint contradiction: the remaining
strong-H³ endpoint condition is no longer indexed by the six curl/gradient
pairs, only by the three physical velocity components.
-/
theorem smoothContinuationExtension_of_velocityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hVelocity :
      H3TerminalVelocityStrongH3EndpointPath
        hH3) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension
        u v T := by

  exact
    smoothContinuationExtension_of_allPairs_strongH3EndpointPath
      hH3
      hClass
      (
        allPairs_strongH3EndpointPath_of_velocityStrongH3EndpointPath
          hH3
          hVelocity
      )

end

end Euclidean
end Bridge
end PrimeTensor
