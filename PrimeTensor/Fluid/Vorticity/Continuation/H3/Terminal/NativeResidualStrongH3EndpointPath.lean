import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualStrongH3EndpointContradiction

/-!
# Replace all selected-sequence endpoint hypotheses by one pathwise H³ limit

The strong-H³ contradiction theorem was phrased using

    every strict selected terminal sequence has a strong H³ endpoint.

That is a convenient sequential interface, but it is not the natural analytic
frontier.

This file introduces the actual complementary scalar spectral H³ state at an
arbitrary strict time `t < T` and states the direct pathwise endpoint property:

    there is one terminal spectral state `G∞`,
    representing the actual terminal velocity component,
    such that the strict-time spectral state approaches `G∞`
    in H³ norm as `t ↑ T`.

The direct time-local modulus immediately specializes to every selected
terminal sequence.  Therefore an all-pairs pathwise strong H³ endpoint implies
the already-proved all-sequences hypothesis and hence smooth continuation.

This removes the sequence quantifier from the remaining analytic condition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalStrongEndpointPath
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Actual strict-time complementary spectral state -/

/--
The spectral H³ scalar state of the complementary velocity component at an
arbitrary strict preterminal time.
-/
noncomputable def h3TerminalComplementSpectralStateAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (p : H3TerminalCurlGradientPair)
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
    )
      (
        h3ClassicalizationFinOfAxis
          (h3TerminalComplementComponentAxisForPair p)
      )

/--
The selected-sequence spectral state is definitionally the arbitrary
strict-time state specialized to the selected time.
-/
theorem h3TerminalSelectedComplementSpectralState_eq_at
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {τ : ℕ → ℝ}
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    (p : H3TerminalCurlGradientPair)
    (n : ℕ) :
    h3TerminalSelectedComplementSpectralState
        hH3 hTauStrict p n
      =
    h3TerminalComplementSpectralStateAt
      hH3 p (τ n) (hTauStrict n) := by

  rfl

/-! ## Direct pathwise strong H³ endpoint -/

/--
One fixed pair has a genuine strong spectral H³ endpoint along the entire
strict-time path.

The modulus is stated directly in physical time rather than through any
chosen sequence.
-/
def H3TerminalComplementGradientStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (p : H3TerminalCurlGradientPair) : Prop :=
  ∃ Ginf : H3SpectralScalarState,
    h3SpectralScalarRealC1RepresentativeOnPoint3 Ginf
      =
    loggedVelocityComponent
      u T
      (h3TerminalComplementComponentAxisForPair p)
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
                h3TerminalComplementSpectralStateAt
                    hH3 p t ht
                  -
                Ginf
              )
              < ε

/-! ## Pathwise endpoint specializes to every selected sequence -/

/--
A direct pathwise strong H³ endpoint gives the selected strong endpoint on any
strict selected time sequence.

No use of convergence of the sequence is needed at this step: the pathwise
time-local modulus is already stronger than the selected-sequence modulus.
-/
theorem selectedStrongH3Endpoint_of_strongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {τ : ℕ → ℝ}
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    {p : H3TerminalCurlGradientPair}
    (hPath :
      H3TerminalComplementGradientStrongH3EndpointPath
        hH3 p) :
    H3TerminalComplementGradientSelectedStrongH3Endpoint
      hH3 hTauStrict p := by

  obtain
    ⟨
      Ginf,
      hTerminalRep,
      hPathModulus
    ⟩ :=
    hPath

  refine
    ⟨
      Ginf,
      hTerminalRep,
      ?_
    ⟩

  intro ε hε

  obtain
    ⟨
      η,
      hη,
      hNear
    ⟩ :=
    hPathModulus
      ε hε

  refine
    ⟨
      η,
      hη,
      ?_
    ⟩

  intro n hTime

  rw [
    h3TerminalSelectedComplementSpectralState_eq_at
      hH3 hTauStrict p n
  ]

  exact
    hNear
      (τ n)
      (hTauStrict n)
      hTime

/--
A direct pathwise strong H³ endpoint gives the existing
all-selected-terminal-sequences predicate.
-/
theorem strongH3EndpointOnAllSelectedTerminalSequences_of_path
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {p : H3TerminalCurlGradientPair}
    (hPath :
      H3TerminalComplementGradientStrongH3EndpointPath
        hH3 p) :
    H3TerminalComplementGradientStrongH3EndpointOnAllSelectedTerminalSequences
      hH3 p := by

  intro τ hTauStrict _hTau

  exact
    selectedStrongH3Endpoint_of_strongH3EndpointPath
      hH3
      hTauStrict
      hPath

/-! ## Direct pathwise criterion forces continuation -/

/--
If every terminal pair has one direct strong H³ endpoint along the actual
preterminal path, then the solution admits a smooth continuation extension.

This is the sequence-free form of the strong-H³ contradiction theorem.
-/
theorem smoothContinuationExtension_of_allPairs_strongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (hClass :
      PreterminalH3EnergyClass
        u a T)
    (hAllPath :
      ∀ p : H3TerminalCurlGradientPair,
        H3TerminalComplementGradientStrongH3EndpointPath
          hH3 p) :
    ∃
      v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension
        u v T := by

  apply
    smoothContinuationExtension_of_allPairs_strongH3Endpoint
      hH3
      hClass

  intro p

  exact
    strongH3EndpointOnAllSelectedTerminalSequences_of_path
      hH3
      (hAllPath p)

end

end Euclidean
end Bridge
end PrimeTensor
