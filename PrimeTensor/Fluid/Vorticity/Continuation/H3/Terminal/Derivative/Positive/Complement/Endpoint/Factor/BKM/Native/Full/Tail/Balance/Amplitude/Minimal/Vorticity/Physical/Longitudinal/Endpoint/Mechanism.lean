import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Angular.Cone.Cauchy

/-!
# Split the surviving longitudinal endpoint obstruction

At the previous checkpoint, one physical vorticity component `i` was shown to
force pairwise Cauchy control of the same-index longitudinal velocity on every
fixed angular good cone.

The direct strong-H³ endpoint predicate contains two logically distinct
requirements:

1. the strict-time spectral state converges in weighted H³ to some
   `Ginf`;
2. that `Ginf` represents the actual terminal longitudinal velocity
   component.

Therefore failure of the longitudinal endpoint criterion should not be
identified automatically with failure of spectral convergence.

This file makes the exact split.

* **equatorial spectral-limit obstruction**:
  no global longitudinal spectral H³ limit exists, while every fixed angular
  good cone is asymptotically Cauchy;

* **terminal representation obstruction**:
  a global longitudinal spectral H³ limit exists, but that limit does not
  represent the actual terminal longitudinal velocity component.

Under hypothetical nonextension, any physical vorticity component that
retains its pathwise strong-H³ endpoint must produce one of these two
longitudinal mechanisms.

This is a neutral necessary-condition reduction.  It does not assert that
either mechanism actually occurs for a Navier–Stokes solution, nor that
failure of the sufficient continuation criterion by itself proves blowup.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Separate spectral convergence from terminal representation -/

/--
The strict-time spectral H³ state of velocity component `j` converges to
`Ginf` as time approaches `T` from below.

Unlike `H3TerminalVelocityComponentStrongH3EndpointPath`, this predicate says
nothing about whether `Ginf` represents the actual terminal velocity field.
-/
def H3TerminalVelocityComponentSpectralLimitPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (j : Fin 3)
    (Ginf : H3SpectralScalarState) : Prop :=
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
Velocity component `j` possesses some global strict-time spectral H³ limit at
the terminal time.
-/
def H3TerminalVelocityComponentHasSpectralLimitPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (j : Fin 3) : Prop :=
  ∃ Ginf : H3SpectralScalarState,
    H3TerminalVelocityComponentSpectralLimitPath
      hH3 j Ginf

/--
The original strong-H³ endpoint predicate is exactly a spectral path limit
whose H³ representative agrees with the actual terminal velocity component.
-/
theorem velocityComponentStrongH3EndpointPath_iff_exists_spectralLimit_and_terminalRepresentation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (j : Fin 3) :
    H3TerminalVelocityComponentStrongH3EndpointPath
        hH3 j
      ↔
    ∃ Ginf : H3SpectralScalarState,
      H3TerminalVelocityComponentSpectralLimitPath
          hH3 j Ginf
        ∧
      h3SpectralScalarRealC1RepresentativeOnPoint3 Ginf
        =
      loggedVelocityComponent
        u T
        (h3AxisOfFin3 j) := by

  constructor

  · rintro
      ⟨
        Ginf,
        hRep,
        hLimit
      ⟩

    exact
      ⟨
        Ginf,
        hLimit,
        hRep
      ⟩

  · rintro
      ⟨
        Ginf,
        hLimit,
        hRep
      ⟩

    exact
      ⟨
        Ginf,
        hRep,
        hLimit
      ⟩

/-! ## Fixed-good-cone Cauchy property -/

/--
For coordinate `i`, the longitudinal defect becomes arbitrarily small on
every fixed angular good cone.
-/
def H3TerminalLongitudinalGoodConeCauchyControl
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (i : Fin 3) : Prop :=
  ∀
    (κ : ℝ),
    0 < κ →
    ∀
      (r : ℝ),
      0 < r →
      ∃ η : ℝ,
        0 < η
          ∧
        ∀
          (s : ℝ)
          (hs : s ∈ Set.Ioo (0 : ℝ) T)
          (t : ℝ)
          (ht : t ∈ Set.Ioo (0 : ℝ) T),
          dist s T < η →
          dist t T < η →
            h3TerminalLongitudinalGoodConeScaledSquareDefect
                i κ
                (h3TerminalVelocitySpectralStateAt hH3 s hs)
                (h3TerminalVelocitySpectralStateAt hH3 t ht)
              <
            4 * r ^ 2

/--
A physical-vorticity strong-H³ endpoint forces fixed-good-cone longitudinal
Cauchy control.
-/
theorem longitudinalGoodConeCauchyControl_of_actualVorticityStrongH3EndpointPath
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {i : Fin 3}
    (hPhysical :
      H3TerminalActualVorticityStrongH3EndpointPath
        hH3 i) :
    H3TerminalLongitudinalGoodConeCauchyControl
      hH3 i := by

  intro κ hκ r hr

  exact
    longitudinalGoodConeScaledSquareDefect_lt_four_mul_sq_of_actualVorticityStrongH3EndpointPath
      hH3
      hPhysical
      hκ
      hr

/-! ## The two longitudinal mechanisms -/

/--
No global longitudinal spectral H³ limit exists, even though every fixed
angular good cone is asymptotically Cauchy.

This isolates the only place where genuine nonconvergence can still hide:
toward the complementary equatorial angular region.
-/
def H3TerminalLongitudinalEquatorialSpectralLimitObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (i : Fin 3) : Prop :=
  ¬
    H3TerminalVelocityComponentHasSpectralLimitPath
      hH3 i
    ∧
  H3TerminalLongitudinalGoodConeCauchyControl
    hH3 i

/--
A global longitudinal spectral H³ limit exists, but its real C¹
representative is not the actual terminal longitudinal velocity component.
-/
def H3TerminalLongitudinalTerminalRepresentationObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (i : Fin 3) : Prop :=
  ∃ Ginf : H3SpectralScalarState,
    H3TerminalVelocityComponentSpectralLimitPath
        hH3 i Ginf
      ∧
    h3SpectralScalarRealC1RepresentativeOnPoint3 Ginf
      ≠
    loggedVelocityComponent
      u T
      (h3AxisOfFin3 i)

/-! ## Exact logical split of endpoint failure -/

/--
Failure of the strong-H³ endpoint criterion splits exactly into either absence
of any global spectral H³ limit, or existence of a spectral limit that fails
terminal representation.
-/
theorem noSpectralLimit_or_terminalRepresentationObstruction_of_velocityComponentStrongH3EndpointPathFailure
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (i : Fin 3)
    (hFailure :
      ¬
        H3TerminalVelocityComponentStrongH3EndpointPath
          hH3 i) :
    (
      ¬
        H3TerminalVelocityComponentHasSpectralLimitPath
          hH3 i
    )
      ∨
    H3TerminalLongitudinalTerminalRepresentationObstruction
      hH3 i := by

  by_cases hLimit :
      H3TerminalVelocityComponentHasSpectralLimitPath
        hH3 i

  · right

    obtain
      ⟨
        Ginf,
        hGinf
      ⟩ :=
      hLimit

    refine
      ⟨
        Ginf,
        hGinf,
        ?_
      ⟩

    intro hRep

    exact
      hFailure
        ⟨
          Ginf,
          hRep,
          hGinf
        ⟩

  · exact
      Or.inl
        hLimit

/-! ## Physical endpoint + hypothetical nonextension -/

/--
Under hypothetical nonextension, a surviving physical-vorticity endpoint
forces one of the two precise longitudinal mechanisms.
-/
theorem longitudinalEquatorialSpectralLimit_or_terminalRepresentationObstruction_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
    H3TerminalLongitudinalEquatorialSpectralLimitObstruction
        hH3 i
      ∨
    H3TerminalLongitudinalTerminalRepresentationObstruction
        hH3 i := by

  have hFailure :
      ¬
        H3TerminalVelocityComponentStrongH3EndpointPath
          hH3 i :=
    longitudinalVelocityStrongH3EndpointPath_failure_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical

  rcases
    noSpectralLimit_or_terminalRepresentationObstruction_of_velocityComponentStrongH3EndpointPathFailure
      hH3
      i
      hFailure
    with hNoLimit | hRepresentation

  · exact
      Or.inl
        ⟨
          hNoLimit,
          longitudinalGoodConeCauchyControl_of_actualVorticityStrongH3EndpointPath
            hH3
            hPhysical
        ⟩

  · exact
      Or.inr
        hRepresentation

/-! ## Global neutral alternative -/

/--
Sequence-free global classification.

Either the H³ path extends smoothly, every physical-vorticity component fails
its pathwise strong-H³ endpoint criterion, or some surviving physical
component exhibits one of the two precise longitudinal mechanisms:

* equatorial spectral nonconvergence with fixed-good-cone Cauchy control;
* terminal representation failure of a genuine spectral H³ limit.
-/
theorem smoothContinuationExtension_or_allActualVorticityStrongH3EndpointsFail_or_longitudinalEndpointMechanism
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
          H3TerminalActualVorticityStrongH3EndpointPath
              hH3 i
            ∧
          (
            H3TerminalLongitudinalEquatorialSpectralLimitObstruction
                hH3 i
              ∨
            H3TerminalLongitudinalTerminalRepresentationObstruction
                hH3 i
          )
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

  · right

    by_cases hAllFail :
        ∀ i : Fin 3,
          ¬
            H3TerminalActualVorticityStrongH3EndpointPath
              hH3 i

    · exact
        Or.inl
          hAllFail

    · right

      have hExists :
          ∃ i : Fin 3,
            H3TerminalActualVorticityStrongH3EndpointPath
              hH3 i := by

        by_contra hNone

        apply hAllFail

        intro i hPhysical

        exact
          hNone
            ⟨
              i,
              hPhysical
            ⟩

      obtain
        ⟨
          i,
          hPhysical
        ⟩ :=
        hExists

      refine
        ⟨
          i,
          hPhysical,
          ?_
        ⟩

      exact
        longitudinalEquatorialSpectralLimit_or_terminalRepresentationObstruction_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
          hH3
          hExtension
          hClass
          hPhysical

end

end Euclidean
end Bridge
end PrimeTensor
