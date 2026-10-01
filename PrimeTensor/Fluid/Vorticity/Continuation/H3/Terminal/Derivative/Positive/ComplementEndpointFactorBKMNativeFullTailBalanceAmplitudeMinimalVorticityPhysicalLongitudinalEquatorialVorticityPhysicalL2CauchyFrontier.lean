import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityPhysicalLongitudinalEquatorialVorticityInfraredVanishingFromRawL2Cauchy
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.RHS.Continuity

/-!
# Physical kinetic L² form of the terminal infrared frontier

The preceding checkpoint reduced infrared normalized-vorticity concentration
to a terminal Cauchy condition for the deweighted/raw Fourier velocity.

That condition is not a genuinely new Fourier hypothesis.  On every strict
preterminal snapshot, exact H³ deweighting recovers the ordinary zeroth-order
Fourier transform of the physical velocity, and scalar Plancherel is an
isometry.

This file therefore identifies the raw Fourier square defect exactly with the
three-component physical kinetic `L²` square defect.

Consequently

    terminal raw-Fourier L² Cauchy

is equivalent to

    terminal physical velocity L² Cauchy.

The infrared branch can hence be closed by ordinary strong kinetic `L²`
terminal control.  The next remaining analytic issue is whether the already
available weak zeroth-order endpoint continuity has a terminal norm/energy
defect.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalPhysicalLongitudinalEquatorialVorticityPhysicalL2CauchyFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Canonical strict-time physical velocity -/

/--
The ordinary physical zeroth-order `L²` velocity component at one strict
preterminal time.
-/
noncomputable def h3TerminalPhysicalVelocityComponentAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (t : ℝ)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T)
    (j : Fin 3) :
    H3ScalarL2 := by

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

  exact
    velocityH3L2JetAt
      u t hInt hMeas
      (h3JetSlot0 j)

/--
Three-component physical kinetic `L²` square defect between two strict
preterminal times.
-/
noncomputable def h3TerminalPhysicalVelocityTotalSquareDefect
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (s t : ℝ)
    (hs :
      s ∈ Set.Ioo (0 : ℝ) T)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T) : ℝ :=
  norm
      (
        h3TerminalPhysicalVelocityComponentAt
          hH3 s hs 0
          -
        h3TerminalPhysicalVelocityComponentAt
          hH3 t ht 0
      ) ^ 2
    +
  norm
      (
        h3TerminalPhysicalVelocityComponentAt
          hH3 s hs 1
          -
        h3TerminalPhysicalVelocityComponentAt
          hH3 t ht 1
      ) ^ 2
    +
  norm
      (
        h3TerminalPhysicalVelocityComponentAt
          hH3 s hs 2
          -
        h3TerminalPhysicalVelocityComponentAt
          hH3 t ht 2
      ) ^ 2

/-! ## Strict-time raw Fourier / physical identification -/

/--
At every strict preterminal snapshot, deweighting the terminal H³ spectral
state gives exactly the scalar Plancherel transform of the ordinary physical
velocity component.
-/
theorem h3TerminalRawVelocityFourierComponent_velocitySpectralStateAt_eq_scalarFourierL2_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (t : ℝ)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T)
    (j : Fin 3) :
    h3TerminalRawVelocityFourierComponent
        (h3TerminalVelocitySpectralStateAt
          hH3 t ht)
        j
      =
    h3ScalarFourierL2
      (
        h3TerminalPhysicalVelocityComponentAt
          hH3 t ht j
      ) := by

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

  unfold
    h3TerminalRawVelocityFourierComponent
    h3TerminalVelocitySpectralStateAt
    h3TerminalPhysicalVelocityComponentAt

  dsimp only

  rw [
    h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
      hFourier j
  ]

  rfl

/-! ## Exact raw Fourier square defect -/

/--
The integral definition of the total raw Fourier velocity defect is exactly the
sum of the three coordinate `L²` distance squares.
-/
theorem h3TerminalRawVelocityFourierTotalSquareDefect_eq_coordinate_norm_squares
    (G H : H3SpectralFinVectorState) :
    h3TerminalRawVelocityFourierTotalSquareDefect
        G H
      =
    norm
        (
          h3TerminalRawVelocityFourierComponent G 0
            -
          h3TerminalRawVelocityFourierComponent H 0
        ) ^ 2
      +
    norm
        (
          h3TerminalRawVelocityFourierComponent G 1
            -
          h3TerminalRawVelocityFourierComponent H 1
        ) ^ 2
      +
    norm
        (
          h3TerminalRawVelocityFourierComponent G 2
            -
          h3TerminalRawVelocityFourierComponent H 2
        ) ^ 2 := by

  have h0 :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalRawVelocityFourierComponent G 0 ξ
                  -
                h3TerminalRawVelocityFourierComponent H 0 ξ
              ) ^ 2
        )
        volume :=
    h3FourierComplexL2_pointwise_sub_norm_sq_integrable
      (h3TerminalRawVelocityFourierComponent G 0)
      (h3TerminalRawVelocityFourierComponent H 0)

  have h1 :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalRawVelocityFourierComponent G 1 ξ
                  -
                h3TerminalRawVelocityFourierComponent H 1 ξ
              ) ^ 2
        )
        volume :=
    h3FourierComplexL2_pointwise_sub_norm_sq_integrable
      (h3TerminalRawVelocityFourierComponent G 1)
      (h3TerminalRawVelocityFourierComponent H 1)

  have h2 :
      Integrable
        (
          fun ξ : H3FourierPoint3 =>
            norm
              (
                h3TerminalRawVelocityFourierComponent G 2 ξ
                  -
                h3TerminalRawVelocityFourierComponent H 2 ξ
              ) ^ 2
        )
        volume :=
    h3FourierComplexL2_pointwise_sub_norm_sq_integrable
      (h3TerminalRawVelocityFourierComponent G 2)
      (h3TerminalRawVelocityFourierComponent H 2)

  unfold
    h3TerminalRawVelocityFourierTotalSquareDefect
    h3TerminalRawVelocityFourierTotalSquareDensity

  rw [
    integral_add
      (h0.add h1)
      h2,
    integral_add
      h0
      h1
  ]

  rw [
    ← h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq,
    ← h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq,
    ← h3FourierComplexL2_sub_norm_sq_eq_integral_pointwise_sub_norm_sq
  ]

/-! ## Exact Plancherel identification -/

/--
At two strict preterminal times, the total raw Fourier velocity square defect
is exactly the physical three-component kinetic `L²` square defect.
-/
theorem h3TerminalRawVelocityFourierTotalSquareDefect_velocitySpectralStateAt_eq_physical
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    (s t : ℝ)
    (hs :
      s ∈ Set.Ioo (0 : ℝ) T)
    (ht :
      t ∈ Set.Ioo (0 : ℝ) T) :
    h3TerminalRawVelocityFourierTotalSquareDefect
        (h3TerminalVelocitySpectralStateAt
          hH3 s hs)
        (h3TerminalVelocitySpectralStateAt
          hH3 t ht)
      =
    h3TerminalPhysicalVelocityTotalSquareDefect
      hH3 s t hs ht := by

  rw [
    h3TerminalRawVelocityFourierTotalSquareDefect_eq_coordinate_norm_squares
  ]

  rw [
    h3TerminalRawVelocityFourierComponent_velocitySpectralStateAt_eq_scalarFourierL2_physical
      hH3 s hs 0,
    h3TerminalRawVelocityFourierComponent_velocitySpectralStateAt_eq_scalarFourierL2_physical
      hH3 t ht 0,
    h3TerminalRawVelocityFourierComponent_velocitySpectralStateAt_eq_scalarFourierL2_physical
      hH3 s hs 1,
    h3TerminalRawVelocityFourierComponent_velocitySpectralStateAt_eq_scalarFourierL2_physical
      hH3 t ht 1,
    h3TerminalRawVelocityFourierComponent_velocitySpectralStateAt_eq_scalarFourierL2_physical
      hH3 s hs 2,
    h3TerminalRawVelocityFourierComponent_velocitySpectralStateAt_eq_scalarFourierL2_physical
      hH3 t ht 2
  ]

  unfold
    h3TerminalPhysicalVelocityTotalSquareDefect

  rw [
    ← h3ScalarFourierL2_sub,
    norm_h3ScalarFourierL2,
    ← h3ScalarFourierL2_sub,
    norm_h3ScalarFourierL2,
    ← h3ScalarFourierL2_sub,
    norm_h3ScalarFourierL2
  ]

/-! ## Physical terminal kinetic L² Cauchy property -/

/--
Terminal Cauchy property in ordinary physical kinetic `L²`, expressed as the
sum of the three component distance squares.
-/
def H3TerminalVelocityPhysicalL2CauchyAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T) : Prop :=
  ∀ δ : ℝ,
    0 < δ
      →
    ∃ η : ℝ,
      0 < η
        ∧
      ∀ s t : ℝ,
        ∀ hs :
          s ∈ Set.Ioo (0 : ℝ) T,
          ∀ ht :
            t ∈ Set.Ioo (0 : ℝ) T,
            dist s T < η
              →
            dist t T < η
              →
            h3TerminalPhysicalVelocityTotalSquareDefect
                hH3 s t hs ht
              <
            δ

/--
The raw-Fourier terminal Cauchy condition is exactly equivalent to the ordinary
physical kinetic `L²` terminal Cauchy condition.
-/
theorem velocityRawFourierL2CauchyAtEndpoint_iff_physicalL2CauchyAtEndpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T) :
    H3TerminalVelocityRawFourierL2CauchyAtEndpoint
        hH3
      ↔
    H3TerminalVelocityPhysicalL2CauchyAtEndpoint
        hH3 := by

  constructor

  · intro hRaw
    intro δ hδ

    obtain
      ⟨
        η,
        hη,
        hCauchy
      ⟩ :=
      hRaw δ hδ

    refine
      ⟨
        η,
        hη,
        ?_
      ⟩

    intro s t hs ht hsNear htNear

    rw [
      ← h3TerminalRawVelocityFourierTotalSquareDefect_velocitySpectralStateAt_eq_physical
        hH3 s t hs ht
    ]

    exact
      hCauchy
        s t hs ht
        hsNear htNear

  · intro hPhysical
    intro δ hδ

    obtain
      ⟨
        η,
        hη,
        hCauchy
      ⟩ :=
      hPhysical δ hδ

    refine
      ⟨
        η,
        hη,
        ?_
      ⟩

    intro s t hs ht hsNear htNear

    rw [
      h3TerminalRawVelocityFourierTotalSquareDefect_velocitySpectralStateAt_eq_physical
        hH3 s t hs ht
    ]

    exact
      hCauchy
        s t hs ht
        hsNear htNear

/-! ## Conditional radial closure in physical kinetic form -/

/--
Ordinary terminal physical kinetic `L²` Cauchy control excludes the diagonal
infrared branch.  Under hypothetical nonextension with one surviving physical
vorticity endpoint, a failing complementary vorticity component must therefore
carry the positive-cutoff high-radial raw-vorticity obstruction.
-/
theorem exists_failing_complementary_vorticityComponent_highRadialRaw_of_velocityPhysicalL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
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
        hH3 i)
    (hPhysicalL2Cauchy :
      H3TerminalVelocityPhysicalL2CauchyAtEndpoint
        hH3)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ρ : ℝ,
      0 < ρ
        ∧
      ∃ q : Fin 3,
        q ≠ i
          ∧
        ¬
          H3TerminalActualVorticityStrongH3EndpointPath
            hH3 q
          ∧
        H3TerminalHighRadialRawVorticityBranchAtCutoff
          hH3 i q ε ρ := by

  apply
    exists_failing_complementary_vorticityComponent_highRadialRaw_of_velocityRawFourierL2Cauchy_of_actualVorticityStrongH3EndpointPath_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hPhysical

  · exact
      (
        velocityRawFourierL2CauchyAtEndpoint_iff_physicalL2CauchyAtEndpoint
          hH3
      ).2
        hPhysicalL2Cauchy

  · exact
      hε

end

end Euclidean
end Bridge
end PrimeTensor
