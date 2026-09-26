import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.NativeResidualSpatialDecayAutomatic
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Selected.Spatial.First

/-!
# Reduce the terminal temporal modulus to strong spectral H³ endpoint control

The terminal geometry still assumes

    H3TerminalComplementGradientSelectedEndpointTemporalModulus,

a uniform-in-selected-space convergence of one first velocity derivative to
its actual terminal value.

This file identifies a clean sufficient Banach-space condition.

For arbitrary spectral H³ scalar states `F,G`, the already-proved evaluation
estimate gives, uniformly in the physical point,

    |∂ₐ Rep(F)(x) - ∂ₐ Rep(G)(x)|
      ≤ C₁ ‖F-G‖_{H³}.

Therefore, if the selected strict-time scalar H³ states approach a terminal
spectral H³ state in a time-local uniform modulus, and that terminal state
represents the actual terminal velocity component, then the required endpoint
temporal modulus follows immediately.

This does not claim that strong H³ endpoint convergence has already been
proved.  Rather, it relocates the remaining temporal frontier from pointwise
derivative language to the natural H³ Banach-space endpoint question.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3TerminalResidualEndpointH3Criterion
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## The actual selected strict-time scalar H³ state -/

/--
The spectral H³ scalar state of the selected complementary velocity component
at one strict selected time.
-/
noncomputable def h3TerminalSelectedComplementSpectralState
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
    H3SpectralScalarState := by

  let hNS :
      LoggedPreterminalNavierStokesAdmissible
        u T :=
    hH3.navier_stokes

  let hInt :
      VelocityH3IntegrableAt
        u (τ n) :=
    hH3.velocity_h3_integrable
      (τ n)
      (hTauStrict n)

  let hMeas :
      VelocityH3MeasurableAt
        u (τ n) :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS
      (hTauStrict n)

  let hFourier :
      VelocityH3FourierCompatibleAt
        u (τ n) hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS
      (hTauStrict n)
      hInt

  exact
    (
      velocityH3SpectralStateAt
        u
        (τ n)
        hInt
        hMeas
        hFourier
    )
      (
        h3ClassicalizationFinOfAxis
          (h3TerminalComplementComponentAxisForPair p)
      )

/--
The canonical real C¹ representative of the actual selected strict-time H³
state is pointwise the corresponding old logged velocity component.
-/
theorem h3TerminalSelectedComplementSpectralState_representative_eq_loggedVelocityComponent
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
    h3SpectralScalarRealC1RepresentativeOnPoint3
        (
          h3TerminalSelectedComplementSpectralState
            hH3 hTauStrict p n
        )
      =
    loggedVelocityComponent
      u
      (τ n)
      (h3TerminalComplementComponentAxisForPair p) := by

  let hNS :
      LoggedPreterminalNavierStokesAdmissible
        u T :=
    hH3.navier_stokes

  let hInt :
      VelocityH3IntegrableAt
        u (τ n) :=
    hH3.velocity_h3_integrable
      (τ n)
      (hTauStrict n)

  let hMeas :
      VelocityH3MeasurableAt
        u (τ n) :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hNS
      (hTauStrict n)

  let hFourier :
      VelocityH3FourierCompatibleAt
        u (τ n) hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hNS
      (hTauStrict n)
      hInt

  let j : Fin 3 :=
    h3ClassicalizationFinOfAxis
      (h3TerminalComplementComponentAxisForPair p)

  have hAE :
      h3SpectralScalarRealC1RepresentativeOnPoint3
          (
            (
              velocityH3SpectralStateAt
                u
                (τ n)
                hInt
                hMeas
                hFourier
            ) j
          )
        =ᵐ[(volume : Measure Point3)]
      loggedVelocityComponent
        u
        (τ n)
        (h3AxisOfFin3 j) := by

    exact
      h3SpectralVelocityRealC1RepresentativeOnPoint3_velocityH3SpectralStateAt_ae_eq_loggedVelocityComponent
        hFourier
        j

  have hLeft :
      Continuous
        (
          h3SpectralScalarRealC1RepresentativeOnPoint3
            (
              (
                velocityH3SpectralStateAt
                  u
                  (τ n)
                  hInt
                  hMeas
                  hFourier
              ) j
            )
        ) :=
    (
      h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one
        (
          (
            velocityH3SpectralStateAt
              u
              (τ n)
              hInt
              hMeas
              hFourier
          ) j
        )
    ).continuous

  have hRight :
      Continuous
        (
          loggedVelocityComponent
            u
            (τ n)
            (h3AxisOfFin3 j)
        ) := by

    let pressure :
        ℝ → ScalarField3 :=
      Classical.choose hNS

    let hPDE :
        PreterminalNavierStokes3
          (logSpaceTimeVectorField u)
          pressure
          T :=
      Classical.choose_spec hNS

    unfold loggedVelocityComponent

    exact
      (
        hPDE.regularity.velocity_spatial_three
          (τ n)
          (hTauStrict n)
          (h3AxisOfFin3 j)
      ).continuous

  have hPointwise :
      h3SpectralScalarRealC1RepresentativeOnPoint3
          (
            (
              velocityH3SpectralStateAt
                u
                (τ n)
                hInt
                hMeas
                hFourier
            ) j
          )
        =
      loggedVelocityComponent
        u
        (τ n)
        (h3AxisOfFin3 j) :=
    MeasureTheory.Measure.eq_of_ae_eq
      hAE
      hLeft
      hRight

  have hAxis :
      h3AxisOfFin3 j
        =
      h3TerminalComplementComponentAxisForPair p := by

    dsimp only [j]

    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
        (h3TerminalComplementComponentAxisForPair p)

  unfold h3TerminalSelectedComplementSpectralState

  dsimp only

  rw [hAxis] at hPointwise

  exact
    hPointwise

/-! ## Abstract H³ endpoint criterion -/

/--
A pair-specific strong spectral H³ endpoint criterion.

`Ginf` represents the actual terminal complementary velocity component, and the
actual selected strict-time H³ scalar states approach `Ginf` with a modulus
measured by closeness of the selected physical time to `T`.
-/
def H3TerminalComplementGradientSelectedStrongH3Endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {τ : ℕ → ℝ}
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
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
        ∀ n : ℕ,
          dist (τ n) T < η →
          norm
            (
              h3TerminalSelectedComplementSpectralState
                  hH3 hTauStrict p n
                -
              Ginf
            )
            < ε

/-! ## H³ endpoint control implies the terminal derivative modulus -/

/--
The strong spectral H³ endpoint criterion implies the uniform selected
endpoint temporal modulus for the complementary first derivative.
-/
theorem selectedEndpointTemporalModulus_of_strongH3Endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 :
      LoggedPreterminalH3PathAdmissible
        u T)
    {τ : ℕ → ℝ}
    (hTauStrict :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo (0 : ℝ) T)
    {x : ℕ → Point3}
    {p : H3TerminalCurlGradientPair}
    (hStrong :
      H3TerminalComplementGradientSelectedStrongH3Endpoint
        hH3 hTauStrict p) :
    H3TerminalComplementGradientSelectedEndpointTemporalModulus
      u p τ x T := by

  obtain
    ⟨
      Ginf,
      hTerminalRep,
      hH3Modulus
    ⟩ :=
    hStrong

  let i : Fin 3 :=
    h3ClassicalizationFinOfAxis
      (h3TerminalComplementDerivativeAxisForPair p)

  let K : ℝ :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient

  have hK :
      0 ≤ K := by

    dsimp only [K]

    exact
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg

  have hAxis :
      h3AxisOfFin3 i
        =
      h3TerminalComplementDerivativeAxisForPair p := by

    dsimp only [i]

    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis
        (h3TerminalComplementDerivativeAxisForPair p)

  intro ε hε

  have hKOne :
      0 < K + 1 := by
    linarith

  have hScaledPos :
      0 < ε / (K + 1) :=
    div_pos hε hKOne

  obtain
    ⟨
      η,
      hη,
      hState
    ⟩ :=
    hH3Modulus
      (ε / (K + 1))
      hScaledPos

  refine
    ⟨
      η,
      hη,
      ?_
    ⟩

  intro r n hTime

  let Gn : H3SpectralScalarState :=
    h3TerminalSelectedComplementSpectralState
      hH3 hTauStrict p n

  have hStateSmall :
      ‖Gn - Ginf‖ < ε / (K + 1) := by

    dsimp only [Gn]

    exact
      hState
        n
        hTime

  have hSelectedRep :
      h3SpectralScalarRealC1RepresentativeOnPoint3 Gn
        =
      loggedVelocityComponent
        u
        (τ n)
        (h3TerminalComplementComponentAxisForPair p) := by

    dsimp only [Gn]

    exact
      h3TerminalSelectedComplementSpectralState_representative_eq_loggedVelocityComponent
        hH3 hTauStrict p n

  have hSelectedDerivative :
      spatial3.d
          (h3TerminalComplementDerivativeAxisForPair p)
          (
            h3SpectralScalarRealC1RepresentativeOnPoint3
              Gn
          )
          (x r)
        =
      h3TerminalComplementGradientFieldForPair
        u p
        (τ n)
        (x r) := by

    rw [hSelectedRep]

    change
      spatial3.d
          (h3TerminalComplementDerivativeAxisForPair p)
          (
            loggedVelocityComponent
              u
              (τ n)
              (h3TerminalComplementComponentAxisForPair p)
          )
          (x r)
        =
      _

    rfl

  have hTerminalDerivative :
      spatial3.d
          (h3TerminalComplementDerivativeAxisForPair p)
          (
            h3SpectralScalarRealC1RepresentativeOnPoint3
              Ginf
          )
          (x r)
        =
      h3TerminalComplementGradientFieldForPair
        u p
        T
        (x r) := by

    rw [hTerminalRep]

    change
      spatial3.d
          (h3TerminalComplementDerivativeAxisForPair p)
          (
            loggedVelocityComponent
              u
              T
              (h3TerminalComplementComponentAxisForPair p)
          )
          (x r)
        =
      _

    rfl

  have hDerivativeBoundRaw :=
    norm_h3SpectralScalarRealC1RepresentativeOnPoint3_spatial_d_sub_apply_le
      Gn
      Ginf
      i
      (x r)

  have hDerivativeBound :
      dist
          (
            spatial3.d
              (h3TerminalComplementDerivativeAxisForPair p)
              (
                h3SpectralScalarRealC1RepresentativeOnPoint3
                  Gn
              )
              (x r)
          )
          (
            spatial3.d
              (h3TerminalComplementDerivativeAxisForPair p)
              (
                h3SpectralScalarRealC1RepresentativeOnPoint3
                  Ginf
              )
              (x r)
          )
        ≤
      K * ‖Gn - Ginf‖ := by

    rw [hAxis] at hDerivativeBoundRaw

    dsimp only [K]

    simpa only [
      Real.dist_eq,
      Real.norm_eq_abs
    ] using
      hDerivativeBoundRaw

  have hScaledUpper :
      K * ‖Gn - Ginf‖
        ≤
      K * (ε / (K + 1)) :=
    mul_le_mul_of_nonneg_left
      (le_of_lt hStateSmall)
      hK

  have hFraction :
      K * (ε / (K + 1)) < ε := by

    have hRatio :
        K / (K + 1) < 1 :=
      (div_lt_one hKOne).2
        (by linarith)

    calc
      K * (ε / (K + 1))
          =
        ε * (K / (K + 1)) := by
          ring
      _ <
        ε * 1 :=
          mul_lt_mul_of_pos_left
            hRatio
            hε
      _ = ε := by
        ring

  rw [
    ← hSelectedDerivative,
    ← hTerminalDerivative
  ]

  exact
    lt_of_le_of_lt
      hDerivativeBound
      (
        lt_of_le_of_lt
          hScaledUpper
          hFraction
      )

end

end Euclidean
end Bridge
end PrimeTensor
