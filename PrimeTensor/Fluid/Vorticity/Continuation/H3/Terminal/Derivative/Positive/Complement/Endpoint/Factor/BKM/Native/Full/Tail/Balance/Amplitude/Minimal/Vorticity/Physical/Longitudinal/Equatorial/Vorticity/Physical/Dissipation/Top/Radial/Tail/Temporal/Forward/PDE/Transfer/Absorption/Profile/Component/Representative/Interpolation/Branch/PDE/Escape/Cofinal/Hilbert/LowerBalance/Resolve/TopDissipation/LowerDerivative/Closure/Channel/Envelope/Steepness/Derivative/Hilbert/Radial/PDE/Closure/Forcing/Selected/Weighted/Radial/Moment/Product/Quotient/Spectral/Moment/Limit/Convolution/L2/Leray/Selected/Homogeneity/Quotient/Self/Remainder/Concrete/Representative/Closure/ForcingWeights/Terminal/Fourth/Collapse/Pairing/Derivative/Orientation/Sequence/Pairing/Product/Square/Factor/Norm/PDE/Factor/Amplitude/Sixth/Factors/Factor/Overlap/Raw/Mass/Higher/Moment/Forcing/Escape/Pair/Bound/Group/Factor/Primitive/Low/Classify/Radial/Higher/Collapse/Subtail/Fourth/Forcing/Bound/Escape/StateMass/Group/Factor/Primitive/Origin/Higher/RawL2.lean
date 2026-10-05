import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative.Interpolation.Branch.PDE.Escape.Cofinal.Hilbert.LowerBalance.Resolve.TopDissipation.LowerDerivative.Closure.Channel.Envelope.Steepness.Derivative.Hilbert.Radial.PDE.Closure.Forcing.Selected.Weighted.Radial.Moment.Product.Quotient.Spectral.Moment.Limit.Convolution.L2.Leray.Selected.Homogeneity.Quotient.Self.Remainder.Concrete.Representative.Closure.ForcingWeights.Terminal.Fourth.Collapse.Pairing.Derivative.Orientation.Sequence.Pairing.Product.Square.Factor.Norm.PDE.Factor.Amplitude.Sixth.Factors.Factor.Overlap.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify.Radial.Higher.Collapse.Subtail.Fourth.Forcing.Bound.Escape.StateMass.Group.Factor.Primitive.Origin.Higher
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.RHS.Bound

/-!
# Absorb projected-RHS raw L² escape into physical H³ energy

The canonical chosen fourth-q Leray datum now retains both:

* `U =` the terminal physical weighted H³ spectral velocity state;
* the exact raw Fourier PDE for every projected-RHS coordinate `R_i`.

Consequently the raw Fourier `L²` state of `R_i` is exactly the already-defined
terminal raw PDE RHS.  The generic Laplacian and Leray-forcing estimates give

    ‖R_i‖₂ ≤ ‖U‖ + C ‖U‖²,

with `C = 576 π * h3SobolevDeweightingConstant`.

Since `‖U‖ ≤ sqrt(E_H3)`, raw-`L²` escape forces physical H³-energy escape.
The fourth-temporal residual projected-RHS obstruction is therefore reduced to
only raw `L¹` or order-ten moment escape.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2400000

noncomputable local instance axisFintypeH3TerminalFourthQProjectedRHSRawL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQProjectedRHSRawL2 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Identify the chosen projected-RHS raw L² state with the canonical PDE RHS -/

theorem h3TerminalFourthQForcingDerivativeProjectedRHSRawL2_eq_rawPDERHS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i : Fin 3) :
    h3SpectralScalarRawFourierL2
        (
          (
            h3TerminalFourthQForcingDerivativeLerayDataAt
              hH3 hClass ht j
          ).R i
        )
      =
    h3TerminalPhysicalRawPDERHSFourierL2At
      hH3 hClass ht i := by

  let d :=
    h3TerminalFourthQForcingDerivativeLerayDataAt
      hH3 hClass ht j

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U :
      H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 t htAbs

  have hUTerm :
      d.U = U := by
    dsimp only [d, U, htAbs]
    exact
      h3TerminalFourthQForcingDerivativeLerayDataAt_U_eq_terminalVelocity
        hH3 hClass ht j

  have hChosen :
      (
        (
          h3SpectralScalarRawFourierL2 (d.R i) :
          H3FourierComplexL2
        ) :
        H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        -(h3FourierGradientSquare ξ : ℂ)
            *
          (
            (
              h3SpectralScalarRawFourierL2 (d.U i) :
              H3FourierComplexL2
            ) ξ
          )
          -
        h3RawFinLerayOuterProductDivergence
          d.U d.U i ξ) := by
    dsimp only [d]
    exact
      h3TerminalFourthQForcingDerivativeLerayDataAt_R_rawFourier_ae_eq_unitPDE
        hH3 hClass ht j i

  have hChosenU :
      (
        (
          h3SpectralScalarRawFourierL2 (d.R i) :
          H3FourierComplexL2
        ) :
        H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        -(h3FourierGradientSquare ξ : ℂ)
            *
          (
            (
              h3SpectralScalarRawFourierL2 (U i) :
              H3FourierComplexL2
            ) ξ
          )
          -
        h3RawFinLerayOuterProductDivergence
          U U i ξ) := by
    simpa only [hUTerm] using hChosen

  have hCanonical :
      (
        (
          h3TerminalPhysicalRawPDERHSFourierL2At
            hH3 hClass ht i :
          H3FourierComplexL2
        ) :
        H3FourierPoint3 → ℂ
      )
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        -(h3FourierGradientSquare ξ : ℂ)
            *
          (
            (
              h3SpectralScalarRawFourierL2 (U i) :
              H3FourierComplexL2
            ) ξ
          )
          -
        h3RawFinLerayOuterProductDivergence
          U U i ξ) := by

    dsimp only [U, htAbs]

    exact
      h3TerminalPhysicalRawPDERHSFourierL2At_ae_unitPDE
        hH3 hClass ht i

  apply MeasureTheory.Lp.ext

  filter_upwards [hChosenU, hCanonical]
    with ξ hChosenξ hCanonicalξ

  exact
    hChosenξ.trans
      hCanonicalξ.symm

theorem h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt_eq_rawPDERHS_norm
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i : Fin 3) :
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt
        hH3 hClass ht j i
      =
    ‖h3TerminalPhysicalRawPDERHSFourierL2At
      hH3 hClass ht i‖ := by

  unfold
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt

  dsimp only

  rw [
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL2_eq_rawPDERHS
      hH3 hClass ht j i
  ]

/-! ## Direct state-polynomial bound -/

theorem norm_h3TerminalPhysicalRawPDERHSFourierL2At_le_state_poly
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    ‖h3TerminalPhysicalRawPDERHSFourierL2At
        hH3 hClass ht i‖
      ≤
    ‖U‖
      +
    576 * Real.pi * h3SobolevDeweightingConstant
      * ‖U‖ * ‖U‖ := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let L : H3FourierComplexL2 :=
    h3SpectralScalarLaplacianRawFourierL2
      (U i)

  let F : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergenceFourierL2
      U U i

  have hLap :
      ‖L‖ ≤ ‖U‖ := by
    dsimp only [L]
    exact
      (norm_h3SpectralScalarLaplacianRawFourierL2_le
        (U i)).trans
        (h3SpectralFinVector_coordinate_norm_le U i)

  have hForce :
      ‖F‖
        ≤
      576 * Real.pi * h3SobolevDeweightingConstant
        * ‖U‖ * ‖U‖ := by
    dsimp only [F]
    exact
      norm_h3RawFinLerayOuterProductDivergenceFourierL2_le
        U U i

  unfold h3TerminalPhysicalRawPDERHSFourierL2At

  change
    ‖L - F‖
      ≤
    ‖U‖
      +
    576 * Real.pi * h3SobolevDeweightingConstant
      * ‖U‖ * ‖U‖

  exact
    (norm_sub_le L F).trans
      (add_le_add hLap hForce)

theorem h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt_le_state_poly
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i : Fin 3) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    let U :=
      h3TerminalVelocitySpectralStateAt hH3 t htAbs
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt
        hH3 hClass ht j i
      ≤
    ‖U‖
      +
    576 * Real.pi * h3SobolevDeweightingConstant
      * ‖U‖ * ‖U‖ := by

  dsimp only

  rw [
    h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt_eq_rawPDERHS_norm
      hH3 hClass ht j i
  ]

  exact
    norm_h3TerminalPhysicalRawPDERHSFourierL2At_le_state_poly
      hH3 hClass ht i

theorem norm_h3TerminalVelocitySpectralStateAt_le_sqrt_energy_for_fourthQProjectedRHS
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
    ‖h3TerminalVelocitySpectralStateAt hH3 t htAbs‖
      ≤
    Real.sqrt (velocityH3EnergyAt u t) := by

  dsimp only

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs

  let hMeas : VelocityH3MeasurableAt u t :=
    velocityH3MeasurableAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs

  let hFourier :
      VelocityH3FourierCompatibleAt u t hInt hMeas :=
    velocityH3FourierCompatibleAt_of_loggedPreterminalNavierStokes
      hH3.navier_stokes htAbs hInt

  unfold h3TerminalVelocitySpectralStateAt

  exact
    norm_velocityH3SpectralStateAt_le_sqrt_energy
      hFourier

/--
Escape of one chosen projected-RHS raw-`L²` coordinate forces physical H³
energy escape on the same sequence.
-/
theorem velocityH3EnergyAt_tendstoAtTop_of_h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j i : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hRawTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt
            hH3 hClass (hτ n) j i)
        atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        velocityH3EnergyAt u (τ n))
      atTop atTop := by

  refine tendsto_atTop.2 ?_

  intro M

  let R0 : ℝ :=
    max M 0

  let S0 : ℝ :=
    Real.sqrt R0

  let C : ℝ :=
    576 * Real.pi * h3SobolevDeweightingConstant

  let B : ℝ :=
    S0 + C * S0 * S0

  have hMLe :
      M ≤ R0 := by
    dsimp only [R0]
    exact le_max_left M 0

  have hR0 :
      0 ≤ R0 := by
    dsimp only [R0]
    exact le_max_right M 0

  have hS0 :
      0 ≤ S0 := by
    dsimp only [S0]
    exact Real.sqrt_nonneg R0

  have hC0 :
      0 ≤ C := by
    dsimp only [C]
    positivity [h3SobolevDeweightingConstant_nonneg]

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        B + 1
          <
        h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt
          hH3 hClass (hτ n) j i :=
    hRawTop.eventually
      (eventually_gt_atTop (B + 1))

  filter_upwards [hLarge] with n hn

  let htAbs :
      τ n ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 (hτ n).1,
      (hτ n).2
    ⟩

  let U :
      H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt
      hH3 (τ n) htAbs

  have hBound :
      h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt
          hH3 hClass (hτ n) j i
        ≤
      ‖U‖ + C * ‖U‖ * ‖U‖ := by

    dsimp only [U, C, htAbs]

    exact
      h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt_le_state_poly
        hH3 hClass (hτ n) j i

  have hState :
      ‖U‖
        ≤
      Real.sqrt
        (velocityH3EnergyAt u (τ n)) := by

    dsimp only [U, htAbs]

    exact
      norm_h3TerminalVelocitySpectralStateAt_le_sqrt_energy_for_fourthQProjectedRHS
        hH3 hClass (hτ n)

  have hEnergyGt :
      R0 < velocityH3EnergyAt u (τ n) := by

    by_contra hNot

    have hEnergyLe :
        velocityH3EnergyAt u (τ n) ≤ R0 :=
      le_of_not_gt hNot

    have hSqrtLe :
        Real.sqrt
            (velocityH3EnergyAt u (τ n))
          ≤
        S0 := by
      dsimp only [S0]
      exact
        Real.sqrt_le_sqrt
          hEnergyLe

    have hULe :
        ‖U‖ ≤ S0 :=
      hState.trans hSqrtLe

    have hUU :
        ‖U‖ * ‖U‖
          ≤
        S0 * S0 :=
      mul_le_mul
        hULe
        hULe
        (norm_nonneg U)
        hS0

    have hCUU :
        C * ‖U‖ * ‖U‖
          ≤
        C * S0 * S0 := by

      calc
        C * ‖U‖ * ‖U‖
            =
          C * (‖U‖ * ‖U‖) := by
            ring
        _ ≤
          C * (S0 * S0) :=
            mul_le_mul_of_nonneg_left
              hUU
              hC0
        _ =
          C * S0 * S0 := by
            ring

    have hPoly :
        ‖U‖ + C * ‖U‖ * ‖U‖
          ≤
        B := by
      dsimp only [B]
      exact
        add_le_add
          hULe
          hCUU

    have hRawLe :
        h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt
            hH3 hClass (hτ n) j i
          ≤
        B :=
      hBound.trans hPoly

    linarith

  exact
    hMLe.trans
      (le_of_lt hEnergyGt)

/-! ## Remove raw L² from the residual projected-RHS frontier -/

inductive H3TerminalFourthQForcingDerivativeProjectedRHSHighObstruction where
  | moment10
  | rawL1
  deriving DecidableEq, Repr

noncomputable def h3TerminalFourthQForcingDerivativeProjectedRHSHighObstructionAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (c : H3TerminalFourthQForcingDerivativeProjectedRHSHighObstruction)
    (i : Fin 3) : ℝ :=
  match c with
  | .moment10 =>
      h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
        hH3 hClass ht j i
  | .rawL1 =>
      h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
        hH3 hClass ht j i

/--
Fourth-temporal escape now reduces to physical H³ energy, one fixed nonzero
extended higher-radial moment, or one fixed projected-RHS high primitive:
order-ten moment or raw `L¹`.
-/
theorem fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_fixedProjectedRHSHighPrimitive
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hFourth :
      Tendsto
        (fun n : ℕ =>
          h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
            hH3 hClass j
            H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
            (τ n))
        atTop atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n) ∧
        Tendsto s atTop atTop ∧
        Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
        Tendsto
          (fun n : ℕ => velocityH3EnergyAt u (τ (s n)))
          atTop atTop
    )
      ∨
    (
      ∃ m : ℕ,
        m ≠ 0 ∧
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n) ∧
          Tendsto s atTop atTop ∧
          Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
          Tendsto
            (fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass m
                (τ (s n))
                (hτ (s n)))
            atTop (𝓝 ∞)
    )
      ∨
    (
      ∃ c : H3TerminalFourthQForcingDerivativeProjectedRHSHighObstruction,
        ∃ i : Fin 3,
          ∃ s : ℕ → ℕ,
            (∀ n : ℕ, n ≤ s n) ∧
            Tendsto s atTop atTop ∧
            Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
            Tendsto
              (fun n : ℕ =>
                h3TerminalFourthQForcingDerivativeProjectedRHSHighObstructionAt
                  hH3 hClass (hτ (s n)) j c i)
              atTop atTop
    ) := by

  rcases
    fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_fixedProjectedRHSPrimitive
      hH3 hClass j τ hτ hTauTendsto hFourth
  with hEnergy | hRest

  · exact Or.inl hEnergy

  · rcases hRest with hHigher | hRHS

    · exact Or.inr (Or.inl hHigher)

    · rcases hRHS with
        ⟨c, i, s, hs, hsTop, hTauSub, hPrimitiveTop⟩

      cases c with

      | rawL2 =>

          have hRawTop :
              Tendsto
                (fun n : ℕ =>
                  h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt
                    hH3 hClass (hτ (s n)) j i)
                atTop atTop := by

            simpa [
              h3TerminalFourthQForcingDerivativeProjectedRHSObstructionAt
            ] using hPrimitiveTop

          have hEnergyTop :=
            velocityH3EnergyAt_tendstoAtTop_of_h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt_tendstoAtTop
              hH3 hClass j i
              (fun n : ℕ => τ (s n))
              (fun n : ℕ => hτ (s n))
              hRawTop

          exact
            Or.inl
              ⟨
                s,
                hs,
                hsTop,
                hTauSub,
                hEnergyTop
              ⟩

      | moment10 =>

          exact
            Or.inr
              (
                Or.inr
                  ⟨
                    .moment10,
                    i,
                    s,
                    hs,
                    hsTop,
                    hTauSub,
                    by
                      simpa [
                        h3TerminalFourthQForcingDerivativeProjectedRHSObstructionAt,
                        h3TerminalFourthQForcingDerivativeProjectedRHSHighObstructionAt
                      ] using hPrimitiveTop
                  ⟩
              )

      | rawL1 =>

          exact
            Or.inr
              (
                Or.inr
                  ⟨
                    .rawL1,
                    i,
                    s,
                    hs,
                    hsTop,
                    hTauSub,
                    by
                      simpa [
                        h3TerminalFourthQForcingDerivativeProjectedRHSObstructionAt,
                        h3TerminalFourthQForcingDerivativeProjectedRHSHighObstructionAt
                      ] using hPrimitiveTop
                  ⟩
              )

end

end Euclidean
end Bridge
end PrimeTensor
