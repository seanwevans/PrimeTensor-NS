import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Vorticity.Energy.Envelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.Third.Variation.Zero.Envelope

/-!
# Classify the surviving primitive third-q forcing masses

After excluding primitive raw Fourier `L²` escape, the forcing side contains
only the four cases of the `Fin 2 × Fin 2` moment/`L¹` primitive package.

The diagonal cases are exactly order-fourteen raw Fourier moment masses.
The off-diagonal cases are exactly raw Fourier `L¹` masses.

Raw `L¹` is not an independent high-frequency obstruction: deweighting bounds
it by a fixed coefficient times the weighted H³ spectral norm, and the latter
is bounded by the square root of the physical H³ energy.  Hence raw-`L¹`
escape forces ordinary H³-energy escape.

Thus the sixth-diffusion frontier reduces to three transparent alternatives:

* the existing shift-four extended higher-radial moment;
* physical H³-energy escape;
* one fixed order-fourteen raw Fourier moment mass.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3TerminalThirdQPrimitiveClassify
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalThirdQPrimitiveClassify :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Named primitive masses -/

/-- One terminal order-fourteen raw Fourier moment mass. -/
noncomputable def h3TerminalForcingThirdQMoment14MassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  h3SpectralScalarRawFourierMomentMass (14 : ℝ) (U j)

/-- One terminal raw Fourier `L¹` mass. -/
noncomputable def h3TerminalForcingThirdQRawL1MassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  h3SpectralScalarRawFourierL1Mass (U j)

theorem h3TerminalForcingThirdQMoment14MassAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    0 ≤
      h3TerminalForcingThirdQMoment14MassAt
        hH3 hClass ht j := by

  unfold h3TerminalForcingThirdQMoment14MassAt
  dsimp only

  exact
    h3SpectralScalarRawFourierMomentMass_nonneg
      (14 : ℝ) _

theorem h3TerminalForcingThirdQRawL1MassAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    0 ≤
      h3TerminalForcingThirdQRawL1MassAt
        hH3 hClass ht j := by

  unfold h3TerminalForcingThirdQRawL1MassAt
  dsimp only

  exact
    h3SpectralScalarRawFourierL1Mass_nonneg _

/-! ## Raw L¹ is controlled by physical H³ energy -/

/--
Every terminal raw Fourier `L¹` component is bounded by the fixed deweighting
coefficient times the square root of the physical H³ energy.
-/
theorem h3TerminalForcingThirdQRawL1MassAt_le_deweight_sqrt_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalForcingThirdQRawL1MassAt
        hH3 hClass ht j
      ≤
    h3RawFourierL1DeweightingCoefficient
      *
    Real.sqrt (velocityH3EnergyAt u t) := by

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

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  have hRaw :
      h3SpectralScalarRawFourierL1Mass (U j)
        ≤
      h3RawFourierL1DeweightingCoefficient * ‖U j‖ :=
    h3SpectralScalarRawFourierL1Mass_le_norm
      (U j)

  have hCoord :
      ‖U j‖ ≤ ‖U‖ :=
    h3SpectralFinVector_coordinate_norm_le
      U j

  have hState :
      ‖U‖
        ≤
      Real.sqrt (velocityH3EnergyAt u t) := by

    dsimp only [U]

    unfold h3TerminalVelocitySpectralStateAt

    exact
      norm_velocityH3SpectralStateAt_le_sqrt_energy
        hFourier

  have hCoeff0 :
      0 ≤ h3RawFourierL1DeweightingCoefficient :=
    h3RawFourierL1DeweightingCoefficient_nonneg

  unfold h3TerminalForcingThirdQRawL1MassAt
  dsimp only

  calc
    h3SpectralScalarRawFourierL1Mass (U j)
        ≤
      h3RawFourierL1DeweightingCoefficient * ‖U j‖ :=
      hRaw
    _ ≤
      h3RawFourierL1DeweightingCoefficient * ‖U‖ :=
      mul_le_mul_of_nonneg_left hCoord hCoeff0
    _ ≤
      h3RawFourierL1DeweightingCoefficient
        *
      Real.sqrt (velocityH3EnergyAt u t) :=
      mul_le_mul_of_nonneg_left hState hCoeff0

/--
Divergence of a fixed terminal raw Fourier `L¹` component forces divergence of
the physical H³ energy on the same terminal sequence.
-/
theorem velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingThirdQRawL1MassAt_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hL1Top :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQRawL1MassAt
              hH3 hClass (hτ n) j
        )
        atTop
        atTop) :
    Tendsto
      (fun n : ℕ => velocityH3EnergyAt u (τ n))
      atTop
      atTop := by

  refine tendsto_atTop.2 ?_

  intro M

  let R : ℝ :=
    max M 0

  have hMLe :
      M ≤ R := by
    dsimp only [R]
    exact le_max_left M 0

  have hR0 :
      0 ≤ R := by
    dsimp only [R]
    exact le_max_right M 0

  let C : ℝ :=
    h3RawFourierL1DeweightingCoefficient

  have hC0 :
      0 ≤ C := by
    dsimp only [C]
    exact
      h3RawFourierL1DeweightingCoefficient_nonneg

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        C * Real.sqrt R + 1
          <
        h3TerminalForcingThirdQRawL1MassAt
          hH3 hClass (hτ n) j :=
    hL1Top.eventually
      (eventually_gt_atTop
        (C * Real.sqrt R + 1))

  filter_upwards [hLarge] with n hn

  have hBound :
      h3TerminalForcingThirdQRawL1MassAt
          hH3 hClass (hτ n) j
        ≤
      C * Real.sqrt (velocityH3EnergyAt u (τ n)) := by

    dsimp only [C]

    exact
      h3TerminalForcingThirdQRawL1MassAt_le_deweight_sqrt_energy
        hH3 hClass (hτ n) j

  have hEnergyGt :
      R < velocityH3EnergyAt u (τ n) := by

    by_contra hNot

    have hEnergyLe :
        velocityH3EnergyAt u (τ n) ≤ R :=
      le_of_not_gt hNot

    have hSqrtLe :
        Real.sqrt (velocityH3EnergyAt u (τ n))
          ≤
        Real.sqrt R :=
      Real.sqrt_le_sqrt
        hEnergyLe

    have hScaled :
        C * Real.sqrt (velocityH3EnergyAt u (τ n))
          ≤
        C * Real.sqrt R :=
      mul_le_mul_of_nonneg_left
        hSqrtLe
        hC0

    have hPrimitiveLe :
        h3TerminalForcingThirdQRawL1MassAt
            hH3 hClass (hτ n) j
          ≤
        C * Real.sqrt R :=
      hBound.trans hScaled

    linarith

  exact
    hMLe.trans
      (le_of_lt hEnergyGt)

/-! ## Identify the four primitive cases -/

theorem h3TerminalForcingThirdQMomentL1PrimitiveAt_zero_zero
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    h3TerminalForcingThirdQMomentL1PrimitiveAt
        hH3 hClass ht k l 0 0
      =
    h3TerminalForcingThirdQMoment14MassAt
      hH3 hClass ht k := by

  rfl

theorem h3TerminalForcingThirdQMomentL1PrimitiveAt_zero_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    h3TerminalForcingThirdQMomentL1PrimitiveAt
        hH3 hClass ht k l 0 1
      =
    h3TerminalForcingThirdQRawL1MassAt
      hH3 hClass ht l := by

  rfl

theorem h3TerminalForcingThirdQMomentL1PrimitiveAt_one_zero
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    h3TerminalForcingThirdQMomentL1PrimitiveAt
        hH3 hClass ht k l 1 0
      =
    h3TerminalForcingThirdQRawL1MassAt
      hH3 hClass ht k := by

  rfl

theorem h3TerminalForcingThirdQMomentL1PrimitiveAt_one_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    h3TerminalForcingThirdQMomentL1PrimitiveAt
        hH3 hClass ht k l 1 1
      =
    h3TerminalForcingThirdQMoment14MassAt
      hH3 hClass ht l := by

  rfl

/-! ## Classified sixth-diffusion frontier -/

/--
The forcing-side primitive alternatives are now classified completely:
off-diagonal raw-`L¹` escape is absorbed into physical H³-energy escape, while
the diagonal alternatives are fixed order-fourteen raw Fourier moment masses.
-/
theorem sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_energy_or_fixedMoment14
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hTauTendsto :
      Tendsto τ atTop (𝓝 T))
    (hSixth :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.sixthDiffusion
              (τ n)
        )
        atTop
        atTop) :
    (
      ∃ s : ℕ → ℕ,
        (∀ n : ℕ, n ≤ s n)
          ∧
        Tendsto s atTop atTop
          ∧
        Tendsto
          (fun n : ℕ => τ (s n))
          atTop
          (𝓝 T)
          ∧
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalPhysicalExtendedHigherRadialMomentAt
                hH3 hClass 4
                (τ (s n))
                (hτ (s n))
          )
          atTop
          (𝓝 ∞)
    )
      ∨
    (
      (
        ∃ s : ℕ → ℕ,
          (∀ n : ℕ, n ≤ s n)
            ∧
          Tendsto s atTop atTop
            ∧
          Tendsto
            (fun n : ℕ => τ (s n))
            atTop
            (𝓝 T)
            ∧
          Tendsto
            (fun n : ℕ =>
              velocityH3EnergyAt u (τ (s n)))
            atTop
            atTop
      )
        ∨
      (
        ∃ m : Fin 3,
          ∃ s : ℕ → ℕ,
            (∀ n : ℕ, n ≤ s n)
              ∧
            Tendsto s atTop atTop
              ∧
            Tendsto
              (fun n : ℕ => τ (s n))
              atTop
              (𝓝 T)
              ∧
            Tendsto
              (
                fun n : ℕ =>
                  h3TerminalForcingThirdQMoment14MassAt
                    hH3 hClass (hτ (s n)) m
              )
              atTop
              atTop
      )
    ) := by

  rcases
    sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_fixedForcingMomentL1Primitive
      hH3 hClass j τ hτ hTauTendsto hSixth
  with
    hHigher
    |
    hPrimitive

  · exact
      Or.inl hHigher

  · rcases hPrimitive with
      ⟨k, l, r, q, s, hs, hsTop, hTauSub, hPrimitiveTop⟩

    fin_cases r <;> fin_cases q

    · exact
        Or.inr
          (
            Or.inr
              ⟨
                k,
                s,
                hs,
                hsTop,
                hTauSub,
                by
                  simpa [
                    h3TerminalForcingThirdQMomentL1PrimitiveAt,
                    h3TerminalForcingThirdQMoment14MassAt
                  ] using hPrimitiveTop
              ⟩
          )

    · have hL1Top :
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingThirdQRawL1MassAt
                  hH3 hClass (hτ (s n)) l
            )
            atTop
            atTop := by
        simpa [
          h3TerminalForcingThirdQMomentL1PrimitiveAt,
          h3TerminalForcingThirdQRawL1MassAt
        ] using hPrimitiveTop

      have hEnergyTop :
          Tendsto
            (fun n : ℕ =>
              velocityH3EnergyAt u (τ (s n)))
            atTop
            atTop :=
        velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingThirdQRawL1MassAt_tendstoAtTop
          hH3 hClass l
          (fun n : ℕ => τ (s n))
          (fun n : ℕ => hτ (s n))
          hL1Top

      exact
        Or.inr
          (
            Or.inl
              ⟨
                s,
                hs,
                hsTop,
                hTauSub,
                hEnergyTop
              ⟩
          )

    · have hL1Top :
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingThirdQRawL1MassAt
                  hH3 hClass (hτ (s n)) k
            )
            atTop
            atTop := by
        simpa [
          h3TerminalForcingThirdQMomentL1PrimitiveAt,
          h3TerminalForcingThirdQRawL1MassAt
        ] using hPrimitiveTop

      have hEnergyTop :
          Tendsto
            (fun n : ℕ =>
              velocityH3EnergyAt u (τ (s n)))
            atTop
            atTop :=
        velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingThirdQRawL1MassAt_tendstoAtTop
          hH3 hClass k
          (fun n : ℕ => τ (s n))
          (fun n : ℕ => hτ (s n))
          hL1Top

      exact
        Or.inr
          (
            Or.inl
              ⟨
                s,
                hs,
                hsTop,
                hTauSub,
                hEnergyTop
              ⟩
          )

    · exact
        Or.inr
          (
            Or.inr
              ⟨
                l,
                s,
                hs,
                hsTop,
                hTauSub,
                by
                  simpa [
                    h3TerminalForcingThirdQMomentL1PrimitiveAt,
                    h3TerminalForcingThirdQMoment14MassAt
                  ] using hPrimitiveTop
              ⟩
          )

end

end Euclidean
end Bridge
end PrimeTensor
