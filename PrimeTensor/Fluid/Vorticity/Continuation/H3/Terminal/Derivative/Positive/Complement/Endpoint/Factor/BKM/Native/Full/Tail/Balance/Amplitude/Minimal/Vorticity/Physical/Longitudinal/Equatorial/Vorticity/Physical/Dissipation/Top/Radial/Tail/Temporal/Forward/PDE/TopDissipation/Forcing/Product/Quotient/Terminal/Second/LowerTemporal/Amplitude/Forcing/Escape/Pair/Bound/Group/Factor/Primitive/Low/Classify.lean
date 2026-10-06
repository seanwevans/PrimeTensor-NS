import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify

/-!
# Classify the surviving primitive fourth-q forcing masses

After excluding primitive raw Fourier `L²` escape, the fourth-q forcing side
contains only the four cases of the `Fin 2 × Fin 2` moment/`L¹` primitive
package.

The diagonal cases are exactly order-ten raw Fourier moment masses.  The
off-diagonal cases are raw Fourier `L¹` masses.

Raw `L¹` is controlled by the same fixed deweighting coefficient times the
square root of the physical H³ energy used in the third-q branch.  Hence
raw-`L¹` escape forces ordinary H³-energy escape.

Thus the fourth-temporal frontier reduces to three transparent alternatives:

* the existing shift-two extended higher-radial moment;
* physical H³-energy escape;
* one fixed order-ten raw Fourier moment mass.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3TerminalFourthQPrimitiveClassify
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQPrimitiveClassify :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Named primitive masses -/

/-- One terminal order-ten raw Fourier moment mass. -/
noncomputable def h3TerminalForcingFourthQMoment10MassAt
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
  h3SpectralScalarRawFourierMomentMass (10 : ℝ) (U j)

/-- One terminal raw Fourier `L¹` mass. -/
noncomputable def h3TerminalForcingFourthQRawL1MassAt
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

theorem h3TerminalForcingFourthQMoment10MassAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    0 ≤
      h3TerminalForcingFourthQMoment10MassAt
        hH3 hClass ht j := by

  unfold h3TerminalForcingFourthQMoment10MassAt
  dsimp only

  exact
    h3SpectralScalarRawFourierMomentMass_nonneg
      (10 : ℝ) _

theorem h3TerminalForcingFourthQRawL1MassAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    0 ≤
      h3TerminalForcingFourthQRawL1MassAt
        hH3 hClass ht j := by

  unfold h3TerminalForcingFourthQRawL1MassAt
  dsimp only

  exact
    h3SpectralScalarRawFourierL1Mass_nonneg _

/-! ## Raw L¹ is controlled by physical H³ energy -/

/--
Every terminal fourth-q raw Fourier `L¹` component is bounded by the fixed
deweighting coefficient times the square root of physical H³ energy.
-/
theorem h3TerminalForcingFourthQRawL1MassAt_le_deweight_sqrt_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalForcingFourthQRawL1MassAt
        hH3 hClass ht j
      ≤
    h3RawFourierL1DeweightingCoefficient
      *
    Real.sqrt (velocityH3EnergyAt u t) := by

  simpa [
    h3TerminalForcingFourthQRawL1MassAt,
    h3TerminalForcingThirdQRawL1MassAt
  ] using
    h3TerminalForcingThirdQRawL1MassAt_le_deweight_sqrt_energy
      hH3 hClass ht j

/--
Divergence of a fixed terminal fourth-q raw Fourier `L¹` component forces
divergence of physical H³ energy on the same terminal sequence.
-/
theorem velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingFourthQRawL1MassAt_tendstoAtTop
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
            h3TerminalForcingFourthQRawL1MassAt
              hH3 hClass (hτ n) j
        )
        atTop
        atTop) :
    Tendsto
      (fun n : ℕ => velocityH3EnergyAt u (τ n))
      atTop
      atTop := by

  have hThirdTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingThirdQRawL1MassAt
              hH3 hClass (hτ n) j
        )
        atTop
        atTop := by
    simpa [
      h3TerminalForcingFourthQRawL1MassAt,
      h3TerminalForcingThirdQRawL1MassAt
    ] using hL1Top

  exact
    velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingThirdQRawL1MassAt_tendstoAtTop
      hH3 hClass j τ hτ hThirdTop

/-! ## Identify the four primitive cases -/

theorem h3TerminalForcingFourthQMomentL1PrimitiveAt_zero_zero
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    h3TerminalForcingFourthQMomentL1PrimitiveAt
        hH3 hClass ht k l 0 0
      =
    h3TerminalForcingFourthQMoment10MassAt
      hH3 hClass ht k := by
  rfl

theorem h3TerminalForcingFourthQMomentL1PrimitiveAt_zero_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    h3TerminalForcingFourthQMomentL1PrimitiveAt
        hH3 hClass ht k l 0 1
      =
    h3TerminalForcingFourthQRawL1MassAt
      hH3 hClass ht l := by
  rfl

theorem h3TerminalForcingFourthQMomentL1PrimitiveAt_one_zero
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    h3TerminalForcingFourthQMomentL1PrimitiveAt
        hH3 hClass ht k l 1 0
      =
    h3TerminalForcingFourthQRawL1MassAt
      hH3 hClass ht k := by
  rfl

theorem h3TerminalForcingFourthQMomentL1PrimitiveAt_one_one
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    h3TerminalForcingFourthQMomentL1PrimitiveAt
        hH3 hClass ht k l 1 1
      =
    h3TerminalForcingFourthQMoment10MassAt
      hH3 hClass ht l := by
  rfl

/-! ## Classified fourth-temporal frontier -/

/--
The fourth-q forcing primitive alternatives are classified completely:
off-diagonal raw-`L¹` escape is absorbed into physical H³-energy escape, while
the diagonal alternatives are fixed order-ten raw Fourier moment masses.
-/
theorem fourthTemporal_amplitude_escape_extendedHigherTwo_or_energy_or_fixedMoment10
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
    (hAmplitudeTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelAmplitude
              hH3 hClass j
              H3TerminalResolvedPhysicalPDEChannel.fourthTemporal
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
                hH3 hClass 2
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
                  h3TerminalForcingFourthQMoment10MassAt
                    hH3 hClass (hτ (s n)) m
              )
              atTop
              atTop
      )
    ) := by

  rcases
    fourthTemporal_amplitude_escape_extendedHigherTwo_or_fixedForcingMomentL1Primitive
      hH3 hClass j τ hτ hTauTendsto hAmplitudeTop
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
                    h3TerminalForcingFourthQMomentL1PrimitiveAt,
                    h3TerminalForcingFourthQMoment10MassAt
                  ] using hPrimitiveTop
              ⟩
          )

    · have hL1Top :
          Tendsto
            (
              fun n : ℕ =>
                h3TerminalForcingFourthQRawL1MassAt
                  hH3 hClass (hτ (s n)) l
            )
            atTop
            atTop := by
        simpa [
          h3TerminalForcingFourthQMomentL1PrimitiveAt,
          h3TerminalForcingFourthQRawL1MassAt
        ] using hPrimitiveTop

      have hEnergyTop :
          Tendsto
            (fun n : ℕ =>
              velocityH3EnergyAt u (τ (s n)))
            atTop
            atTop :=
        velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingFourthQRawL1MassAt_tendstoAtTop
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
                h3TerminalForcingFourthQRawL1MassAt
                  hH3 hClass (hτ (s n)) k
            )
            atTop
            atTop := by
        simpa [
          h3TerminalForcingFourthQMomentL1PrimitiveAt,
          h3TerminalForcingFourthQRawL1MassAt
        ] using hPrimitiveTop

      have hEnergyTop :
          Tendsto
            (fun n : ℕ =>
              velocityH3EnergyAt u (τ (s n)))
            atTop
            atTop :=
        velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingFourthQRawL1MassAt_tendstoAtTop
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
                    h3TerminalForcingFourthQMomentL1PrimitiveAt,
                    h3TerminalForcingFourthQMoment10MassAt
                  ] using hPrimitiveTop
              ⟩
          )

end

end Euclidean
end Bridge
end PrimeTensor
