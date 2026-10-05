import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Higher.Subtail.StateMass.Group.Factor.Primitive
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Mass.Higher.Moment.Forcing.Escape.Pair.Bound.Group.Factor.Primitive.Low.Classify

/-!
# Classify fourth-q forcing derivative primitive masses by state origin

The chosen product-rule datum now records that its `U` slot is exactly the
terminal physical velocity state.  Hence velocity-side raw `L²` escape is
excluded by the kinetic tail bound and velocity-side raw `L¹` escape is
absorbed into physical H³-energy escape.

The residual primitive obstructions are:
* one terminal velocity order-ten moment;
* projected-RHS raw `L²`;
* projected-RHS order-ten moment;
* projected-RHS raw `L¹`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2400000

noncomputable local instance axisFintypeH3TerminalFourthQForcingPrimitiveOrigin
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQForcingPrimitiveOrigin :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

noncomputable def h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (i : Fin 3) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U := h3TerminalVelocitySpectralStateAt hH3 t htAbs
  h3SpectralScalarRawFourierMomentMass (10 : ℝ) (U i)

noncomputable def h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i : Fin 3) : ℝ :=
  let d := h3TerminalFourthQForcingDerivativeLerayDataAt hH3 hClass ht j
  ‖h3SpectralScalarRawFourierL2 (d.R i)‖

noncomputable def h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i : Fin 3) : ℝ :=
  let d := h3TerminalFourthQForcingDerivativeLerayDataAt hH3 hClass ht j
  h3SpectralScalarRawFourierMomentMass (10 : ℝ) (d.R i)

noncomputable def h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j i : Fin 3) : ℝ :=
  let d := h3TerminalFourthQForcingDerivativeLerayDataAt hH3 hClass ht j
  h3SpectralScalarRawFourierL1Mass (d.R i)

inductive H3TerminalFourthQForcingDerivativePrimitiveObstruction where
  | velocityMoment10
  | projectedRHSRawL2
  | projectedRHSMoment10
  | projectedRHSRawL1
  deriving DecidableEq, Repr

noncomputable def h3TerminalFourthQForcingDerivativePrimitiveObstructionAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (c : H3TerminalFourthQForcingDerivativePrimitiveObstruction)
    (i : Fin 3) : ℝ :=
  match c with
  | .velocityMoment10 =>
      h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt
        hH3 hClass ht i
  | .projectedRHSRawL2 =>
      h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt
        hH3 hClass ht j i
  | .projectedRHSMoment10 =>
      h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
        hH3 hClass ht j i
  | .projectedRHSRawL1 =>
      h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
        hH3 hClass ht j i

theorem fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_fixedForcingDerivativePrimitiveObstruction
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
        Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ (s n))) atTop atTop
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
                hH3 hClass m (τ (s n)) (hτ (s n)))
            atTop (𝓝 ∞)
    )
      ∨
    (
      ∃ c : H3TerminalFourthQForcingDerivativePrimitiveObstruction,
        ∃ i : Fin 3,
          ∃ s : ℕ → ℕ,
            (∀ n : ℕ, n ≤ s n) ∧
            Tendsto s atTop atTop ∧
            Tendsto (fun n : ℕ => τ (s n)) atTop (𝓝 T) ∧
            Tendsto
              (fun n : ℕ =>
                h3TerminalFourthQForcingDerivativePrimitiveObstructionAt
                  hH3 hClass (hτ (s n)) j c i)
              atTop atTop
    ) := by

  rcases
    fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_fixedForcingDerivativePrimitiveMass
      hH3 hClass j τ hτ hTauTendsto hFourth
  with hEnergy | hRest

  · exact Or.inl hEnergy

  · rcases hRest with hHigher | hPrimitive
    · exact Or.inr (Or.inl hHigher)
    · rcases hPrimitive with ⟨o, k, l, hRaw | hMoment⟩

      · rcases hRaw with ⟨r, s, hs, hsTop, hTauSub, hRawTop⟩
        fin_cases o <;> fin_cases r

        · exact Or.inr (Or.inr
            ⟨.projectedRHSRawL2, k, s, hs, hsTop, hTauSub, by
              simpa [
                h3TerminalFourthQForcingDerivativeRawL2FactorAt,
                h3TerminalFourthQForcingDerivativeFirstStateAt,
                h3TerminalFourthQForcingDerivativeSecondStateAt,
                h3TerminalFourthQForcingDerivativePrimitiveObstructionAt,
                h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt,
                norm_h3SpectralScalarRawFourierConjL2_eq_rawFourierL2
              ] using hRawTop⟩)

        · have hOldTop :
              Tendsto
                (fun n : ℕ =>
                  h3TerminalForcingThirdQRawL2FactorAt
                    hH3 hClass (hτ (s n)) k l 1)
                atTop atTop := by
            simpa [
              h3TerminalFourthQForcingDerivativeRawL2FactorAt,
              h3TerminalFourthQForcingDerivativeFirstStateAt,
              h3TerminalFourthQForcingDerivativeSecondStateAt,
              h3TerminalForcingThirdQRawL2FactorAt,
              h3TerminalFourthQForcingDerivativeLerayDataAt_U_eq_terminalVelocity
            ] using hRawTop
          have hNot :=
            not_h3TerminalForcingThirdQRawL2FactorAt_tendstoAtTop
              hH3 hClass k l 1
              (fun n : ℕ => τ (s n))
              (fun n : ℕ => hτ (s n))
              hTauSub
          exact False.elim (hNot hOldTop)

        · have hOldTop :
              Tendsto
                (fun n : ℕ =>
                  h3TerminalForcingThirdQRawL2FactorAt
                    hH3 hClass (hτ (s n)) k l 0)
                atTop atTop := by
            simpa [
              h3TerminalFourthQForcingDerivativeRawL2FactorAt,
              h3TerminalFourthQForcingDerivativeFirstStateAt,
              h3TerminalFourthQForcingDerivativeSecondStateAt,
              h3TerminalForcingThirdQRawL2FactorAt,
              h3TerminalFourthQForcingDerivativeLerayDataAt_U_eq_terminalVelocity
            ] using hRawTop
          have hNot :=
            not_h3TerminalForcingThirdQRawL2FactorAt_tendstoAtTop
              hH3 hClass k l 0
              (fun n : ℕ => τ (s n))
              (fun n : ℕ => hτ (s n))
              hTauSub
          exact False.elim (hNot hOldTop)

        · exact Or.inr (Or.inr
            ⟨.projectedRHSRawL2, l, s, hs, hsTop, hTauSub, by
              simpa [
                h3TerminalFourthQForcingDerivativeRawL2FactorAt,
                h3TerminalFourthQForcingDerivativeFirstStateAt,
                h3TerminalFourthQForcingDerivativeSecondStateAt,
                h3TerminalFourthQForcingDerivativePrimitiveObstructionAt,
                h3TerminalFourthQForcingDerivativeProjectedRHSRawL2MassAt
              ] using hRawTop⟩)

      · rcases hMoment with
          ⟨r, q, s, hs, hsTop, hTauSub, hPrimitiveTop⟩
        fin_cases o <;> fin_cases r <;> fin_cases q

        · exact Or.inr (Or.inr
            ⟨.projectedRHSMoment10, k, s, hs, hsTop, hTauSub, by
              simpa [
                h3TerminalFourthQForcingDerivativeMomentL1PrimitiveAt,
                h3TerminalFourthQForcingDerivativeFirstStateAt,
                h3TerminalFourthQForcingDerivativeSecondStateAt,
                h3TerminalFourthQForcingDerivativePrimitiveObstructionAt,
                h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
              ] using hPrimitiveTop⟩)

        · have hL1Top :
              Tendsto
                (fun n : ℕ =>
                  h3TerminalForcingThirdQRawL1MassAt
                    hH3 hClass (hτ (s n)) l)
                atTop atTop := by
            simpa [
              h3TerminalFourthQForcingDerivativeMomentL1PrimitiveAt,
              h3TerminalFourthQForcingDerivativeFirstStateAt,
              h3TerminalFourthQForcingDerivativeSecondStateAt,
              h3TerminalForcingThirdQRawL1MassAt,
              h3TerminalFourthQForcingDerivativeLerayDataAt_U_eq_terminalVelocity
            ] using hPrimitiveTop
          have hEnergyTop :=
            velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingThirdQRawL1MassAt_tendstoAtTop
              hH3 hClass l
              (fun n : ℕ => τ (s n))
              (fun n : ℕ => hτ (s n))
              hL1Top
          exact Or.inl ⟨s, hs, hsTop, hTauSub, hEnergyTop⟩

        · exact Or.inr (Or.inr
            ⟨.projectedRHSRawL1, k, s, hs, hsTop, hTauSub, by
              simpa [
                h3TerminalFourthQForcingDerivativeMomentL1PrimitiveAt,
                h3TerminalFourthQForcingDerivativeFirstStateAt,
                h3TerminalFourthQForcingDerivativeSecondStateAt,
                h3TerminalFourthQForcingDerivativePrimitiveObstructionAt,
                h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
              ] using hPrimitiveTop⟩)

        · exact Or.inr (Or.inr
            ⟨.velocityMoment10, l, s, hs, hsTop, hTauSub, by
              simpa [
                h3TerminalFourthQForcingDerivativeMomentL1PrimitiveAt,
                h3TerminalFourthQForcingDerivativeFirstStateAt,
                h3TerminalFourthQForcingDerivativeSecondStateAt,
                h3TerminalFourthQForcingDerivativePrimitiveObstructionAt,
                h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt,
                h3TerminalFourthQForcingDerivativeLerayDataAt_U_eq_terminalVelocity
              ] using hPrimitiveTop⟩)

        · exact Or.inr (Or.inr
            ⟨.velocityMoment10, k, s, hs, hsTop, hTauSub, by
              simpa [
                h3TerminalFourthQForcingDerivativeMomentL1PrimitiveAt,
                h3TerminalFourthQForcingDerivativeFirstStateAt,
                h3TerminalFourthQForcingDerivativeSecondStateAt,
                h3TerminalFourthQForcingDerivativePrimitiveObstructionAt,
                h3TerminalFourthQForcingDerivativeVelocityMoment10MassAt,
                h3TerminalFourthQForcingDerivativeLerayDataAt_U_eq_terminalVelocity
              ] using hPrimitiveTop⟩)

        · exact Or.inr (Or.inr
            ⟨.projectedRHSRawL1, l, s, hs, hsTop, hTauSub, by
              simpa [
                h3TerminalFourthQForcingDerivativeMomentL1PrimitiveAt,
                h3TerminalFourthQForcingDerivativeFirstStateAt,
                h3TerminalFourthQForcingDerivativeSecondStateAt,
                h3TerminalFourthQForcingDerivativePrimitiveObstructionAt,
                h3TerminalFourthQForcingDerivativeProjectedRHSRawL1MassAt
              ] using hPrimitiveTop⟩)

        · have hL1Top :
              Tendsto
                (fun n : ℕ =>
                  h3TerminalForcingThirdQRawL1MassAt
                    hH3 hClass (hτ (s n)) k)
                atTop atTop := by
            simpa [
              h3TerminalFourthQForcingDerivativeMomentL1PrimitiveAt,
              h3TerminalFourthQForcingDerivativeFirstStateAt,
              h3TerminalFourthQForcingDerivativeSecondStateAt,
              h3TerminalForcingThirdQRawL1MassAt,
              h3TerminalFourthQForcingDerivativeLerayDataAt_U_eq_terminalVelocity
            ] using hPrimitiveTop
          have hEnergyTop :=
            velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingThirdQRawL1MassAt_tendstoAtTop
              hH3 hClass k
              (fun n : ℕ => τ (s n))
              (fun n : ℕ => hτ (s n))
              hL1Top
          exact Or.inl ⟨s, hs, hsTop, hTauSub, hEnergyTop⟩

        · exact Or.inr (Or.inr
            ⟨.projectedRHSMoment10, l, s, hs, hsTop, hTauSub, by
              simpa [
                h3TerminalFourthQForcingDerivativeMomentL1PrimitiveAt,
                h3TerminalFourthQForcingDerivativeFirstStateAt,
                h3TerminalFourthQForcingDerivativeSecondStateAt,
                h3TerminalFourthQForcingDerivativePrimitiveObstructionAt,
                h3TerminalFourthQForcingDerivativeProjectedRHSMoment10MassAt
              ] using hPrimitiveTop⟩)

end

end Euclidean
end Bridge
end PrimeTensor
