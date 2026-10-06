import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.SecondQ.Escape.StateMass.Primitive
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.Closure

/-!
# Classify second-q forcing-state primitive escape

The second-q forcing-state Young envelope has been reduced to one of six fixed
velocity primitives.  These six cases are already covered by existing terminal
estimates:

* raw `L²` escape is impossible by the terminal kinetic-energy bound;
* raw `L¹` escape forces physical H³-energy escape;
* moment-six escape is handled by the existing second-q velocity moment-six
  resolver, yielding physical H³-energy escape or escape of one fixed nonzero
  extended higher-radial moment.

Thus the complete second-q forcing-state mass escape is reduced to the same
two physical alternatives.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2600000

/--
Every fixed primitive factor of the second-q forcing-state envelope either
cannot escape, or reduces to physical H³-energy escape or one fixed nonzero
extended higher-radial escape.
-/
theorem h3TerminalForcingSecondQPrimitiveFactor_escape_energy_or_fixedExtendedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (k l : Fin 3)
    (q : Fin 6)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hPrimitiveTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingSecondQPrimitiveFactorAt
              hH3 hClass (hτ n) k l q
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
              velocityH3EnergyAt u (τ (s n))
          )
          atTop
          atTop
    )
      ∨
    (
      ∃ m : ℕ,
        m ≠ 0
          ∧
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
                  hH3 hClass m
                  (τ (s n))
                  (hτ (s n))
            )
            atTop
            (𝓝 ∞)
    ) := by

  fin_cases q

  · have hRawTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingThirdQRawL2FactorAt
                hH3 hClass (hτ n) k l 0
          )
          atTop
          atTop := by
      simpa [
        h3TerminalForcingSecondQPrimitiveFactorAt,
        h3TerminalForcingThirdQRawL2FactorAt
      ] using hPrimitiveTop

    have hNot :=
      not_h3TerminalForcingThirdQRawL2FactorAt_tendstoAtTop
        hH3 hClass k l 0 τ hτ hTauTendsto

    exact
      False.elim
        (hNot hRawTop)

  · have hRawTop :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingThirdQRawL2FactorAt
                hH3 hClass (hτ n) k l 1
          )
          atTop
          atTop := by
      simpa [
        h3TerminalForcingSecondQPrimitiveFactorAt,
        h3TerminalForcingThirdQRawL2FactorAt
      ] using hPrimitiveTop

    have hNot :=
      not_h3TerminalForcingThirdQRawL2FactorAt_tendstoAtTop
        hH3 hClass k l 1 τ hτ hTauTendsto

    exact
      False.elim
        (hNot hRawTop)

  · have hM6Top :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
                hH3 hClass (hτ n) k
          )
          atTop
          atTop := by
      simpa [
        h3TerminalForcingSecondQPrimitiveFactorAt,
        h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
      ] using hPrimitiveTop

    exact
      h3TerminalSecondQVelocityMoment6_escape_energy_or_fixedExtendedHigherRadial
        hH3 hClass k τ hτ hTauTendsto hM6Top

  · have hL1Top :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingThirdQRawL1MassAt
                hH3 hClass (hτ n) l
          )
          atTop
          atTop := by
      simpa [
        h3TerminalForcingSecondQPrimitiveFactorAt,
        h3TerminalForcingThirdQRawL1MassAt
      ] using hPrimitiveTop

    have hEnergyTop :=
      velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingThirdQRawL1MassAt_tendstoAtTop
        hH3 hClass l τ hτ hL1Top

    exact
      Or.inl
        ⟨
          id,
          (fun n => le_rfl),
          tendsto_id,
          hTauTendsto,
          by simpa using hEnergyTop
        ⟩

  · have hL1Top :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalForcingThirdQRawL1MassAt
                hH3 hClass (hτ n) k
          )
          atTop
          atTop := by
      simpa [
        h3TerminalForcingSecondQPrimitiveFactorAt,
        h3TerminalForcingThirdQRawL1MassAt
      ] using hPrimitiveTop

    have hEnergyTop :=
      velocityH3EnergyAt_tendstoAtTop_of_h3TerminalForcingThirdQRawL1MassAt_tendstoAtTop
        hH3 hClass k τ hτ hL1Top

    exact
      Or.inl
        ⟨
          id,
          (fun n => le_rfl),
          tendsto_id,
          hTauTendsto,
          by simpa using hEnergyTop
        ⟩

  · have hM6Top :
        Tendsto
          (
            fun n : ℕ =>
              h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
                hH3 hClass (hτ n) l
          )
          atTop
          atTop := by
      simpa [
        h3TerminalForcingSecondQPrimitiveFactorAt,
        h3TerminalSecondQForcingDerivativeVelocityMoment6MassAt
      ] using hPrimitiveTop

    exact
      h3TerminalSecondQVelocityMoment6_escape_energy_or_fixedExtendedHigherRadial
        hH3 hClass l τ hτ hTauTendsto hM6Top

/--
Complete closure of the second-q forcing-state mass branch.

If the physical second-q forcing mass diverges along a strict terminal
sequence, a cofinal refinement carries either physical H³-energy escape or one
fixed nonzero extended higher-radial moment escape.
-/
theorem h3TerminalForcingSecondQMassPath_escape_energy_or_fixedExtendedHigherRadial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hTauTendsto : Tendsto τ atTop (𝓝 T))
    (hMassTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalPhysicalTopDissipationForcingSecondQMassPath
              hH3 hClass j (τ n)
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
              velocityH3EnergyAt u (τ (s n))
          )
          atTop
          atTop
    )
      ∨
    (
      ∃ m : ℕ,
        m ≠ 0
          ∧
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
                  hH3 hClass m
                  (τ (s n))
                  (hτ (s n))
            )
            atTop
            (𝓝 ∞)
    ) := by

  obtain
    ⟨k, l, q, s, hs, hsTop, hTauSub, hPrimitiveTop⟩ :=
    exists_fixed_h3TerminalForcingSecondQPrimitiveFactor_subsequence_of_massPath_tendstoAtTop
      hH3 hClass j τ hτ hTauTendsto hMassTop

  rcases
    h3TerminalForcingSecondQPrimitiveFactor_escape_energy_or_fixedExtendedHigherRadial
      hH3
      hClass
      k
      l
      q
      (fun n : ℕ => τ (s n))
      (fun n : ℕ => hτ (s n))
      hTauSub
      hPrimitiveTop
  with
    hEnergy
    |
    hHigher

  · rcases hEnergy with
      ⟨v, hv, hvTop, hTauFinal, hEnergyTop⟩

    refine
      Or.inl
        ⟨
          (fun n : ℕ => s (v n)),
          ?_,
          hsTop.comp hvTop,
          hTauFinal,
          hEnergyTop
        ⟩

    intro n

    exact
      le_trans
        (hv n)
        (hs (v n))

  · rcases hHigher with
      ⟨m, hm, v, hv, hvTop, hTauFinal, hHigherTop⟩

    refine
      Or.inr
        ⟨
          m,
          hm,
          (fun n : ℕ => s (v n)),
          ?_,
          hsTop.comp hvTop,
          hTauFinal,
          hHigherTop
        ⟩

    intro n

    exact
      le_trans
        (hv n)
        (hs (v n))

end

end Euclidean
end Bridge
end PrimeTensor
