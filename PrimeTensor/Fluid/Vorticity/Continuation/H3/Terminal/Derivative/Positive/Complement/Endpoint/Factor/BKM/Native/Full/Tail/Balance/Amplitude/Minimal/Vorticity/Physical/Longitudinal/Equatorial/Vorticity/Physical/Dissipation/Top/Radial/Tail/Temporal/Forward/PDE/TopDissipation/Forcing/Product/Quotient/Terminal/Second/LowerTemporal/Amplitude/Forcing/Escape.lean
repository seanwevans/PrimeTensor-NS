import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Fourth-q forcing escape reduces to the terminal radial Leray envelope

The preceding checkpoint bounds the canonical fourth-q forcing mass

    ‖q² F_j(U,U)‖²

by the square of the explicit order-four radial Leray envelope.  This file
names that envelope and transfers forcing-mass escape to escape of the
already-compiled order-five radial product-convolution bound.

Combining that transfer with the fourth-temporal amplitude split leaves only:

* escape of the existing shift-two extended higher-radial velocity moment on
  a cofinal subsequence, or
* escape of the terminal order-four radial Leray envelope on a cofinal
  subsequence.

No new analytic estimate is introduced here.  The step is quantitative only:
a nonnegative quantity whose square dominates something tending to `+∞` must
itself tend to `+∞`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3TerminalFourthQForcingRadialLerayEscape
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQForcingRadialLerayEscape :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
The explicit nonnegative radial-Leray envelope controlling the canonical
terminal fourth-q forcing coordinate.
-/
noncomputable def h3TerminalForcingFourthQRadialLerayEnvelopeAt
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
  let h10 :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (4 + 1) : ℕ) : ℝ))
          (U k) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayFour
      hH3 hClass ht
  ((2 * Real.pi) ^ 4 : ℝ)
    *
  (
    ∑ k : Fin 3,
      2 *
        (
          ∑ l : Fin 3,
            (2 * Real.pi) *
              ‖h3RawProductConvolutionRadialFourierL2
                  5
                  (U k) (U l)
                  (h10 k) (h10 l)‖
        )
  )

/-- The terminal fourth-q radial-Leray envelope is nonnegative. -/
theorem h3TerminalForcingFourthQRadialLerayEnvelopeAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    0 ≤
      h3TerminalForcingFourthQRadialLerayEnvelopeAt
        hH3 hClass ht j := by

  unfold h3TerminalForcingFourthQRadialLerayEnvelopeAt
  dsimp only

  apply mul_nonneg
  · positivity

  apply Finset.sum_nonneg
  intro k hk

  apply mul_nonneg
  · norm_num

  apply Finset.sum_nonneg
  intro l hl

  exact
    mul_nonneg
      (by positivity)
      (norm_nonneg _)

/--
The previous fourth-q mass estimate is exactly the square bound by the named
terminal radial-Leray envelope.
-/
theorem h3TerminalPhysicalTopDissipationForcingFourthQMassAt_le_sq_radialLerayEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3) :
    h3TerminalPhysicalTopDissipationForcingFourthQMassAt
        hH3 hClass ht j
      ≤
    (
      h3TerminalForcingFourthQRadialLerayEnvelopeAt
        hH3 hClass ht j
    ) ^ 2 := by

  simpa only [h3TerminalForcingFourthQRadialLerayEnvelopeAt] using
    h3TerminalPhysicalTopDissipationForcingFourthQMassAt_le_sq_radialLeray
      hH3 hClass ht j

/--
Escape of the canonical fourth-q forcing mass path forces escape of the named
terminal radial-Leray envelope on the same strict-time sequence.
-/
theorem h3TerminalForcingFourthQRadialLerayEnvelopeAt_tendstoAtTop_of_massPath_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hMassTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalPhysicalTopDissipationForcingFourthQMassPath
              hH3 hClass j (τ n)
        )
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          h3TerminalForcingFourthQRadialLerayEnvelopeAt
            hH3 hClass (hτ n) j
      )
      atTop
      atTop := by

  refine
    tendsto_atTop.2
      ?_

  intro M

  let M0 : ℝ :=
    max M 0

  have hM0Nonneg :
      0 ≤ M0 := by
    dsimp only [M0]
    exact le_max_right M 0

  have hMLe :
      M ≤ M0 := by
    dsimp only [M0]
    exact le_max_left M 0

  have hMassLarge :
      ∀ᶠ n : ℕ in atTop,
        M0 ^ 2
          <
        h3TerminalPhysicalTopDissipationForcingFourthQMassPath
          hH3 hClass j (τ n) :=
    hMassTop.eventually
      (eventually_gt_atTop (M0 ^ 2))

  filter_upwards [hMassLarge] with n hn

  have hBound :=
    h3TerminalPhysicalTopDissipationForcingFourthQMassAt_le_sq_radialLerayEnvelope
      hH3 hClass (hτ n) j

  rw [
    ← h3TerminalPhysicalTopDissipationForcingFourthQMassPath_eq
      hH3 hClass (hτ n) j
  ] at hBound

  have hEnvelopeNonneg :=
    h3TerminalForcingFourthQRadialLerayEnvelopeAt_nonneg
      hH3 hClass (hτ n) j

  have hM0Lt :
      M0
        <
      h3TerminalForcingFourthQRadialLerayEnvelopeAt
        hH3 hClass (hτ n) j := by
    nlinarith

  exact
    le_of_lt
      (
        lt_of_le_of_lt
          hMLe
          hM0Lt
      )

/--
After closing the sixth-diffusion state-size side, fourth-temporal amplitude
escape reduces to either the existing shift-two higher-radial velocity moment,
or the explicit terminal fourth-q radial-Leray envelope.
-/
theorem fourthTemporal_amplitude_escape_extendedHigherTwo_or_forcingFourthQRadialLerayEnvelope
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
              h3TerminalForcingFourthQRadialLerayEnvelopeAt
                hH3 hClass (hτ (s n)) j
          )
          atTop
          atTop
    ) := by

  rcases
    fourthTemporal_amplitude_escape_extendedHigherTwo_or_forcingFourthQMass
      hH3 hClass j τ hτ hTauTendsto hAmplitudeTop
  with
    hHigher
    |
    hForcingMass

  · exact
      Or.inl hHigher

  · rcases hForcingMass with
      ⟨s, hs, hsTop, hTauSub, hMassTop⟩

    have hEnvelopeTop :=
      h3TerminalForcingFourthQRadialLerayEnvelopeAt_tendstoAtTop_of_massPath_tendstoAtTop
        hH3 hClass j
        (fun n : ℕ => τ (s n))
        (fun n : ℕ => hτ (s n))
        hMassTop

    exact
      Or.inr
        ⟨
          s,
          hs,
          hsTop,
          hTauSub,
          hEnvelopeTop
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
