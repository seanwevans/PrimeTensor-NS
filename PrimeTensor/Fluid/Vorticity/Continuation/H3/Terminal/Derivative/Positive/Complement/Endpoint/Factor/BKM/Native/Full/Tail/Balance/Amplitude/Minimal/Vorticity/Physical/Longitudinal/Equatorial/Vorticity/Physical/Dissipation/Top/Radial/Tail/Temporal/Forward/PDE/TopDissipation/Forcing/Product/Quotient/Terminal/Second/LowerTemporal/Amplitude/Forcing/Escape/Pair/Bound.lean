import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.Escape.Pair

/-!
# Bound the frozen fourth-q forcing pair by terminal state masses

The preceding checkpoint freezes one order-five radial raw-product-convolution
channel `(k,l)` whenever the fourth-q radial-Leray forcing envelope escapes.

The generic quantitative Young estimate already bounds the square of that
radial convolution norm by four primitive state masses:

* raw Fourier `L²` norm of the first factor,
* raw Fourier `L²` norm of the second factor,
* order-ten raw Fourier moment mass,
* raw Fourier `L¹` mass.

This file names the resulting terminal state-mass envelope and transfers
escape of the fixed radial product norm to escape of that explicit envelope.
No new analytic estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3TerminalFourthQForcingFixedPairStateMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQForcingFixedPairStateMass :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
Explicit Young state-mass envelope for one frozen terminal order-five radial
raw-product-convolution channel.
-/
noncomputable def h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) : ℝ :=
  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs
  (
    ‖h3SpectralScalarRawFourierConjL2 (U k)‖ *
      ‖h3SpectralScalarRawFourierL2 (U l)‖
  )
    *
  (
    h3FourierMomentSplitCoefficient (10 : ℝ)
      *
    (
      h3SpectralScalarRawFourierMomentMass (10 : ℝ) (U k)
        *
      h3SpectralScalarRawFourierL1Mass (U l)
      +
      h3SpectralScalarRawFourierL1Mass (U k)
        *
      h3SpectralScalarRawFourierMomentMass (10 : ℝ) (U l)
    )
  )

/-- The terminal fixed-pair state-mass envelope is nonnegative. -/
theorem h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    0 ≤
      h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
        hH3 hClass ht k l := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let h10 :
      ∀ q : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (4 + 1) : ℕ) : ℝ))
          (U q) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayFour
      hH3 hClass ht

  have hBound :=
    norm_sq_h3RawProductConvolutionRadialFourierL2_le_stateMasses
      5
      (U k)
      (U l)
      (h10 k)
      (h10 l)

  have hNonneg :
      0 ≤
        (
          ‖h3SpectralScalarRawFourierConjL2 (U k)‖ *
            ‖h3SpectralScalarRawFourierL2 (U l)‖
        )
          *
        (
          h3FourierMomentSplitCoefficient (((2 * 5 : ℕ) : ℝ))
            *
          (
            h3SpectralScalarRawFourierMomentMass
                (((2 * 5 : ℕ) : ℝ))
                (U k)
              *
            h3SpectralScalarRawFourierL1Mass (U l)
            +
            h3SpectralScalarRawFourierL1Mass (U k)
              *
            h3SpectralScalarRawFourierMomentMass
                (((2 * 5 : ℕ) : ℝ))
                (U l)
          )
        ) :=
    (sq_nonneg
      ‖h3RawProductConvolutionRadialFourierL2
          5
          (U k)
          (U l)
          (h10 k)
          (h10 l)‖).trans
      hBound

  unfold h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
  dsimp only

  simpa only [
    show (((2 * 5 : ℕ) : ℝ)) = (10 : ℝ) by norm_num
  ] using hNonneg

/--
The square of one terminal order-five radial raw-product-convolution norm is
bounded by its explicit Young state-mass envelope.
-/
theorem sq_h3TerminalForcingFourthQRadialProductNormAt_le_stateMassEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    (
      h3TerminalForcingFourthQRadialProductNormAt
        hH3 hClass ht k l
    ) ^ 2
      ≤
    h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
      hH3 hClass ht k l := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let h10 :
      ∀ q : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (4 + 1) : ℕ) : ℝ))
          (U q) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayFour
      hH3 hClass ht

  have hBound :=
    norm_sq_h3RawProductConvolutionRadialFourierL2_le_stateMasses
      5
      (U k)
      (U l)
      (h10 k)
      (h10 l)

  unfold h3TerminalForcingFourthQRadialProductNormAt
  unfold h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
  dsimp only

  simpa only [show (((2 * 5 : ℕ) : ℝ)) = (10 : ℝ) by norm_num] using
    hBound

/--
Escape of one fixed terminal order-five radial product norm forces escape of
its explicit Young state-mass envelope on the same sequence.
-/
theorem h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt_tendstoAtTop_of_productNorm_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (k l : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hNormTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalForcingFourthQRadialProductNormAt
              hH3 hClass (hτ n) k l
        )
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
            hH3 hClass (hτ n) k l
      )
      atTop
      atTop := by

  refine
    tendsto_atTop.2
      ?_

  intro M

  let R : ℝ :=
    max M 1

  have hMLe :
      M ≤ R := by
    dsimp only [R]
    exact le_max_left M 1

  have hOneLe :
      1 ≤ R := by
    dsimp only [R]
    exact le_max_right M 1

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        R
          <
        h3TerminalForcingFourthQRadialProductNormAt
          hH3 hClass (hτ n) k l :=
    hNormTop.eventually
      (eventually_gt_atTop R)

  filter_upwards [hLarge] with n hn

  have hNormNonneg :
      0 ≤
        h3TerminalForcingFourthQRadialProductNormAt
          hH3 hClass (hτ n) k l :=
    h3TerminalForcingFourthQRadialProductNormAt_nonneg
      hH3 hClass (hτ n) k l

  have hSqBound :=
    sq_h3TerminalForcingFourthQRadialProductNormAt_le_stateMassEnvelope
      hH3 hClass (hτ n) k l

  have hRNonneg :
      0 ≤ R :=
    le_trans
      (by norm_num)
      hOneLe

  have hRSqLeNormSq :
      R ^ 2
        ≤
      (
        h3TerminalForcingFourthQRadialProductNormAt
          hH3 hClass (hτ n) k l
      ) ^ 2 := by
    nlinarith

  have hRLeRSq :
      R ≤ R ^ 2 := by
    nlinarith

  exact
    hMLe.trans
      (
        hRLeRSq.trans
          (
            hRSqLeNormSq.trans
              hSqBound
          )
      )

/--
The fourth-temporal state-amplitude frontier now reduces to either the existing
shift-two higher-radial velocity moment, or the explicit Young state-mass
envelope of one fixed terminal order-five product channel on a cofinal
subsequence.
-/
theorem fourthTemporal_amplitude_escape_extendedHigherTwo_or_fixedForcingStateMassEnvelope
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
      ∃ k l : Fin 3,
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
                h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt
                  hH3 hClass (hτ (s n)) k l
            )
            atTop
            atTop
    ) := by

  rcases
    fourthTemporal_amplitude_escape_extendedHigherTwo_or_fixedForcingRadialProductPair
      hH3 hClass j τ hτ hTauTendsto hAmplitudeTop
  with
    hHigher
    |
    hPair

  · exact
      Or.inl hHigher

  · rcases hPair with
      ⟨k, l, s, hs, hsTop, hTauSub, hNormTop⟩

    exact
      Or.inr
        ⟨
          k,
          l,
          s,
          hs,
          hsTop,
          hTauSub,
          h3TerminalForcingFourthQRadialProductStateMassEnvelopeAt_tendstoAtTop_of_productNorm_tendstoAtTop
            hH3 hClass k l
            (fun n : ℕ => τ (s n))
            (fun n : ℕ => hτ (s n))
            hNormTop
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
