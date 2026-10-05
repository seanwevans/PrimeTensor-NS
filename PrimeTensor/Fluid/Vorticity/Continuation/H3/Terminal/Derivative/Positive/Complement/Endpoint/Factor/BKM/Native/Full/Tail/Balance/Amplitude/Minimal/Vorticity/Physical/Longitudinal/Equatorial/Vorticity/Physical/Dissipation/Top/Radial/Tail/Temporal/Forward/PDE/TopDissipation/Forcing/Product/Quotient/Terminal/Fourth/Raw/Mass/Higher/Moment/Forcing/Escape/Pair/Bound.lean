import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Mass.Higher.Moment.Forcing.Escape.Pair

/-!
# Bound the frozen third-q forcing pair by terminal state masses

The preceding checkpoint freezes one order-seven radial raw-product-convolution
channel `(k,l)` whenever the third-q radial-Leray forcing envelope escapes.

The generic quantitative Young estimate already bounds the square of that
radial convolution norm by four primitive state masses:

* raw Fourier `L²` norm of the first factor,
* raw Fourier `L²` norm of the second factor,
* order-fourteen raw Fourier moment mass,
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

noncomputable local instance axisFintypeH3TerminalThirdQForcingFixedPairStateMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalThirdQForcingFixedPairStateMass :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/--
Explicit Young state-mass envelope for one frozen terminal order-seven radial
raw-product-convolution channel.
-/
noncomputable def h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt
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
    h3FourierMomentSplitCoefficient (14 : ℝ)
      *
    (
      h3SpectralScalarRawFourierMomentMass (14 : ℝ) (U k)
        *
      h3SpectralScalarRawFourierL1Mass (U l)
      +
      h3SpectralScalarRawFourierL1Mass (U k)
        *
      h3SpectralScalarRawFourierMomentMass (14 : ℝ) (U l)
    )
  )

/--
The terminal fixed-pair state-mass envelope is nonnegative.
-/
theorem h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    0 ≤
      h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt
        hH3 hClass ht k l := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let h14 :
      ∀ q : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (6 + 1) : ℕ) : ℝ))
          (U q) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLeraySix
      hH3 hClass ht

  have hBound :=
    norm_sq_h3RawProductConvolutionRadialFourierL2_le_stateMasses
      7
      (U k)
      (U l)
      (h14 k)
      (h14 l)

  have hNonneg :
      0 ≤
        (
          ‖h3SpectralScalarRawFourierConjL2 (U k)‖ *
            ‖h3SpectralScalarRawFourierL2 (U l)‖
        )
          *
        (
          h3FourierMomentSplitCoefficient (((2 * 7 : ℕ) : ℝ))
            *
          (
            h3SpectralScalarRawFourierMomentMass
                (((2 * 7 : ℕ) : ℝ))
                (U k)
              *
            h3SpectralScalarRawFourierL1Mass (U l)
            +
            h3SpectralScalarRawFourierL1Mass (U k)
              *
            h3SpectralScalarRawFourierMomentMass
                (((2 * 7 : ℕ) : ℝ))
                (U l)
          )
        ) :=
    (sq_nonneg
      ‖h3RawProductConvolutionRadialFourierL2
          7
          (U k)
          (U l)
          (h14 k)
          (h14 l)‖).trans
      hBound

  unfold h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt
  dsimp only

  simpa only [
    show (((2 * 7 : ℕ) : ℝ)) = (14 : ℝ) by norm_num
  ] using hNonneg

/--
The square of one terminal order-seven radial raw-product-convolution norm is
bounded by its explicit Young state-mass envelope.
-/
theorem sq_h3TerminalForcingThirdQRadialProductNormAt_le_stateMassEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    (
      h3TerminalForcingThirdQRadialProductNormAt
        hH3 hClass ht k l
    ) ^ 2
      ≤
    h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt
      hH3 hClass ht k l := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let h14 :
      ∀ q : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (6 + 1) : ℕ) : ℝ))
          (U q) :=
    h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLeraySix
      hH3 hClass ht

  have hBound :=
    norm_sq_h3RawProductConvolutionRadialFourierL2_le_stateMasses
      7
      (U k)
      (U l)
      (h14 k)
      (h14 l)

  unfold h3TerminalForcingThirdQRadialProductNormAt
  unfold h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt
  dsimp only

  simpa only [show (((2 * 7 : ℕ) : ℝ)) = (14 : ℝ) by norm_num] using
    hBound

/--
Escape of one fixed terminal order-seven radial product norm forces escape of
its explicit Young state-mass envelope on the same sequence.
-/
theorem h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt_tendstoAtTop_of_productNorm_tendstoAtTop
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
            h3TerminalForcingThirdQRadialProductNormAt
              hH3 hClass (hτ n) k l
        )
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt
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
        h3TerminalForcingThirdQRadialProductNormAt
          hH3 hClass (hτ n) k l :=
    hNormTop.eventually
      (eventually_gt_atTop R)

  filter_upwards [hLarge] with n hn

  have hNormNonneg :
      0 ≤
        h3TerminalForcingThirdQRadialProductNormAt
          hH3 hClass (hτ n) k l :=
    h3TerminalForcingThirdQRadialProductNormAt_nonneg
      hH3 hClass (hτ n) k l

  have hSqBound :=
    sq_h3TerminalForcingThirdQRadialProductNormAt_le_stateMassEnvelope
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
        h3TerminalForcingThirdQRadialProductNormAt
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
The sixth-diffusion derivative frontier now reduces to either the existing
shift-four higher-radial velocity moment, or the explicit Young state-mass
envelope of one fixed terminal order-seven product channel on a cofinal
subsequence.
-/
theorem sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_fixedForcingStateMassEnvelope
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
                h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt
                  hH3 hClass (hτ (s n)) k l
            )
            atTop
            atTop
    ) := by

  rcases
    sixthDiffusion_hilbertDerivativeNorm_escape_extendedHigherFour_or_fixedForcingRadialProductPair
      hH3 hClass j τ hτ hTauTendsto hSixth
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
          h3TerminalForcingThirdQRadialProductStateMassEnvelopeAt_tendstoAtTop_of_productNorm_tendstoAtTop
            hH3 hClass k l
            (fun n : ℕ => τ (s n))
            (fun n : ℕ => hτ (s n))
            hNormTop
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
