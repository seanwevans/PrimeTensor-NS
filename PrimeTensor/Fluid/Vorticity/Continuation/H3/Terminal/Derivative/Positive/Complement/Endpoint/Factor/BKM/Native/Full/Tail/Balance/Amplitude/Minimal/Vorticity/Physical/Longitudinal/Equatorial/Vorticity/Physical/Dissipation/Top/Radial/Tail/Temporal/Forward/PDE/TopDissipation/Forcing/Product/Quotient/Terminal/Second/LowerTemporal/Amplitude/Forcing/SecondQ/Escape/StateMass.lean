import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.LowerTemporal.Amplitude.Forcing.SecondQ.Escape

/-!
# Second-q forcing-state Young envelope

The second-q forcing-state escape has been frozen to one fixed order-three
velocity product-convolution pair.

This file packages the corresponding Young state-mass envelope.  Because both
factors are terminal velocity coordinates, the envelope contains only

* raw `L²`;
* raw `L¹`;
* raw Fourier moment `6`.

No projected-RHS state or orientation remains.

The generic order-three convolution estimate gives

    productNorm² ≤ stateMassEnvelope,

and hence escape of the frozen product pair forces escape of the explicit
velocity state-mass envelope.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalSecondQForcingStateMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalSecondQForcingStateMass :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 1800000

/--
Explicit Young state-mass envelope for one frozen second-q velocity pair.
-/
noncomputable def h3TerminalForcingSecondQStateMassEnvelopeAt
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
    ‖h3SpectralScalarRawFourierConjL2 (U k)‖
      *
    ‖h3SpectralScalarRawFourierL2 (U l)‖
  )
    *
  (
    h3FourierMomentSplitCoefficient (6 : ℝ)
      *
    (
      h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U k)
        *
      h3SpectralScalarRawFourierL1Mass (U l)
      +
      h3SpectralScalarRawFourierL1Mass (U k)
        *
      h3SpectralScalarRawFourierMomentMass (6 : ℝ) (U l)
    )
  )

theorem h3TerminalForcingSecondQStateMassEnvelopeAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    0 ≤
      h3TerminalForcingSecondQStateMassEnvelopeAt
        hH3 hClass ht k l := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let h6 :
      ∀ q : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * 3 : ℕ) : ℝ))
          (U q) := by
    intro q
    simpa using
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayTwo
        hH3 hClass ht q

  have hBound :=
    norm_sq_h3RawProductConvolutionRadialFourierL2_le_stateMasses
      3
      (U k) (U l)
      (h6 k) (h6 l)

  have hNonneg :
      0 ≤
        (
          ‖h3SpectralScalarRawFourierConjL2 (U k)‖ *
            ‖h3SpectralScalarRawFourierL2 (U l)‖
        )
          *
        (
          h3FourierMomentSplitCoefficient (((2 * 3 : ℕ) : ℝ))
            *
          (
            h3SpectralScalarRawFourierMomentMass
                (((2 * 3 : ℕ) : ℝ))
                (U k)
              *
            h3SpectralScalarRawFourierL1Mass (U l)
            +
            h3SpectralScalarRawFourierL1Mass (U k)
              *
            h3SpectralScalarRawFourierMomentMass
                (((2 * 3 : ℕ) : ℝ))
                (U l)
          )
        ) :=
    (sq_nonneg
      ‖h3RawProductConvolutionRadialFourierL2
          3
          (U k) (U l)
          (h6 k) (h6 l)‖).trans
      hBound

  unfold h3TerminalForcingSecondQStateMassEnvelopeAt
  dsimp only [U, htAbs]

  simpa only [
    show (((2 * 3 : ℕ) : ℝ)) = (6 : ℝ) by norm_num
  ] using hNonneg

/--
The square of the frozen second-q order-three velocity convolution norm is
bounded by its explicit moment-six Young envelope.
-/
theorem sq_h3TerminalForcingSecondQRadialProductNormAt_le_stateMassEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (k l : Fin 3) :
    (
      h3TerminalForcingSecondQRadialProductNormAt
        hH3 hClass ht k l
    ) ^ 2
      ≤
    h3TerminalForcingSecondQStateMassEnvelopeAt
      hH3 hClass ht k l := by

  let htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩

  let U : H3SpectralFinVectorState :=
    h3TerminalVelocitySpectralStateAt hH3 t htAbs

  let h6 :
      ∀ q : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * 3 : ℕ) : ℝ))
          (U q) := by
    intro q
    simpa using
      h3TerminalVelocitySpectralStateAt_rawFourierMomentIntegrable_for_radialLerayTwo
        hH3 hClass ht q

  have hBound :=
    norm_sq_h3RawProductConvolutionRadialFourierL2_le_stateMasses
      3
      (U k) (U l)
      (h6 k) (h6 l)

  unfold
    h3TerminalForcingSecondQRadialProductNormAt
    h3TerminalForcingSecondQStateMassEnvelopeAt

  dsimp only [U, h6, htAbs]

  simpa only [
    show (((2 * 3 : ℕ) : ℝ)) = (6 : ℝ) by norm_num
  ] using hBound

/--
Escape of one frozen second-q velocity convolution pair forces escape of its
explicit Young state-mass envelope.
-/
theorem h3TerminalForcingSecondQStateMassEnvelopeAt_tendstoAtTop_of_productNorm_tendstoAtTop
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
            h3TerminalForcingSecondQRadialProductNormAt
              hH3 hClass (hτ n) k l
        )
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          h3TerminalForcingSecondQStateMassEnvelopeAt
            hH3 hClass (hτ n) k l
      )
      atTop
      atTop := by

  refine tendsto_atTop.2 ?_

  intro M

  let R : ℝ := max M 1

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
        h3TerminalForcingSecondQRadialProductNormAt
          hH3 hClass (hτ n) k l :=
    hNormTop.eventually
      (eventually_gt_atTop R)

  filter_upwards [hLarge] with n hn

  have hSqBound :=
    sq_h3TerminalForcingSecondQRadialProductNormAt_le_stateMassEnvelope
      hH3 hClass (hτ n) k l

  have hR0 :
      0 ≤ R :=
    le_trans
      (by norm_num)
      hOneLe

  have hNorm0 :=
    h3TerminalForcingSecondQRadialProductNormAt_nonneg
      hH3 hClass (hτ n) k l

  have hRSqLeNormSq :
      R ^ 2
        ≤
      (
        h3TerminalForcingSecondQRadialProductNormAt
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
Complete second-q forcing-state reduction through the Young envelope: a
divergent forcing mass has a cofinal refinement with one fixed coordinate pair
whose explicit velocity state-mass envelope diverges.
-/
theorem exists_fixed_pair_subsequence_of_h3TerminalForcingSecondQMassPath_stateMassEnvelope_tendstoAtTop
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
              h3TerminalForcingSecondQStateMassEnvelopeAt
                hH3 hClass (hτ (s n)) k l
          )
          atTop
          atTop := by

  obtain
    ⟨k, l, s, hs, hsTop, hTauSub, hPairTop⟩ :=
    exists_fixed_pair_subsequence_of_h3TerminalForcingSecondQMassPath_tendstoAtTop
      hH3 hClass j τ hτ hTauTendsto hMassTop

  have hEnvelopeTop :=
    h3TerminalForcingSecondQStateMassEnvelopeAt_tendstoAtTop_of_productNorm_tendstoAtTop
      hH3
      hClass
      k
      l
      (fun n : ℕ => τ (s n))
      (fun n : ℕ => hτ (s n))
      hPairTop

  exact
    ⟨
      k,
      l,
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
