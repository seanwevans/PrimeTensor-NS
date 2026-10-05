import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Fourth.Raw.Higher.Collapse.Subtail.Fourth.Forcing.Bound.Escape

/-!
# Reduce a frozen fourth-q forcing derivative channel to state masses

A fourth-q forcing derivative escape has now been reduced to one fixed
order-five raw-product-convolution channel.  The generic Young estimate applies
with doubled moment order ten.

This file names the two oriented scalar states selected by the frozen channel,
packages their explicit state-mass envelope, transfers channel escape to escape
of that envelope, and substitutes the result back into the fourth-temporal
frontier.

The remaining primitive factors are therefore raw `L²`, raw `L¹`, and
order-ten Fourier moment masses of one velocity/projected-RHS pair.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalFourthQForcingDerivativeStateMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalFourthQForcingDerivativeStateMass :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 1800000

/--
First scalar factor of a frozen product-rule channel.

Orientation `0` selects the projected-RHS factor `R_k`; orientation `1`
selects the velocity factor `U_k`.
-/
noncomputable def h3TerminalFourthQForcingDerivativeFirstStateAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k : Fin 3) :
    H3SpectralScalarState :=
  let d :=
    h3TerminalFourthQForcingDerivativeLerayDataAt
      hH3 hClass ht j
  if o = 0 then d.R k else d.U k

/--
Second scalar factor of a frozen product-rule channel.

Orientation `0` selects the velocity factor `U_l`; orientation `1` selects the
projected-RHS factor `R_l`.
-/
noncomputable def h3TerminalFourthQForcingDerivativeSecondStateAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (l : Fin 3) :
    H3SpectralScalarState :=
  let d :=
    h3TerminalFourthQForcingDerivativeLerayDataAt
      hH3 hClass ht j
  if o = 0 then d.U l else d.R l

theorem h3TerminalFourthQForcingDerivativeFirstStateAt_moment10_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k : Fin 3) :
    H3RawFourierMomentIntegrable
      (10 : ℝ)
      (h3TerminalFourthQForcingDerivativeFirstStateAt
        hH3 hClass ht j o k) := by

  unfold h3TerminalFourthQForcingDerivativeFirstStateAt
  dsimp only

  by_cases ho : o = 0
  · simp only [ho, if_pos]
    exact
      (h3TerminalFourthQForcingDerivativeLerayDataAt
        hH3 hClass ht j).hR k
  · simp only [ho, if_neg]
    exact
      (h3TerminalFourthQForcingDerivativeLerayDataAt
        hH3 hClass ht j).hU k

theorem h3TerminalFourthQForcingDerivativeSecondStateAt_moment10_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (l : Fin 3) :
    H3RawFourierMomentIntegrable
      (10 : ℝ)
      (h3TerminalFourthQForcingDerivativeSecondStateAt
        hH3 hClass ht j o l) := by

  unfold h3TerminalFourthQForcingDerivativeSecondStateAt
  dsimp only

  by_cases ho : o = 0
  · simp only [ho, if_pos]
    exact
      (h3TerminalFourthQForcingDerivativeLerayDataAt
        hH3 hClass ht j).hU l
  · simp only [ho, if_neg]
    exact
      (h3TerminalFourthQForcingDerivativeLerayDataAt
        hH3 hClass ht j).hR l

/--
The named frozen channel is exactly the order-five radial convolution norm of
the two oriented scalar states.
-/
theorem h3TerminalFourthQForcingDerivativeRadialProductNormAt_eq_states
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) :
    h3TerminalFourthQForcingDerivativeRadialProductNormAt
        hH3 hClass ht j o k l
      =
    ‖h3RawProductConvolutionRadialFourierL2
        5
        (h3TerminalFourthQForcingDerivativeFirstStateAt
          hH3 hClass ht j o k)
        (h3TerminalFourthQForcingDerivativeSecondStateAt
          hH3 hClass ht j o l)
        (h3TerminalFourthQForcingDerivativeFirstStateAt_moment10_integrable
          hH3 hClass ht j o k)
        (h3TerminalFourthQForcingDerivativeSecondStateAt_moment10_integrable
          hH3 hClass ht j o l)‖ := by

  by_cases ho : o = 0

  · simp [
      h3TerminalFourthQForcingDerivativeRadialProductNormAt,
      h3TerminalFourthQForcingDerivativeFirstStateAt,
      h3TerminalFourthQForcingDerivativeSecondStateAt,
      ho
    ]

  · simp [
      h3TerminalFourthQForcingDerivativeRadialProductNormAt,
      h3TerminalFourthQForcingDerivativeFirstStateAt,
      h3TerminalFourthQForcingDerivativeSecondStateAt,
      ho
    ]

/--
Explicit Young state-mass envelope of a frozen fourth-q forcing derivative
channel.
-/
noncomputable def h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) : ℝ :=
  let F :=
    h3TerminalFourthQForcingDerivativeFirstStateAt
      hH3 hClass ht j o k
  let G :=
    h3TerminalFourthQForcingDerivativeSecondStateAt
      hH3 hClass ht j o l
  (
    ‖h3SpectralScalarRawFourierConjL2 F‖ *
      ‖h3SpectralScalarRawFourierL2 G‖
  )
    *
  (
    h3FourierMomentSplitCoefficient (10 : ℝ)
      *
    (
      h3SpectralScalarRawFourierMomentMass (10 : ℝ) F
        *
      h3SpectralScalarRawFourierL1Mass G
      +
      h3SpectralScalarRawFourierL1Mass F
        *
      h3SpectralScalarRawFourierMomentMass (10 : ℝ) G
    )
  )

/--
The frozen fourth-q forcing derivative state-mass envelope is nonnegative.
-/
theorem h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) :
    0 ≤
      h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt
        hH3 hClass ht j o k l := by

  let F :=
    h3TerminalFourthQForcingDerivativeFirstStateAt
      hH3 hClass ht j o k

  let G :=
    h3TerminalFourthQForcingDerivativeSecondStateAt
      hH3 hClass ht j o l

  let hF :
      H3RawFourierMomentIntegrable
        (((2 * 5 : ℕ) : ℝ))
        F := by
    dsimp only [F]
    simpa using
      h3TerminalFourthQForcingDerivativeFirstStateAt_moment10_integrable
        hH3 hClass ht j o k

  let hG :
      H3RawFourierMomentIntegrable
        (((2 * 5 : ℕ) : ℝ))
        G := by
    dsimp only [G]
    simpa using
      h3TerminalFourthQForcingDerivativeSecondStateAt_moment10_integrable
        hH3 hClass ht j o l

  have hBound :=
    norm_sq_h3RawProductConvolutionRadialFourierL2_le_stateMasses
      5 F G hF hG

  have hNonneg :
      0 ≤
        (
          ‖h3SpectralScalarRawFourierConjL2 F‖ *
            ‖h3SpectralScalarRawFourierL2 G‖
        )
          *
        (
          h3FourierMomentSplitCoefficient (((2 * 5 : ℕ) : ℝ))
            *
          (
            h3SpectralScalarRawFourierMomentMass
                (((2 * 5 : ℕ) : ℝ))
                F
              *
            h3SpectralScalarRawFourierL1Mass G
            +
            h3SpectralScalarRawFourierL1Mass F
              *
            h3SpectralScalarRawFourierMomentMass
                (((2 * 5 : ℕ) : ℝ))
                G
          )
        ) :=
    (sq_nonneg
      ‖h3RawProductConvolutionRadialFourierL2
          5 F G hF hG‖).trans
      hBound

  unfold h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt
  dsimp only

  simpa only [
    show (((2 * 5 : ℕ) : ℝ)) = (10 : ℝ) by norm_num
  ] using hNonneg

/--
The square of a frozen fourth-q forcing derivative radial product norm is
bounded by its explicit Young state-mass envelope.
-/
theorem sq_h3TerminalFourthQForcingDerivativeRadialProductNormAt_le_stateMassEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) :
    (
      h3TerminalFourthQForcingDerivativeRadialProductNormAt
        hH3 hClass ht j o k l
    ) ^ 2
      ≤
    h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt
      hH3 hClass ht j o k l := by

  let F :=
    h3TerminalFourthQForcingDerivativeFirstStateAt
      hH3 hClass ht j o k

  let G :=
    h3TerminalFourthQForcingDerivativeSecondStateAt
      hH3 hClass ht j o l

  let hF :
      H3RawFourierMomentIntegrable
        (((2 * 5 : ℕ) : ℝ))
        F := by
    dsimp only [F]
    simpa using
      h3TerminalFourthQForcingDerivativeFirstStateAt_moment10_integrable
        hH3 hClass ht j o k

  let hG :
      H3RawFourierMomentIntegrable
        (((2 * 5 : ℕ) : ℝ))
        G := by
    dsimp only [G]
    simpa using
      h3TerminalFourthQForcingDerivativeSecondStateAt_moment10_integrable
        hH3 hClass ht j o l

  have hBound :=
    norm_sq_h3RawProductConvolutionRadialFourierL2_le_stateMasses
      5 F G hF hG

  rw [
    h3TerminalFourthQForcingDerivativeRadialProductNormAt_eq_states
      hH3 hClass ht j o k l
  ]

  unfold h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt
  dsimp only [F, G]

  simpa only [
    show (((2 * 5 : ℕ) : ℝ)) = (10 : ℝ) by norm_num
  ] using hBound

/--
Escape of one frozen fourth-q forcing derivative radial product norm forces
escape of its explicit Young state-mass envelope.
-/
theorem h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt_tendstoAtTop_of_productNorm_tendstoAtTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3)
    (τ : ℕ → ℝ)
    (hτ :
      ∀ n : ℕ,
        τ n ∈ Set.Ioo a T)
    (hNormTop :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalFourthQForcingDerivativeRadialProductNormAt
              hH3 hClass (hτ n) j o k l
        )
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt
            hH3 hClass (hτ n) j o k l
      )
      atTop
      atTop := by

  refine tendsto_atTop.2 ?_

  intro M

  let R0 : ℝ :=
    max M 1

  have hMLe :
      M ≤ R0 := by
    dsimp only [R0]
    exact le_max_left M 1

  have hOneLe :
      1 ≤ R0 := by
    dsimp only [R0]
    exact le_max_right M 1

  have hLarge :
      ∀ᶠ n : ℕ in atTop,
        R0
          <
        h3TerminalFourthQForcingDerivativeRadialProductNormAt
          hH3 hClass (hτ n) j o k l :=
    hNormTop.eventually
      (eventually_gt_atTop R0)

  filter_upwards [hLarge] with n hn

  have hNormNonneg :
      0 ≤
        h3TerminalFourthQForcingDerivativeRadialProductNormAt
          hH3 hClass (hτ n) j o k l :=
    h3TerminalFourthQForcingDerivativeRadialProductNormAt_nonneg
      hH3 hClass (hτ n) j o k l

  have hSqBound :=
    sq_h3TerminalFourthQForcingDerivativeRadialProductNormAt_le_stateMassEnvelope
      hH3 hClass (hτ n) j o k l

  have hR0Nonneg :
      0 ≤ R0 :=
    le_trans
      (by norm_num)
      hOneLe

  have hR0SqLeNormSq :
      R0 ^ 2
        ≤
      (
        h3TerminalFourthQForcingDerivativeRadialProductNormAt
          hH3 hClass (hτ n) j o k l
      ) ^ 2 := by
    nlinarith

  have hR0LeR0Sq :
      R0 ≤ R0 ^ 2 := by
    nlinarith

  exact
    hMLe.trans
      (
        hR0LeR0Sq.trans
          (
            hR0SqLeNormSq.trans
              hSqBound
          )
      )

/--
Fourth-temporal Hilbert derivative escape now resolves to physical H³ energy,
one fixed nonzero extended higher-radial moment, or one fixed explicit Young
state-mass envelope of a velocity/projected-RHS product channel.
-/
theorem fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_fixedForcingDerivativeStateMassEnvelope
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
    (hFourth :
      Tendsto
        (
          fun n : ℕ =>
            h3TerminalResolvedPhysicalPDEChannelHilbertDerivativeNormEnvelope
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
    )
      ∨
    (
      ∃ o : Fin 2,
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
                  h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt
                    hH3 hClass (hτ (s n)) j o k l
              )
              atTop
              atTop
    ) := by

  rcases
    fourthTemporal_hilbertDerivativeNorm_escape_energy_or_fixedExtendedHigherRadial_or_forcingDerivative
      hH3 hClass j τ hτ hTauTendsto hFourth
  with
    hEnergy
    |
    hRest

  · exact Or.inl hEnergy

  · rcases hRest with
      hHigher
      |
      hDerivTop

    · exact
        Or.inr
          (Or.inl hHigher)

    · obtain
        ⟨o, k, l, s, hs, hsTop, hTauSub, hNormTop⟩ :=
        exists_fixed_orientation_pair_subsequence_of_h3TerminalFourthQForcingDerivative_tendstoAtTop
          hH3 hClass j τ hτ hTauTendsto hDerivTop

      exact
        Or.inr
          (
            Or.inr
              ⟨
                o,
                k,
                l,
                s,
                hs,
                hsTop,
                hTauSub,
                h3TerminalFourthQForcingDerivativeStateMassEnvelopeAt_tendstoAtTop_of_productNorm_tendstoAtTop
                  hH3 hClass j o k l
                  (fun n : ℕ => τ (s n))
                  (fun n : ℕ => hτ (s n))
                  hNormTop
              ⟩
          )

end

end Euclidean
end Bridge
end PrimeTensor
