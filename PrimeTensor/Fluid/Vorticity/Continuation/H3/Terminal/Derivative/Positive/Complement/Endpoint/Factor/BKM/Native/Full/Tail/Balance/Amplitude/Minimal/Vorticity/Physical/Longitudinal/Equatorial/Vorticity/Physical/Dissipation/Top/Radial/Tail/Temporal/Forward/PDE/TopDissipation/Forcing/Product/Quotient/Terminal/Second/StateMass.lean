import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Quotient.Terminal.Second.Escape

/-!
# Reduce a frozen second-q forcing derivative channel to state masses

A second-q forcing derivative escape has now been reduced to one fixed
order-three raw-product-convolution channel.  The generic Young estimate applies
with doubled moment order six.

This file names the two oriented scalar states selected by the frozen channel,
packages their explicit state-mass envelope, and transfers channel escape to
escape of that envelope.

The remaining primitive factors are raw `L²`, raw `L¹`, and order-six Fourier
moment masses of one velocity/projected-RHS pair.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3TerminalSecondQForcingDerivativeStateMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3TerminalSecondQForcingDerivativeStateMass :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

set_option maxHeartbeats 1800000

/--
First scalar factor of a frozen second-q product-rule channel.

Orientation `0` selects the projected-RHS factor `R_k`; orientation `1`
selects the velocity factor `U_k`.
-/
noncomputable def h3TerminalSecondQForcingDerivativeFirstStateAt
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
    h3TerminalSecondQForcingDerivativeLerayDataAt
      hH3 hClass ht j
  if o = 0 then d.R k else d.U k

/--
Second scalar factor of a frozen second-q product-rule channel.

Orientation `0` selects the velocity factor `U_l`; orientation `1` selects the
projected-RHS factor `R_l`.
-/
noncomputable def h3TerminalSecondQForcingDerivativeSecondStateAt
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
    h3TerminalSecondQForcingDerivativeLerayDataAt
      hH3 hClass ht j
  if o = 0 then d.U l else d.R l

theorem h3TerminalSecondQForcingDerivativeFirstStateAt_moment6_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k : Fin 3) :
    H3RawFourierMomentIntegrable
      (6 : ℝ)
      (h3TerminalSecondQForcingDerivativeFirstStateAt
        hH3 hClass ht j o k) := by

  unfold h3TerminalSecondQForcingDerivativeFirstStateAt
  dsimp only

  by_cases ho : o = 0
  · simp only [ho, if_pos]
    exact
      (h3TerminalSecondQForcingDerivativeLerayDataAt
        hH3 hClass ht j).hR k
  · simp only [ho, if_neg]
    exact
      (h3TerminalSecondQForcingDerivativeLerayDataAt
        hH3 hClass ht j).hU k

theorem h3TerminalSecondQForcingDerivativeSecondStateAt_moment6_integrable
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (l : Fin 3) :
    H3RawFourierMomentIntegrable
      (6 : ℝ)
      (h3TerminalSecondQForcingDerivativeSecondStateAt
        hH3 hClass ht j o l) := by

  unfold h3TerminalSecondQForcingDerivativeSecondStateAt
  dsimp only

  by_cases ho : o = 0
  · simp only [ho, if_pos]
    exact
      (h3TerminalSecondQForcingDerivativeLerayDataAt
        hH3 hClass ht j).hU l
  · simp only [ho, if_neg]
    exact
      (h3TerminalSecondQForcingDerivativeLerayDataAt
        hH3 hClass ht j).hR l

/--
The named frozen channel is exactly the order-three radial convolution norm of
the two oriented scalar states.
-/
theorem h3TerminalSecondQForcingDerivativeRadialProductNormAt_eq_states
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) :
    h3TerminalSecondQForcingDerivativeRadialProductNormAt
        hH3 hClass ht j o k l
      =
    ‖h3RawProductConvolutionRadialFourierL2
        3
        (h3TerminalSecondQForcingDerivativeFirstStateAt
          hH3 hClass ht j o k)
        (h3TerminalSecondQForcingDerivativeSecondStateAt
          hH3 hClass ht j o l)
        (h3TerminalSecondQForcingDerivativeFirstStateAt_moment6_integrable
          hH3 hClass ht j o k)
        (h3TerminalSecondQForcingDerivativeSecondStateAt_moment6_integrable
          hH3 hClass ht j o l)‖ := by

  by_cases ho : o = 0

  · simp [
      h3TerminalSecondQForcingDerivativeRadialProductNormAt,
      h3TerminalSecondQForcingDerivativeFirstStateAt,
      h3TerminalSecondQForcingDerivativeSecondStateAt,
      ho
    ]

  · simp [
      h3TerminalSecondQForcingDerivativeRadialProductNormAt,
      h3TerminalSecondQForcingDerivativeFirstStateAt,
      h3TerminalSecondQForcingDerivativeSecondStateAt,
      ho
    ]

/-- Explicit Young state-mass envelope of a frozen second-q channel. -/
noncomputable def h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) : ℝ :=
  let F :=
    h3TerminalSecondQForcingDerivativeFirstStateAt
      hH3 hClass ht j o k
  let G :=
    h3TerminalSecondQForcingDerivativeSecondStateAt
      hH3 hClass ht j o l
  (
    ‖h3SpectralScalarRawFourierConjL2 F‖ *
      ‖h3SpectralScalarRawFourierL2 G‖
  )
    *
  (
    h3FourierMomentSplitCoefficient (6 : ℝ)
      *
    (
      h3SpectralScalarRawFourierMomentMass (6 : ℝ) F
        *
      h3SpectralScalarRawFourierL1Mass G
      +
      h3SpectralScalarRawFourierL1Mass F
        *
      h3SpectralScalarRawFourierMomentMass (6 : ℝ) G
    )
  )

theorem h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt_nonneg
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) :
    0 ≤
      h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt
        hH3 hClass ht j o k l := by

  let F :=
    h3TerminalSecondQForcingDerivativeFirstStateAt
      hH3 hClass ht j o k

  let G :=
    h3TerminalSecondQForcingDerivativeSecondStateAt
      hH3 hClass ht j o l

  let hF :
      H3RawFourierMomentIntegrable
        (((2 * 3 : ℕ) : ℝ))
        F := by
    dsimp only [F]
    simpa using
      h3TerminalSecondQForcingDerivativeFirstStateAt_moment6_integrable
        hH3 hClass ht j o k

  let hG :
      H3RawFourierMomentIntegrable
        (((2 * 3 : ℕ) : ℝ))
        G := by
    dsimp only [G]
    simpa using
      h3TerminalSecondQForcingDerivativeSecondStateAt_moment6_integrable
        hH3 hClass ht j o l

  have hBound :=
    norm_sq_h3RawProductConvolutionRadialFourierL2_le_stateMasses
      3 F G hF hG

  have hNonneg :
      0 ≤
        (
          ‖h3SpectralScalarRawFourierConjL2 F‖ *
            ‖h3SpectralScalarRawFourierL2 G‖
        )
          *
        (
          h3FourierMomentSplitCoefficient (((2 * 3 : ℕ) : ℝ))
            *
          (
            h3SpectralScalarRawFourierMomentMass
                (((2 * 3 : ℕ) : ℝ))
                F
              *
            h3SpectralScalarRawFourierL1Mass G
            +
            h3SpectralScalarRawFourierL1Mass F
              *
            h3SpectralScalarRawFourierMomentMass
                (((2 * 3 : ℕ) : ℝ))
                G
          )
        ) :=
    (sq_nonneg
      ‖h3RawProductConvolutionRadialFourierL2
          3 F G hF hG‖).trans
      hBound

  unfold h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt
  dsimp only

  simpa only [
    show (((2 * 3 : ℕ) : ℝ)) = (6 : ℝ) by norm_num
  ] using hNonneg

/--
The square of a frozen second-q radial product norm is bounded by its explicit
Young state-mass envelope.
-/
theorem sq_h3TerminalSecondQForcingDerivativeRadialProductNormAt_le_stateMassEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (j : Fin 3)
    (o : Fin 2)
    (k l : Fin 3) :
    (
      h3TerminalSecondQForcingDerivativeRadialProductNormAt
        hH3 hClass ht j o k l
    ) ^ 2
      ≤
    h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt
      hH3 hClass ht j o k l := by

  let F :=
    h3TerminalSecondQForcingDerivativeFirstStateAt
      hH3 hClass ht j o k

  let G :=
    h3TerminalSecondQForcingDerivativeSecondStateAt
      hH3 hClass ht j o l

  let hF :
      H3RawFourierMomentIntegrable
        (((2 * 3 : ℕ) : ℝ))
        F := by
    dsimp only [F]
    simpa using
      h3TerminalSecondQForcingDerivativeFirstStateAt_moment6_integrable
        hH3 hClass ht j o k

  let hG :
      H3RawFourierMomentIntegrable
        (((2 * 3 : ℕ) : ℝ))
        G := by
    dsimp only [G]
    simpa using
      h3TerminalSecondQForcingDerivativeSecondStateAt_moment6_integrable
        hH3 hClass ht j o l

  have hBound :=
    norm_sq_h3RawProductConvolutionRadialFourierL2_le_stateMasses
      3 F G hF hG

  rw [
    h3TerminalSecondQForcingDerivativeRadialProductNormAt_eq_states
      hH3 hClass ht j o k l
  ]

  unfold h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt
  dsimp only [F, G]

  simpa only [
    show (((2 * 3 : ℕ) : ℝ)) = (6 : ℝ) by norm_num
  ] using hBound

/--
Escape of one frozen second-q radial product norm forces escape of its explicit
Young state-mass envelope.
-/
theorem h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt_tendstoAtTop_of_productNorm_tendstoAtTop
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
            h3TerminalSecondQForcingDerivativeRadialProductNormAt
              hH3 hClass (hτ n) j o k l
        )
        atTop
        atTop) :
    Tendsto
      (
        fun n : ℕ =>
          h3TerminalSecondQForcingDerivativeStateMassEnvelopeAt
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
        h3TerminalSecondQForcingDerivativeRadialProductNormAt
          hH3 hClass (hτ n) j o k l :=
    hNormTop.eventually
      (eventually_gt_atTop R0)

  filter_upwards [hLarge] with n hn

  have hNormNonneg :
      0 ≤
        h3TerminalSecondQForcingDerivativeRadialProductNormAt
          hH3 hClass (hτ n) j o k l :=
    h3TerminalSecondQForcingDerivativeRadialProductNormAt_nonneg
      hH3 hClass (hτ n) j o k l

  have hSqBound :=
    sq_h3TerminalSecondQForcingDerivativeRadialProductNormAt_le_stateMassEnvelope
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
        h3TerminalSecondQForcingDerivativeRadialProductNormAt
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

end

end Euclidean
end Bridge
end PrimeTensor
