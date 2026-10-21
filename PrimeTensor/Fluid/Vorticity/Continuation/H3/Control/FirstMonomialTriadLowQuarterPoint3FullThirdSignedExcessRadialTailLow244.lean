import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSignedExcessDiffusionTransport244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Hilbert.Weighted.Old.Derivative.Split
import Mathlib.Tactic

/-!
# Exact radial tail plus low complement in the physical H³ signed moment source

The top dissipation is a sum of global fourth-radial Hilbert norm squares.
Its actual time derivative is the named Hilbert pairing. The established
radial-tail PDE balance identifies the derivative of each *natural* sharp
cutoff as heat diffusion plus the actual nonlinear Leray transfer.

The missing term in moving from tail to total is precisely the derivative
of the physical low-frequency complement D₃ - Tail₃(n). We keep this term
and prove an exact three-channel decomposition of the signed source X:

    X = [lower-order diffusion plus top-tail heat]
      + [order-two transport plus top-tail Leray transfer]
      + [derivative of low radial complement].

No vanishing low-frequency derivative, terminal decay, or uniform rate estimate
is assumed. This is a legitimate PDE decomposition at every fixed natural
frequency cutoff, with the residual made explicit rather than discarded.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1200000

/-- The actual physical low-radial complement of the top H³ dissipation,
with respect to the existing sharp natural Fourier tail at cutoff n+1. -/
noncomputable def h3PathTopFourierLowRadialComplement244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (n : ℕ) (s : ℝ) : ℝ :=
  h3TerminalPhysicalTopDissipation3Path hClass s -
    h3TerminalPhysicalTopDissipationNaturalRadialTailPath hH3 hClass n s

/-- Lower-order viscous production with the top-tail fifth-moment heat rate. -/
noncomputable def h3PathTopFourierTailDiffusionBackground244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (n : ℕ) : ℝ :=
  2 * velocityH3Energy2At u t * velocityH3DiffusionDerivative2At u t *
      (velocityH3Energy0At u t * h3TerminalPhysicalTopDissipation3Path hClass t) -
    velocityH3Energy2At u t ^ 2 *
      (velocityH3DiffusionDerivative0At u t *
          h3TerminalPhysicalTopDissipation3Path hClass t +
        velocityH3Energy0At u t *
          h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt
            hH3 hClass ht ((n : ℝ) + 1))

/-- Nonlinear production retained in order-two transport and the actual
sharp top-radial Leray transfer. -/
noncomputable def h3PathTopFourierTailNonlinearExcess244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (n : ℕ) : ℝ :=
  -(2 * velocityH3Energy2At u t * velocityH3TransportDerivative2At u t *
      (velocityH3Energy0At u t * h3TerminalPhysicalTopDissipation3Path hClass t)) -
    velocityH3Energy2At u t ^ 2 * velocityH3Energy0At u t *
      h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
        hH3 hClass ht ((n : ℝ) + 1)

/-- The signed correction is *exactly* the temporal derivative of low
fourth-radial Fourier mass, multiplied by its true middle/kinetic weights. -/
noncomputable def h3PathTopFourierLowRadialDerivativeCorrection244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (n : ℕ) (t : ℝ) : ℝ :=
  -(velocityH3Energy2At u t ^ 2 * velocityH3Energy0At u t *
      deriv (h3PathTopFourierLowRadialComplement244 hH3 hClass n) t)

/-- The physical low-frequency top-dissipation complement is differentiable
at each strict time. Its derivative is the global fourth-radial Hilbert
pairing minus the *proven* localized heat-plus-Leray PDE rate. -/
theorem h3Path_topFourierLowRadialComplement_hasDerivAt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (n : ℕ) :
    HasDerivAt (h3PathTopFourierLowRadialComplement244 hH3 hClass n)
      (h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t -
        (h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt
          hH3 hClass ht ((n : ℝ) + 1) +
         h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
          hH3 hClass ht ((n : ℝ) + 1))) t := by
  have hGlobal : HasDerivAt
      (h3TerminalPhysicalTopDissipation3Path hClass)
      (h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t) t := by
    exact h3TerminalPhysicalTopDissipation3Path_hasDerivAt hH3 hClass ht
  have hBalance :=
    h3TerminalPhysicalTopDissipationNaturalRadialTailLocalizedPDEBalanceAtEndpoint_closed
      hH3 hClass n t ht
  have hTail : HasDerivAt
      (h3TerminalPhysicalTopDissipationNaturalRadialTailPath hH3 hClass n)
      (h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt
          hH3 hClass ht ((n : ℝ) + 1) +
       h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
          hH3 hClass ht ((n : ℝ) + 1)) t := by
    exact hBalance.1.hasDerivAt.congr_deriv hBalance.2
  have hSub := hGlobal.sub hTail
  rw [Pi.sub_def] at hSub
  exact hSub

/-- Exact equality of the true top-dissipation derivative and its high
heat + high nonlinear + low correction components. -/
theorem h3Path_fourthRadialPairing_eq_tailHeat_add_transfer_add_low244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (n : ℕ) :
    h3PathTopFourierFourthRadialPairingRate244 hH3 hClass t =
      h3TerminalPhysicalTopDissipationRadialTailDiffusionRateAt
        hH3 hClass ht ((n : ℝ) + 1) +
      h3TerminalPhysicalTopDissipationRadialTailNonlinearTransferRateAt
        hH3 hClass ht ((n : ℝ) + 1) +
      deriv (h3PathTopFourierLowRadialComplement244 hH3 hClass n) t := by
  have hDeriv := (h3Path_topFourierLowRadialComplement_hasDerivAt244
    hH3 hClass ht n).deriv
  linarith only [hDeriv]

/-- The actual physical signed excess is exactly a three-channel quantity:
order-zero/order-two diffusion plus high radial heat; order-two transport plus
high radial Leray; and the exact derivative of the low radial complement. -/
theorem h3Path_signedExcess_eq_tailHeat_add_Leray_add_low244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (n : ℕ) :
    h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass t =
      h3PathTopFourierTailDiffusionBackground244 hH3 hClass ht n +
      h3PathTopFourierTailNonlinearExcess244 hH3 hClass ht n +
      h3PathTopFourierLowRadialDerivativeCorrection244 hH3 hClass n t := by
  have hOld := h3Path_signedExcess_eq_diffusionHilbert_add_transport244
    hH3 hClass ht
  have hTransport := h3Path_nonlinearTransportExcess_eq_orderTwo244
    hH3 hClass ht
  have hTop := h3Path_fourthRadialPairing_eq_tailHeat_add_transfer_add_low244
    hH3 hClass ht n
  rw [hOld, hTransport]
  unfold h3PathTopFourierDiffusionHilbertBackground244
    h3PathTopFourierTailDiffusionBackground244
    h3PathTopFourierTailNonlinearExcess244
    h3PathTopFourierLowRadialDerivativeCorrection244
  rw [hTop]
  ring

/-- In particular, the exactly normalized physical spectral-concentration
source is the sum of the three genuine radial PDE contributions. -/
theorem h3Path_normalizedExcessRate_eq_tailHeat_add_Leray_add_low244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (n : ℕ) :
    h3PathTopFourierNormalizedSignedExcessRate244 hH3 hClass t =
      (h3PathTopFourierTailDiffusionBackground244 hH3 hClass ht n +
       h3PathTopFourierTailNonlinearExcess244 hH3 hClass ht n +
       h3PathTopFourierLowRadialDerivativeCorrection244 hH3 hClass n t) /
        (velocityH3Energy0At u t *
          h3TerminalPhysicalTopDissipation3Path hClass t) ^ 2 := by
  unfold h3PathTopFourierNormalizedSignedExcessRate244
  rw [h3Path_signedExcess_eq_tailHeat_add_Leray_add_low244 hH3 hClass ht n]

/-- Near-sharp Young absorption forces the complete localized PDE source
at some interior time, including the explicit low-frequency derivative. -/
theorem h3Path_nearYoung_forces_tailHeat_Leray_low_secant244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ)
    (n : ℕ) :
    ∃ r : ℝ, ∃ hr : r ∈ Set.Ioo s t,
      (h3PathTopFourierNormalizedRadialVariance244 u s -
        (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t)) /
          (t - s) ≤
        (h3PathTopFourierTailDiffusionBackground244 hH3 hClass
          ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩ n +
         h3PathTopFourierTailNonlinearExcess244 hH3 hClass
          ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩ n +
         h3PathTopFourierLowRadialDerivativeCorrection244 hH3 hClass n r) /
          (velocityH3Energy0At u r *
            h3TerminalPhysicalTopDissipation3Path hClass r) ^ 2 := by
  obtain ⟨r, hr, hRate⟩ :=
    h3Path_normalizedVariance_exists_exactSignedExcessSecant244
      hH3 hClass hs ht hst hMass hD
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  rw [h3Path_normalizedExcessRate_eq_tailHeat_add_Leray_add_low244
    hH3 hClass hrClass n] at hRate
  have hYoung := h3Path_topFourier_normalizedVariance_nearYoung_upper244
    hH3 hClass ht (hMass t ⟨hst.le, le_refl t⟩)
    hK (hD t ⟨hst.le, le_refl t⟩) hNear
  refine ⟨r, hr, ?_⟩
  rw [hRate]
  apply (div_le_div_iff_of_pos_right (sub_pos.mpr hst)).2
  linarith only [hYoung]

end
end PrimeTensor.FirstMonomialTriad
