import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdSignedExcessPDETerminal244
import PrimeTensor.Fluid.Vorticity.H3.Energy.PDE.Split
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Pairing.PDE.L2.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Pressure.Cancel.Zero
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalLowerOrderSignedTransport
import Mathlib.Tactic

/-!
# Exact diffusion/transport decomposition of the physical H³ concentration source

Let A = E₀ D₃ and R = 1 - E₂²/A.  The actual derivative is
  R' = -(B + N)/A²,
where B collects the two linear diffusion energy contributions together
with the genuine fourth-radial Hilbert derivative D₃', and N is the
signed order-zero/order-two nonlinear transport contribution.

The pressure contributions vanish by the already-closed physical H³
cancellation theorems.  All moment pairing integrability and higher
spatial derivative splittings come from the actual H³ energy class.

An exact secant and near-Young deficit impose a lower bound on B+N.
If the normalized B part is bounded above by M, the same secant forces
the normalized nonlinear transport source N to exceed the required
spectral concentration rate minus M at some interior physical time.

There is NO claim here that the linear-plus-Hilbert background is bounded,
or that nonlinear transport is sign-definite or globally controlled.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1200000

/-- The diffusion energy contribution together with the actual fourth-radial
Hilbert derivative. This is NOT a purely heat-flow term because D₃' contains
the full physical nonlinear PDE forcing. -/
noncomputable def h3PathTopFourierDiffusionHilbertBackground244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (r : ℝ) : ℝ :=
  2 * velocityH3Energy2At u r * velocityH3DiffusionDerivative2At u r *
      (velocityH3Energy0At u r *
        h3TerminalPhysicalTopDissipation3Path hClass r) -
    velocityH3Energy2At u r ^ 2 *
      (velocityH3DiffusionDerivative0At u r *
          h3TerminalPhysicalTopDissipation3Path hClass r +
        velocityH3Energy0At u r *
          h3PathTopFourierFourthRadialPairingRate244 hH3 hClass r)

/-- The genuine signed order-zero/order-two nonlinear transport source
contributing to the evolution of the normalized radial Fourier variance. -/
noncomputable def h3PathTopFourierNonlinearTransportExcess244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (r : ℝ) : ℝ :=
  -(2 * velocityH3Energy2At u r *
      velocityH3TransportDerivative2At u r *
      (velocityH3Energy0At u r *
        h3TerminalPhysicalTopDissipation3Path hClass r)) +
    velocityH3Energy2At u r ^ 2 *
      (velocityH3TransportDerivative0At u r *
        h3TerminalPhysicalTopDissipation3Path hClass r)

/-- Actual physical signed moment production splits EXACTLY into its
viscous/Hilbert background and signed nonlinear transport. No new spatial
regularity, pressure-cancellation or integrability assumption is added. -/
theorem h3Path_signedExcess_eq_diffusionHilbert_add_transport244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierSignedMiddleMomentExcess244 hH3 hClass t =
      h3PathTopFourierDiffusionHilbertBackground244 hH3 hClass t +
        h3PathTopFourierNonlinearTransportExcess244 hClass t := by
  let p : PrimeTensor.SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3EnergyClassSplitPressureAt hClass ht
  have hPDE : PreterminalNavierStokes3
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) p T := by
    dsimp only [p]
    exact h3EnergyClassSplitPressureAt_navierStokes hClass ht
  have hHigher : HigherOrderMomentumRHSSplitsAt
      (PrimeTensor.Bridge.logSpaceTimeVectorField u) p t := by
    dsimp only [p]
    exact h3EnergyClassSplitPressureAt_momentumRHSSplits hClass ht
  have hInt : H3PDEPairingIntegrableAt u p t := by
    dsimp only [p]
    exact h3PathEnergyClassProducesPDEPairingIntegrability_closed
      u T hH3 a hClass t ht
  have hZeroSplit := velocityH3PDEDerivative0At_eq_split hInt
  have hTwoSplit := velocityH3PDEDerivative2At_eq_split hHigher hInt
  have hPressure0 : velocityH3PressureDerivative0At u p t = 0 := by
    dsimp only [p]
    exact h3PathEnergyClassProducesPressure0Cancellation_closed
      u T hH3 a hClass t ht
  have hPressure2 : velocityH3PressureDerivative2At u p t = 0 := by
    dsimp only [p]
    exact (h3PathEnergyClassProducesPressureHigherCancellation_closed
      u T hH3 a hClass t ht).2.1
  have hSource := h3Path_signedMiddleMomentExcess_eq_PDE244
    hH3 hClass ht hPDE
  rw [hSource]
  unfold h3PathTopFourierPDESignedMiddleMomentExcess244
    h3PathTopFourierDiffusionHilbertBackground244
    h3PathTopFourierNonlinearTransportExcess244
  rw [hZeroSplit, hTwoSplit, hPressure0, hPressure2]
  ring

/-- The zeroth-order advective energy flux cancels on an actual physical
H³ energy-class slice. Hence ONLY the signed order-two transport pairing
remains in the nonlinear contribution from E₀' and E₂'. -/
theorem h3Path_nonlinearTransportExcess_eq_orderTwo244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierNonlinearTransportExcess244 hClass t =
      -(2 * velocityH3Energy2At u t *
        velocityH3TransportDerivative2At u t *
        (velocityH3Energy0At u t *
          h3TerminalPhysicalTopDissipation3Path hClass t)) := by
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hInt : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs
  let h : ℝ → ℝ := h3PathCanonicalSqrtEnergyGradientEnvelope u
  have hGradient : VelocityGradientEnvelope u h t := by
    simpa only [h] using
      h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass ht
  have hIBP0 : H3TransportEnergyIntegrationByPartsAt u t :=
    h3TransportEnergyIntegrationByPartsAt_of_energyClass
      hClass ht hInt hGradient
  have hFlux0 : H3TransportEnergyFluxVanishesAt u t :=
    h3TransportEnergyFluxVanishesAt_of_integrationByParts hIBP0
  have hTransport0 : velocityH3TransportDerivative0At u t = 0 :=
    velocityH3TransportDerivative0At_eq_zero_of_energyClass hClass ht hFlux0
  unfold h3PathTopFourierNonlinearTransportExcess244
  rw [hTransport0]
  ring

/-- Exact normalized concentration rate in physically split form. -/
theorem h3Path_normalizedExcessRate_eq_diffusionHilbert_add_transport244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierNormalizedSignedExcessRate244 hH3 hClass t =
      (h3PathTopFourierDiffusionHilbertBackground244 hH3 hClass t +
        h3PathTopFourierNonlinearTransportExcess244 hClass t) /
        (velocityH3Energy0At u t *
          h3TerminalPhysicalTopDissipation3Path hClass t) ^ 2 := by
  unfold h3PathTopFourierNormalizedSignedExcessRate244
  rw [h3Path_signedExcess_eq_diffusionHilbert_add_transport244 hH3 hClass ht]

/-- A small physical Young gap at t forces an actual intermediate-time
normalized sum of diffusion/Hilbert and nonlinear transport production.
This uses the exact secant, not an assumed time integral. -/
theorem h3Path_nearYoung_forces_diffusionTransportSecant244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    ∃ r ∈ Set.Ioo s t,
      (h3PathTopFourierNormalizedRadialVariance244 u s -
        (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t)) /
        (t - s) ≤
        (h3PathTopFourierDiffusionHilbertBackground244 hH3 hClass r +
          h3PathTopFourierNonlinearTransportExcess244 hClass r) /
          (velocityH3Energy0At u r *
            h3TerminalPhysicalTopDissipation3Path hClass r) ^ 2 := by
  obtain ⟨r, hr, hRate⟩ :=
    h3Path_normalizedVariance_exists_exactSignedExcessSecant244
      hH3 hClass hs ht hst hMass hD
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  rw [h3Path_normalizedExcessRate_eq_diffusionHilbert_add_transport244
    hH3 hClass hrClass] at hRate
  have hYoung := h3Path_topFourier_normalizedVariance_nearYoung_upper244
    hH3 hClass ht (hMass t ⟨hst.le, le_refl t⟩)
    hK (hD t ⟨hst.le, le_refl t⟩) hNear
  refine ⟨r, hr, ?_⟩
  rw [hRate]
  apply (div_le_div_iff_of_pos_right (sub_pos.mpr hst)).2
  linarith only [hYoung]

/-- The first rigorous transport burden: if the normalized diffusion/Hilbert
background is at most M throughout the physical interval, the NECESSARY
nonlinear transport rate reaches the excess secant threshold minus M.
The background ceiling is explicit and is NOT asserted automatically. -/
theorem h3Path_nearYoung_forces_nonlinearTransport_after_backgroundCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t K δ M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ)
    (hBackground : ∀ r, r ∈ Set.Ioo s t →
      h3PathTopFourierDiffusionHilbertBackground244 hH3 hClass r /
        (velocityH3Energy0At u r *
          h3TerminalPhysicalTopDissipation3Path hClass r) ^ 2 ≤ M) :
    ∃ r ∈ Set.Ioo s t,
      (h3PathTopFourierNormalizedRadialVariance244 u s -
        (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t)) /
        (t - s) - M ≤
      h3PathTopFourierNonlinearTransportExcess244 hClass r /
        (velocityH3Energy0At u r *
          h3TerminalPhysicalTopDissipation3Path hClass r) ^ 2 := by
  obtain ⟨r, hr, hRate⟩ :=
    h3Path_nearYoung_forces_diffusionTransportSecant244
      hH3 hClass hs ht hst hMass hD hK hNear
  have hB := hBackground r hr
  refine ⟨r, hr, ?_⟩
  rw [add_div] at hRate
  linarith only [hRate, hB]

/-- The required nonlinearity is an *order-two transport pairing*:
under a background ceiling it must produce the remaining secant rate.
The pressure and order-zero advective pairing are already eliminated. -/
theorem h3Path_nearYoung_forces_orderTwoTransport_after_backgroundCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t K δ M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ)
    (hBackground : ∀ r, r ∈ Set.Ioo s t →
      h3PathTopFourierDiffusionHilbertBackground244 hH3 hClass r /
        (velocityH3Energy0At u r *
          h3TerminalPhysicalTopDissipation3Path hClass r) ^ 2 ≤ M) :
    ∃ r ∈ Set.Ioo s t,
      (h3PathTopFourierNormalizedRadialVariance244 u s -
        (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t)) /
        (t - s) - M ≤
      -(2 * velocityH3Energy2At u r *
        velocityH3TransportDerivative2At u r *
        (velocityH3Energy0At u r *
          h3TerminalPhysicalTopDissipation3Path hClass r)) /
        (velocityH3Energy0At u r *
          h3TerminalPhysicalTopDissipation3Path hClass r) ^ 2 := by
  obtain ⟨r, hr, hBound⟩ :=
    h3Path_nearYoung_forces_nonlinearTransport_after_backgroundCeiling244
      hH3 hClass hs ht hst hMass hD hK hNear hBackground
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  rw [h3Path_nonlinearTransportExcess_eq_orderTwo244
    hH3 hClass hrClass] at hBound
  exact ⟨r, hr, hBound⟩

end
end PrimeTensor.FirstMonomialTriad
