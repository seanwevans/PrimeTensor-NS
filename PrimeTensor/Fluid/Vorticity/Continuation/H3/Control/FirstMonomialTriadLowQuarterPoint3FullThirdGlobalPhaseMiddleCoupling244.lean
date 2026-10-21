import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGlobalSignedPhaseDefect244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGlobalViscousCeiling244
import Mathlib.Tactic

/-!
# Exact phase-defect orientation in the normalized middle/top Fourier evolution

The previous phase theorem states D3' + M5 + P = M3, with P >= 0.
Substituting this into the exact physical signed concentration numerator gives

  X/A^2 = C_middle + C_top,       A = E0 D3,
  C_middle = [2 E2 (L2 - T2) A - E2^2 L0 D3]/A^2,
  C_top = E2^2 E0 (M5 + P - M3)/A^2.

In particular the phase defect P contributes POSITIVELY to the signed
concentration source: because R' = -X/A^2, P is not automatically a
regularizing term. This is a critical orientation audit, not a new
anti-concentration estimate.

We also bound C_middle by the physical kinetic diffusion loss plus the
previously proved 36 h(t) order-two transport budget, without charging
any fifth moment to C_middle. A near-Young secant therefore forces the
signed M5 + P - M3 channel to supply the residual rate.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1800000

/-- Normalized, jointly signed order-two transport and order-zero/two
heat source, prior to adding the fourth-radial PDE derivative. -/
noncomputable def h3PathTopFourierGlobalMiddleCouplingNormalizedRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) : ℝ :=
  let A := velocityH3Energy0At u t *
    h3TerminalPhysicalTopDissipation3Path hClass t
  (2 * velocityH3Energy2At u t *
      (velocityH3DiffusionDerivative2At u t -
        velocityH3TransportDerivative2At u t) * A -
    velocityH3Energy2At u t ^ 2 *
      velocityH3DiffusionDerivative0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t) / A ^ 2

/-- Signed fourth-radial contribution after keeping the complete phase
remainder, rather than replacing the actual Leray transfer by an absolute
forcing majorant. -/
noncomputable def h3PathTopFourierGlobalTopPhaseNormalizedRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) : ℝ :=
  (velocityH3Energy2At u t ^ 2 * velocityH3Energy0At u t *
    (h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht +
      h3PathTopFourierGlobalSignedPhaseDefect244 hH3 hClass t ht -
      h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
        hH3 hClass ht)) /
    (velocityH3Energy0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t) ^ 2

/-- The strictly nonnegative weight with which the true phase defect
contributes to normalized spectral concentration. -/
noncomputable def h3PathTopFourierGlobalPhasePenaltyNormalizedRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) : ℝ :=
  (velocityH3Energy2At u t ^ 2 * velocityH3Energy0At u t *
    h3PathTopFourierGlobalSignedPhaseDefect244 hH3 hClass t ht) /
    (velocityH3Energy0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t) ^ 2

/-- Exact signed variance-production decomposition linked to the physical
fourth-radial phase defect. No sign is discarded. -/
theorem h3Path_normalizedExcessRate_eq_middleCoupling_add_topPhase244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierNormalizedSignedExcessRate244 hH3 hClass t =
      h3PathTopFourierGlobalMiddleCouplingNormalizedRate244 hClass t +
      h3PathTopFourierGlobalTopPhaseNormalizedRate244 hH3 hClass t ht := by
  have hPhase :=
    h3Path_globalSignedPhaseDefect_eq_fifth_add_cubic_sub_Leray244
      hH3 hClass ht
  have hLeray :
      h3PathTopFourierGlobalLerayRate244 hH3 t
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ =
        h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht +
          h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
            hH3 hClass ht -
          h3PathTopFourierGlobalSignedPhaseDefect244 hH3 hClass t ht := by
    linarith only [hPhase]
  rw [h3Path_normalizedExcessRate_eq_globalHeat_add_Leray244
    hH3 hClass ht]
  unfold h3PathTopFourierGlobalDiffusionExcess244
    h3PathTopFourierGlobalNonlinearExcess244
    h3PathTopFourierGlobalMiddleCouplingNormalizedRate244
    h3PathTopFourierGlobalTopPhaseNormalizedRate244
  dsimp only
  rw [h3Path_globalHeatRate_eq_negTwoFifthMass244 hH3 hClass ht,
    hLeray]
  ring

/-- The genuine phase defect contributes with a NONNEGATIVE coefficient
to the normalized signed concentration rate. -/
theorem h3Path_globalPhasePenaltyNormalizedRate_nonneg244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t) :
    0 ≤ h3PathTopFourierGlobalPhasePenaltyNormalizedRate244
      hH3 hClass t ht := by
  unfold h3PathTopFourierGlobalPhasePenaltyNormalizedRate244
  apply div_nonneg
  · exact mul_nonneg
      (mul_nonneg (sq_nonneg _) hMass.le)
      (h3Path_globalSignedPhaseDefect_nonneg244 hH3 hClass ht)
  · exact sq_nonneg _

/-- Exact decomposition of the top phase rate into the phase-free
fifth-minus-cubic moment balance and a positive phase penalty. -/
theorem h3Path_globalTopPhaseRate_eq_phaseFree_add_penalty244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierGlobalTopPhaseNormalizedRate244 hH3 hClass t ht =
      (velocityH3Energy2At u t ^ 2 * velocityH3Energy0At u t *
        (h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht -
          h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
            hH3 hClass ht)) /
        (velocityH3Energy0At u t *
          h3TerminalPhysicalTopDissipation3Path hClass t) ^ 2 +
      h3PathTopFourierGlobalPhasePenaltyNormalizedRate244
        hH3 hClass t ht := by
  unfold h3PathTopFourierGlobalTopPhaseNormalizedRate244
    h3PathTopFourierGlobalPhasePenaltyNormalizedRate244
  ring

/-- At positive kinetic mass, retaining a nonnegative phase defect can
only increase the signed top contribution to normalized concentration. -/
theorem h3Path_globalTopPhaseRate_ge_phaseFree244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t) :
    (velocityH3Energy2At u t ^ 2 * velocityH3Energy0At u t *
      (h3PathTopFourierGlobalFifthMass244 hH3 hClass t ht -
        h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
          hH3 hClass ht)) /
      (velocityH3Energy0At u t *
        h3TerminalPhysicalTopDissipation3Path hClass t) ^ 2 ≤
    h3PathTopFourierGlobalTopPhaseNormalizedRate244 hH3 hClass t ht := by
  rw [h3Path_globalTopPhaseRate_eq_phaseFree_add_penalty244]
  exact le_add_of_nonneg_right
    (h3Path_globalPhasePenaltyNormalizedRate_nonneg244
      hH3 hClass ht hMass)

/-- Scalar kinetic-plus-order-two transport bound independent of M5.
The two estimates used here are previously established Fourier Cauchy
and order-two transport bounds, plus the signed lower diffusion pairing. -/
theorem h3_middleCoupling_scalar_le_kineticGradientBudget244
    (E2 L0 L2 T2 D A h : ℝ)
    (hE2 : 0 ≤ E2) (hA : 0 < A) (hD : 0 ≤ D)
    (hL0 : L0 ≤ 0) (hL2 : L2 ≤ 0) (hh : 0 ≤ h)
    (hCauchy : E2 ^ 2 ≤ A)
    (hTransport : |T2| ≤ 18 * h * E2) :
    (2 * E2 * (L2 - T2) * A - E2 ^ 2 * L0 * D) / A ^ 2 ≤
      -(L0 * D) / A + 36 * h := by
  have hP : L0 * D ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hL0 hD
  have hDiff := h3_normalizedDiffusion_scalar_le_viscousCeiling244
    E2 L2 A (L0 * D) hE2 hL2 hA hCauchy hP
  have hAdv := h3_normalizedOrderTwoTransport_scalar_le_thirtySix244
    E2 T2 A h hE2 hA hh hCauchy hTransport
  have hSplit :
      (2 * E2 * (L2 - T2) * A - E2 ^ 2 * L0 * D) / A ^ 2 =
        (2 * E2 * L2 * A - E2 ^ 2 * (L0 * D)) / A ^ 2 +
        -(2 * E2 * T2 * A) / A ^ 2 := by
    ring
  rw [hSplit]
  exact add_le_add hDiff hAdv

/-- Physical, *fifth-moment-free* ceiling on the middle-moment coupling.
The only positive costs are kinetic diffusion loss and the proved 36 h. -/
theorem h3Path_globalMiddleCoupling_le_kineticGradientBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t) :
    h3PathTopFourierGlobalMiddleCouplingNormalizedRate244 hClass t ≤
      -(velocityH3DiffusionDerivative0At u t *
        h3TerminalPhysicalTopDissipation3Path hClass t) /
        (velocityH3Energy0At u t *
          h3TerminalPhysicalTopDissipation3Path hClass t) +
      36 * h3PathCanonicalSqrtEnergyGradientEnvelope u t := by
  let h : ℝ → ℝ := h3PathCanonicalSqrtEnergyGradientEnvelope u
  have hGradient : VelocityGradientEnvelope u h t := by
    simpa only [h] using
      h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass ht
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hH3At : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs
  have hIBP2 : H3SecondDerivativeTransportIntegrationByPartsAt u t :=
    h3SecondDerivativeTransportIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradient
  have hFlux2 : H3SecondDerivativeTransportFluxVanishesAt u t :=
    h3SecondDerivativeTransportFluxVanishesAt_of_integrationByParts hIBP2
  have hPure : H3OrderTwoPureTransportPairingIntegrableAt u t :=
    h3OrderTwoPureTransportPairingIntegrableAt_of_integrationByParts
      hClass ht hIBP2
  have hPair : H3OrderTwoTransportPairingIntegrableAt u t :=
    h3OrderTwoTransportPairingIntegrableAt_of_pure
      hClass ht hH3At hGradient hPure
  have hTransport :
      |velocityH3TransportDerivative2At u t| ≤
        18 * h t * velocityH3Energy2At u t :=
    velocityH3TransportDerivative2At_le_gradientEnvelope
      hClass ht hFlux2 hPair hH3At hGradient
  have hh : 0 ≤ h t := by
    dsimp only [h, h3PathCanonicalSqrtEnergyGradientEnvelope]
    exact mul_nonneg
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)
  have hIBP : H3DiffusionIntegrationByPartsAt u t :=
    h3PathEnergyClassProducesDiffusionIntegrationByParts_closed
      u T hH3 a hClass t ht
  have hL0 : velocityH3DiffusionDerivative0At u t ≤ 0 := by
    rw [velocityH3DiffusionDerivative0At_eq_neg_two_mul_dissipation0 hIBP]
    have h0 := velocityH3Dissipation0At_nonneg u t
    linarith only [h0]
  have hL2 : velocityH3DiffusionDerivative2At u t ≤ 0 := by
    rw [velocityH3DiffusionDerivative2At_eq_neg_two_mul_dissipation2 hIBP]
    have h2 := velocityH3Dissipation2At_nonneg u t
    linarith only [h2]
  have hTop := h3TerminalPhysicalTopDissipation3Path_eq hClass ht
  have hTopPos : 0 < h3TerminalPhysicalTopDissipation3Path hClass t := by
    rw [hTop]
    exact hD
  have hA : 0 < velocityH3Energy0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t :=
    mul_pos hMass hTopPos
  have hE2 : 0 ≤ velocityH3Energy2At u t :=
    velocityH3Energy2At_nonneg u t
  have hMoment :=
    (h3Path_topFourier_normalizedMoment_strictRange244
      hH3 hClass ht hMass hD).2.2
  have hCauchy : velocityH3Energy2At u t ^ 2 ≤
      velocityH3Energy0At u t *
        h3TerminalPhysicalTopDissipation3Path hClass t := by
    unfold h3PathTopFourierNormalizedMiddleMoment244 at hMoment
    have hBound := le_of_lt hMoment
    have hDenOld : 0 < velocityH3Energy0At u t *
        velocityH3Dissipation3At u t := mul_pos hMass hD
    have hBound' := (div_le_iff₀ hDenOld).mp hBound
    rw [hTop]
    simpa only [one_mul] using hBound'
  unfold h3PathTopFourierGlobalMiddleCouplingNormalizedRate244
  dsimp only
  exact h3_middleCoupling_scalar_le_kineticGradientBudget244
    (velocityH3Energy2At u t)
    (velocityH3DiffusionDerivative0At u t)
    (velocityH3DiffusionDerivative2At u t)
    (velocityH3TransportDerivative2At u t)
    (h3TerminalPhysicalTopDissipation3Path hClass t)
    (velocityH3Energy0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t)
    (h t) hE2 hA hTopPos.le hL0 hL2 hh hCauchy hTransport

/-- A near-Young secant must be supplied by the SIGNED fifth-plus-phase-minus-
cubic source after only kinetic diffusion and order-two transport costs.
This is an obstruction identity and necessary inequality, not exclusion. -/
theorem h3Path_nearYoung_forces_signedTopPhase_after_middleBudget244
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
      K * velocityH3Energy3At u t ≤ δ) :
    ∃ r : ℝ, ∃ hr : r ∈ Set.Ioo s t,
      (h3PathTopFourierNormalizedRadialVariance244 u s -
        (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t)) /
          (t - s) -
        36 * h3PathCanonicalSqrtEnergyGradientEnvelope u r +
        (velocityH3DiffusionDerivative0At u r *
          h3TerminalPhysicalTopDissipation3Path hClass r) /
          (velocityH3Energy0At u r *
            h3TerminalPhysicalTopDissipation3Path hClass r) ≤
      h3PathTopFourierGlobalTopPhaseNormalizedRate244 hH3 hClass r
        ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩ := by
  obtain ⟨r, hr, hRate⟩ :=
    h3Path_normalizedVariance_exists_exactSignedExcessSecant244
      hH3 hClass hs ht hst hMass hD
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  have hrClosed : r ∈ Set.Icc s t := ⟨hr.1.le, hr.2.le⟩
  have hExact := h3Path_normalizedExcessRate_eq_middleCoupling_add_topPhase244
    hH3 hClass hrClass
  rw [hExact] at hRate
  have hYoung := h3Path_topFourier_normalizedVariance_nearYoung_upper244
    hH3 hClass ht (hMass t ⟨hst.le, le_refl t⟩)
    hK (hD t ⟨hst.le, le_refl t⟩) hNear
  have hSecant :
      (h3PathTopFourierNormalizedRadialVariance244 u s -
        (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t)) /
          (t - s) ≤
      h3PathTopFourierGlobalMiddleCouplingNormalizedRate244 hClass r +
        h3PathTopFourierGlobalTopPhaseNormalizedRate244
          hH3 hClass r hrClass := by
    rw [hRate]
    exact (div_le_div_iff_of_pos_right (sub_pos.mpr hst)).2
      (by linarith only [hYoung])
  have hMiddle := h3Path_globalMiddleCoupling_le_kineticGradientBudget244
    hH3 hClass hrClass (hMass r hrClosed) (hD r hrClosed)
  -- `linarith` treats a division by an unknown real expression as an
  -- atomic term.  Normalize the negated quotient first, so the signed
  -- kinetic diffusion contribution is literally the same atom on both
  -- sides of the secant comparison.
  have hNegDiv :
      -(velocityH3DiffusionDerivative0At u r *
        h3TerminalPhysicalTopDissipation3Path hClass r) /
        (velocityH3Energy0At u r *
          h3TerminalPhysicalTopDissipation3Path hClass r) =
      -((velocityH3DiffusionDerivative0At u r *
        h3TerminalPhysicalTopDissipation3Path hClass r) /
        (velocityH3Energy0At u r *
          h3TerminalPhysicalTopDissipation3Path hClass r)) := by
    ring
  rw [hNegDiv] at hMiddle
  refine ⟨r, hr, ?_⟩
  linarith only [hSecant, hMiddle]

end
end PrimeTensor.FirstMonomialTriad
