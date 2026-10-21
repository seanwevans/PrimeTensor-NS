import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGlobalZeroCutoff244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalLowerOrderSignedTransport
import Mathlib.Tactic

/-!
# Order-two transport cannot supply unlimited normalized Fourier concentration

The actual global fourth-radial derivative is now heat plus signed Leray
transfer, with no low-frequency remainder.  Separate the normalized physical
spectral concentration rate into a global heat/moment part, the order-two
transport part, and the fourth-radial Leray part.

The physical H³ order-two transport commutator satisfies |T₂| ≤ 18 h E₂,
with h = C₁ sqrt(E_H3).  The true Fourier first-Cauchy inequality gives
E₂² ≤ E₀ D₃.  Consequently the normalized *signed* order-two contribution
cannot exceed 36 h.  Thus an exact near-Young variance secant must be
supplied by the global heat/moment contribution plus top Leray transfer,
after the explicit finite order-two allowance.

No upper bound is asserted for the global nonlinear Leray transfer, and
nothing here asserts that Young saturation or a terminal singularity occurs.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1400000

/-- The normalized *heat/moment* part of the actual signed source. -/
noncomputable def h3PathTopFourierGlobalDiffusionNormalizedRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) : ℝ :=
  h3PathTopFourierGlobalDiffusionExcess244 hH3 hClass t ht /
    (velocityH3Energy0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t) ^ 2

/-- Actual order-two nonlinear transport contribution, in exact squared
kinetic/top-dissipation normalization, with its sign retained. -/
noncomputable def h3PathTopFourierGlobalOrderTwoNormalizedRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) : ℝ :=
  -(2 * velocityH3Energy2At u t *
      velocityH3TransportDerivative2At u t *
      (velocityH3Energy0At u t *
        h3TerminalPhysicalTopDissipation3Path hClass t)) /
    (velocityH3Energy0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t) ^ 2

/-- The fourth-radial Leray transfer contribution to the normalized
spectral concentration rate, retaining its actual signed Fourier integral. -/
noncomputable def h3PathTopFourierGlobalLerayNormalizedRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) : ℝ :=
  -(velocityH3Energy2At u t ^ 2 * velocityH3Energy0At u t *
      h3PathTopFourierGlobalLerayRate244 hH3 t
        ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩) /
    (velocityH3Energy0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t) ^ 2

/-- Exact three-way normalized decomposition; no new PDE hypothesis. -/
theorem h3Path_normalizedSignedExcess_eq_globalThreeChannels244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathTopFourierNormalizedSignedExcessRate244 hH3 hClass t =
      h3PathTopFourierGlobalDiffusionNormalizedRate244 hH3 hClass t ht +
      h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass t +
      h3PathTopFourierGlobalLerayNormalizedRate244 hH3 hClass t ht := by
  rw [h3Path_normalizedExcessRate_eq_globalHeat_add_Leray244
    hH3 hClass ht]
  unfold h3PathTopFourierGlobalDiffusionNormalizedRate244
    h3PathTopFourierGlobalOrderTwoNormalizedRate244
    h3PathTopFourierGlobalLerayNormalizedRate244
    h3PathTopFourierGlobalNonlinearExcess244
  dsimp only
  ring

/-- Scalar core: the order-two commutator bound and the first spectral
Cauchy inequality give a dimension-free upper rate 36 h. -/
theorem h3_normalizedOrderTwoTransport_scalar_le_thirtySix244
    (E2 T2 A h : ℝ)
    (hE2 : 0 ≤ E2) (hA : 0 < A) (hh : 0 ≤ h)
    (hCauchy : E2 ^ 2 ≤ A)
    (hTransport : |T2| ≤ 18 * h * E2) :
    -(2 * E2 * T2 * A) / A ^ 2 ≤ 36 * h := by
  have hLow : -T2 ≤ 18 * h * E2 := by
    have hAbs := (abs_le.mp hTransport).1
    linarith only [hAbs]
  have hFactor : 0 ≤ 2 * E2 * A :=
    mul_nonneg (mul_nonneg (by norm_num) hE2) hA.le
  have hScaled := mul_le_mul_of_nonneg_left hLow hFactor
  have hPosScale : 0 ≤ 36 * h * A :=
    mul_nonneg (mul_nonneg (by norm_num) hh) hA.le
  have hCauchyScaled := mul_le_mul_of_nonneg_left hCauchy hPosScale
  have hNumerator : -(2 * E2 * T2 * A) ≤ (36 * h) * A ^ 2 := by
    nlinarith only [hScaled, hCauchyScaled]
  exact (div_le_iff₀ (pow_pos hA 2)).2 (by
    nlinarith only [hNumerator])

/-- The physical order-two channel is bounded by the *proven* canonical
square-root H³ gradient envelope. In particular, large global spectral
concentration cannot be attributed solely to the order-two commutator. -/
theorem h3Path_globalOrderTwoNormalizedRate_le_gradientBudget244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u t)
    (hD : 0 < velocityH3Dissipation3At u t) :
    h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass t ≤
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
  have hE2 : 0 ≤ velocityH3Energy2At u t :=
    velocityH3Energy2At_nonneg u t
  have hTop := h3TerminalPhysicalTopDissipation3Path_eq hClass ht
  have hDen : 0 < velocityH3Energy0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t := by
    rw [hTop]
    exact mul_pos hMass hD
  have hMoment := (h3Path_topFourier_normalizedMoment_strictRange244
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
  unfold h3PathTopFourierGlobalOrderTwoNormalizedRate244
  exact h3_normalizedOrderTwoTransport_scalar_le_thirtySix244
    (velocityH3Energy2At u t)
    (velocityH3TransportDerivative2At u t)
    (velocityH3Energy0At u t *
      h3TerminalPhysicalTopDissipation3Path hClass t)
    (h t) hE2 hDen hh hCauchy hTransport

/-- Sharp Young near-saturation requires genuine fourth-radial Leray
production plus the linear heat/moment term to cover the physical variance
secant, *after* the unconditional 36 h allowance for order-two transport. -/
theorem h3Path_nearYoung_forces_heatPlusLeray_after_orderTwoBudget244
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
        36 * h3PathCanonicalSqrtEnergyGradientEnvelope u r ≤
      h3PathTopFourierGlobalDiffusionNormalizedRate244 hH3 hClass r
        ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩ +
      h3PathTopFourierGlobalLerayNormalizedRate244 hH3 hClass r
        ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩ := by
  obtain ⟨r, hr, hRate⟩ :=
    h3Path_normalizedVariance_exists_exactSignedExcessSecant244
      hH3 hClass hs ht hst hMass hD
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  have hrClosed : r ∈ Set.Icc s t := ⟨hr.1.le, hr.2.le⟩
  have hThree := h3Path_normalizedSignedExcess_eq_globalThreeChannels244
    hH3 hClass hrClass
  rw [hThree] at hRate
  have hYoung := h3Path_topFourier_normalizedVariance_nearYoung_upper244
    hH3 hClass ht (hMass t ⟨hst.le, le_refl t⟩)
    hK (hD t ⟨hst.le, le_refl t⟩) hNear
  have hSecant :
      (h3PathTopFourierNormalizedRadialVariance244 u s -
          (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t)) /
        (t - s) ≤
      h3PathTopFourierGlobalDiffusionNormalizedRate244 hH3 hClass r hrClass +
        h3PathTopFourierGlobalOrderTwoNormalizedRate244 hClass r +
        h3PathTopFourierGlobalLerayNormalizedRate244 hH3 hClass r hrClass := by
    rw [hRate]
    exact (div_le_div_iff_of_pos_right (sub_pos.mpr hst)).2
      (by linarith only [hYoung])
  have hBudget := h3Path_globalOrderTwoNormalizedRate_le_gradientBudget244
    hH3 hClass hrClass (hMass r hrClosed) (hD r hrClosed)
  refine ⟨r, hr, ?_⟩
  linarith only [hSecant, hBudget]

end
end PrimeTensor.FirstMonomialTriad
