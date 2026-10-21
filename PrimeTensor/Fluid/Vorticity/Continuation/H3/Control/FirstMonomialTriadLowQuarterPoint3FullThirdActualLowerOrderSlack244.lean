import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdIntegrableMajorantObstruction244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalEffectiveDefectBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalUnabsorbedEssentialBarrier
import Mathlib.Tactic

/-!
# Exact lower-order transport slack in the full signed H³ spectral balance

The weighted spectral rate replaces the *actual signed* lower-order physical
transport by the worst-case positive estimate `24 C₁ sqrt(E) E`.
This creates an exact, nonnegative slack

  L(t) = 24 C₁ sqrt(E(t)) + (T₁(t) + T₂(t))/E(t),

which lies between zero and `48 C₁ sqrt(E(t))`. Thus the signed 972-gradient
and 3×243-interpolation excesses obey the **exact dynamical identity**

  X_G(t) + X_I(t) = E'(t)/E(t) - 4422 + L(t).

This is not an inequality, and it uses the genuine NSE order-zero flux
cancellation and full H³ energy balance. Combining with the existing exact
canonical effective Riccati defect `Q` yields

  Q(t) + X_G(t) + X_I(t) = 4422 C₁ sqrt(E(t)) + L(t).

The resulting signed *joint-channel* continuation criterion is stronger
than bounding both positive channel parts separately: cancellation between
G₃ and 3M₃ is permitted. No unconditional control of the signed joint
channel, the slack, or the Riccati defect is claimed.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory

noncomputable section
set_option maxHeartbeats 1500000

/-- Exactly the lower-order expense of replacing physical T₁+T₂ by the
worst possible adverse sign. Unlike a Schwartz approximation, this uses
the actual physical velocity path. -/
noncomputable def h3PathActualLowerTransportSlack244
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : ℝ :=
  24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) +
    (velocityH3TransportDerivative1At u t +
      velocityH3TransportDerivative2At u t) / velocityH3EnergyAt u t

/-- The order-zero physical convective flux vanishes exactly, rather than
being included in a signed gradient or interpolation error budget. -/
theorem h3Path_actualZeroOrderTransport_eq_zero244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    velocityH3TransportDerivative0At u t = 0 := by
  have htNS : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hH3At : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htNS
  let h : ℝ → ℝ := h3PathCanonicalSqrtEnergyGradientEnvelope u
  have hGradient : VelocityGradientEnvelope u h t := by
    simpa only [h] using
      h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass ht
  have hIBP : H3TransportEnergyIntegrationByPartsAt u t :=
    h3TransportEnergyIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradient
  have hFlux : H3TransportEnergyFluxVanishesAt u t :=
    h3TransportEnergyFluxVanishesAt_of_integrationByParts hIBP
  exact velocityH3TransportDerivative0At_eq_zero_of_energyClass
    hClass ht hFlux

/-- The exact physical NSE balance identifies the entire difference
between the canonical signed top spectral rate and the *actual* logarithmic
H³-energy slope. No error term is discarded. -/
theorem h3Path_weightedSignedRate_eq_slope_add_lowerSlack244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathWeightedSignedTopRate244 u T hH3 t =
      deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t +
        h3PathActualLowerTransportSlack244 u t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hENe : velocityH3EnergyAt u t ≠ 0 := ne_of_gt hEPos
  have hZero := h3Path_actualZeroOrderTransport_eq_zero244 hH3 hClass ht
  have hBalance := deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
    hH3 hClass ht
  have hTransport : velocityH3TransportDerivativeAt u t =
      velocityH3TransportDerivative1At u t +
        velocityH3TransportDerivative2At u t +
        velocityH3TransportDerivative3At u t := by
    unfold velocityH3TransportDerivativeAt
    rw [hZero]
    ring
  rw [hTransport] at hBalance
  have hCanonical := h3Path_weightedFullThird_eq_physical244 hH3 hClass ht
  unfold h3PathWeightedSignedTopRate244 h3PathActualLowerTransportSlack244
  rw [← hCanonical]
  field_simp [hENe]
  nlinarith only [hBalance]

/-- The precise worst-case lower-order slack interval is
`[0, 48 C₁ sqrt(E)]`. Both endpoints are algebraically compatible with
the already-proved absolute lower-order transport inequality. -/
theorem h3Path_actualLowerTransportSlack_bounds244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    0 ≤ h3PathActualLowerTransportSlack244 u t ∧
      h3PathActualLowerTransportSlack244 u t ≤
        48 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) := by
  let B : ℝ :=
    24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t))
  let V : ℝ := velocityH3TransportDerivative1At u t +
    velocityH3TransportDerivative2At u t
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hTransportBound := h3PathCanonical_lowerTransport_abs_le_gradientEnergy
    hH3 hClass ht
  have hAbs : |V| ≤ B * velocityH3EnergyAt u t := by
    simpa only [B, V] using hTransportBound
  have hLow : -(B * velocityH3EnergyAt u t) ≤ V :=
    (abs_le.mp hAbs).1
  have hHigh : V ≤ B * velocityH3EnergyAt u t :=
    (abs_le.mp hAbs).2
  have hRatioLow : -B ≤ V / velocityH3EnergyAt u t := by
    apply (le_div_iff₀ hEPos).2
    nlinarith only [hLow]
  have hRatioHigh : V / velocityH3EnergyAt u t ≤ B := by
    apply (div_le_iff₀ hEPos).2
    exact hHigh
  constructor
  · change 0 ≤ B + V / velocityH3EnergyAt u t
    linarith only [hRatioLow]
  · change B + V / velocityH3EnergyAt u t ≤
      48 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))
    dsimp only [B] at hRatioHigh
    linarith only [hRatioHigh]

/-- Signed gradient plus interpolation excess is exactly the genuine
physical logarithmic growth above the baseline, PLUS nonnegative lower-
order replacement slack. Thus cofinal channel growth need not by itself
be cofinal physical energy growth: the slack must also be accounted for. -/
theorem h3Path_signedChannels_sum_eq_physicalGrowth_add_slack244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathWeightedGradientNormalizedExcess244 u T hH3 t +
        h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t =
      deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t - 4422 +
        h3PathActualLowerTransportSlack244 u t := by
  have hRate := h3Path_weightedSignedRate_eq_slope_add_lowerSlack244
    hH3 hClass ht
  have hSplit := h3Path_weightedSignedRate_subBaseline_eq_channelSum244
    u T hH3 t
  linarith only [hRate, hSplit]

/-- The exact canonical Riccati defect pays precisely for the nonlinear
sqrt-energy allowance, modulo the *joint signed* spectral channel and the
physical lower-order replacement slack. This is the PDE-coupled spectral
identity, not a spatial inequality for arbitrary Schwartz snapshots. -/
theorem h3Path_effectiveDefect_add_signedChannels_eq_nonlinearBudget_add_slack244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathCanonicalEffectiveRiccatiDefect u t +
      (h3PathWeightedGradientNormalizedExcess244 u T hH3 t +
       h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t) =
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
        Real.sqrt (velocityH3EnergyAt u t) +
        h3PathActualLowerTransportSlack244 u t := by
  have hExact := h3PathCanonical_effectiveDefect_add_normalizedGrowth_eq_budget
    hH3 hClass ht
  have hSigned := h3Path_signedChannels_sum_eq_physicalGrowth_add_slack244
    hH3 hClass ht
  linarith only [hExact, hSigned]

/-- A single *signed* a.e. integrable upper envelope on the joint
972-gradient + 3×243-interpolation excess is sufficient for continuation.
Unlike separate channel ceilings, this genuinely allows arbitrary large
opposite-signed excursions to cancel. Spectral channel measurability is
not assumed; only the measurable physical Riccati rate is dominated. -/
theorem h3Path_extension_of_ae_integrable_jointSignedChannel_majorant244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (r : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : IntegrableOn r (Set.Ioo a T))
    (hBound : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo a T)),
      h3PathWeightedGradientNormalizedExcess244 u T hH3 t +
        h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t ≤ r t) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hMajor : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo a T)),
      h3PathCanonicalUnabsorbedRiccatiRate u t ≤ ‖r t‖ := by
    filter_upwards [hBound, ae_restrict_mem measurableSet_Ioo]
      with t hSum ht
    have hPhysical := h3PathCanonical_unabsorbed_le_signedTopTransportRemainder
      hH3 hClass ht
    have hCanonical := h3Path_weightedSignedTopRemainder_eq_physical244
      hH3 hClass ht
    have hRemainder := h3Path_weightedRemainder_eq_positiveChannelSum244
      u T hH3 t
    have hEnvelope : max 0 (h3PathWeightedGradientNormalizedExcess244
          u T hH3 t +
          h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t) ≤
        ‖r t‖ := by
      calc
        _ ≤ max 0 (r t) := max_le_max_left 0 hSum
        _ ≤ ‖r t‖ := by
          rw [Real.norm_eq_abs]
          exact max_le (abs_nonneg _) (le_abs_self _)
    rw [← hCanonical, hRemainder] at hPhysical
    exact hPhysical.trans hEnvelope
  exact h3PathCanonical_extension_of_ae_integrable_unabsorbed_majorant
    hH3 hClass hr.norm hMajor

/-- Consequently hypothetical nonextension excludes EVERY integrable a.e.
upper envelope on the *sum* of both signed channels on EVERY strict subtail.
Individual channels may separately have arbitrarily large positive values;
this theorem rules out their cancellation consistently defeating the joint
physical growth obstruction. -/
theorem h3Path_jointSignedChannel_no_ae_integrable_majorant_on_subtail244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ} (r : ℝ → ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hr : IntegrableOn r (Set.Ioo d T)) :
    ¬ (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo d T)),
      h3PathWeightedGradientNormalizedExcess244 u T hH3 t +
        h3PathWeightedInterpolationNormalizedExcess244 u T hH3 t ≤ r t) := by
  intro hBound
  have hClassD : PreterminalH3EnergyClass u d T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hd.1) hd.2
  exact hNoExtension
    (h3Path_extension_of_ae_integrable_jointSignedChannel_majorant244
      r hH3 hClassD hr hBound)

end
end PrimeTensor.FirstMonomialTriad
