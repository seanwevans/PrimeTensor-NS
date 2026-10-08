import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedTopYoungAbsorption

/-!
# Separate lower-order transport energy from signed top-order adversity

The closed commutator estimates bound the first and second order transport
pairings by `6 h E₁` and `18 h E₂`, respectively, for the canonical envelope
`h = C₁ sqrt(E)`. Their previous use as `24 h E` loses the distinction
between the lower-order energy and total H³ energy.

Keeping the genuine orderwise factors and the signed third-order pairing gives

  E' + 2 D <= h (6 E₁ + 18 E₂) - T₃.

After spending an arbitrary nonnegative top-order viscous share ε D₃, the
retained-dissipation bound is

  E' + (2-ε) D <= h (6 E₁ + 18 E₂) + max(0,-T₃-ε D₃).

For `0 <= ε <= 2`, integrability of the corresponding normalized positive
excess implies continuation. At a time where the actual unabsorbed rate
exceeds M>=0, there is a *physical dichotomy*:

  (4422+M) E < h (6 E₁+18 E₂)
      OR
  2 D < -T₃.

Thus high growth cannot occur with both a subcritical lower-order commutator
and a nonadverse/viscously absorbed top-order transport. Neither branch is
excluded by the presently proved estimates; this is a neutral necessary
condition, not an unconditional regularity theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- The genuine, separately estimated lower-order transport cost retains
`E₁` and `E₂` rather than charging both to the full canonical energy. -/
theorem h3PathCanonical_lowerTransport_abs_le_orderwiseEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    |velocityH3TransportDerivative1At u t +
        velocityH3TransportDerivative2At u t| ≤
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        (6 * velocityH3Energy1At u t + 18 * velocityH3Energy2At u t) := by
  let h : ℝ → ℝ := h3PathCanonicalSqrtEnergyGradientEnvelope u
  have hGradient : VelocityGradientEnvelope u h t := by
    simpa only [h] using
      h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass ht
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hH3At : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs
  have hIBP1 : H3FirstDerivativeTransportIntegrationByPartsAt u t :=
    h3FirstDerivativeTransportIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradient
  have hIBP2 : H3SecondDerivativeTransportIntegrationByPartsAt u t :=
    h3SecondDerivativeTransportIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradient
  have hFlux1 : H3FirstDerivativeTransportFluxVanishesAt u t :=
    h3FirstDerivativeTransportFluxVanishesAt_of_integrationByParts hIBP1
  have hFlux2 : H3SecondDerivativeTransportFluxVanishesAt u t :=
    h3SecondDerivativeTransportFluxVanishesAt_of_integrationByParts hIBP2
  have hPurePairing1 : H3OrderOnePureTransportPairingIntegrableAt u t :=
    h3OrderOnePureTransportPairingIntegrableAt_of_integrationByParts
      hClass ht hIBP1
  have hPurePairing2 : H3OrderTwoPureTransportPairingIntegrableAt u t :=
    h3OrderTwoPureTransportPairingIntegrableAt_of_integrationByParts
      hClass ht hIBP2
  have hPairing1 : H3OrderOneTransportPairingIntegrableAt u t :=
    h3OrderOneTransportPairingIntegrableAt_of_pure
      hClass ht hH3At hGradient hPurePairing1
  have hPairing2 : H3OrderTwoTransportPairingIntegrableAt u t :=
    h3OrderTwoTransportPairingIntegrableAt_of_pure
      hClass ht hH3At hGradient hPurePairing2
  have h1 : |velocityH3TransportDerivative1At u t| ≤
      6 * h t * velocityH3Energy1At u t :=
    velocityH3TransportDerivative1At_le_gradientEnvelope
      hClass ht hFlux1 hPairing1 hH3At hGradient
  have h2 : |velocityH3TransportDerivative2At u t| ≤
      18 * h t * velocityH3Energy2At u t :=
    velocityH3TransportDerivative2At_le_gradientEnvelope
      hClass ht hFlux2 hPairing2 hH3At hGradient
  calc
    |velocityH3TransportDerivative1At u t +
        velocityH3TransportDerivative2At u t| ≤
        |velocityH3TransportDerivative1At u t| +
          |velocityH3TransportDerivative2At u t| := abs_add_le _ _
    _ ≤ 6 * h t * velocityH3Energy1At u t +
          18 * h t * velocityH3Energy2At u t := add_le_add h1 h2
    _ = (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) *
          (6 * velocityH3Energy1At u t +
            18 * velocityH3Energy2At u t) := by
      dsimp only [h, h3PathCanonicalSqrtEnergyGradientEnvelope]
      ring

/-- Exact energy balance with the genuinely lower-order `6E₁+18E₂` cost
and the *signed* third-order transport left unchanged. -/
theorem h3PathCanonical_deriv_add_dissipation_le_lowerOrderSignedTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t + 2 * velocityH3DissipationAt u t ≤
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        (6 * velocityH3Energy1At u t + 18 * velocityH3Energy2At u t) -
        velocityH3TransportDerivative3At u t := by
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hH3At : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs
  let h : ℝ → ℝ := h3PathCanonicalSqrtEnergyGradientEnvelope u
  have hGradient : VelocityGradientEnvelope u h t := by
    simpa only [h] using
      h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass ht
  have hIBP0 : H3TransportEnergyIntegrationByPartsAt u t :=
    h3TransportEnergyIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradient
  have hFlux0 : H3TransportEnergyFluxVanishesAt u t :=
    h3TransportEnergyFluxVanishesAt_of_integrationByParts hIBP0
  have h0 : velocityH3TransportDerivative0At u t = 0 :=
    velocityH3TransportDerivative0At_eq_zero_of_energyClass hClass ht hFlux0
  have hLower := h3PathCanonical_lowerTransport_abs_le_orderwiseEnergy
    hH3 hClass ht
  have hExact := deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
    hH3 hClass ht
  have hSigned :
      -velocityH3TransportDerivativeAt u t ≤
        |velocityH3TransportDerivative1At u t +
          velocityH3TransportDerivative2At u t| -
          velocityH3TransportDerivative3At u t := by
    unfold velocityH3TransportDerivativeAt
    rw [h0]
    have hAbs := neg_le_abs
      (velocityH3TransportDerivative1At u t +
        velocityH3TransportDerivative2At u t)
    simp only [zero_add]
    linarith only [hAbs]
  calc
    deriv (velocityH3EnergyAt u) t + 2 * velocityH3DissipationAt u t =
        -velocityH3TransportDerivativeAt u t := hExact
    _ ≤ |velocityH3TransportDerivative1At u t +
          velocityH3TransportDerivative2At u t| -
          velocityH3TransportDerivative3At u t := hSigned
    _ ≤ (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) *
          (6 * velocityH3Energy1At u t + 18 * velocityH3Energy2At u t) -
          velocityH3TransportDerivative3At u t :=
      sub_le_sub_right hLower _

/-- Spend a nonnegative top viscous share and retain `(2-ε)D`, but charge
only first- and second-order energies to the lower commutators. -/
theorem h3PathCanonical_deriv_retainedDissipation_le_lowerOrderSignedShare
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hε : 0 ≤ ε) :
    deriv (velocityH3EnergyAt u) t +
        (2 - ε) * velocityH3DissipationAt u t ≤
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        (6 * velocityH3Energy1At u t + 18 * velocityH3Energy2At u t) +
        h3PathCanonicalTopAdverseAfterViscousShare u ε t := by
  have hSigned := h3PathCanonical_deriv_add_dissipation_le_lowerOrderSignedTop
    hH3 hClass ht
  have hTopD : velocityH3Dissipation3At u t ≤
      velocityH3DissipationAt u t :=
    velocityH3Dissipation3At_le_dissipationAt u t
  have hScaled : ε * velocityH3Dissipation3At u t ≤
      ε * velocityH3DissipationAt u t :=
    mul_le_mul_of_nonneg_left hTopD hε
  have hMax : -velocityH3TransportDerivative3At u t -
      ε * velocityH3Dissipation3At u t ≤
      h3PathCanonicalTopAdverseAfterViscousShare u ε t := by
    unfold h3PathCanonicalTopAdverseAfterViscousShare
    exact le_max_right _ _
  linarith only [hSigned, hScaled, hMax]

/-- Positive normalized residual retaining *both* true lower-order energies
and the signed, already-viscously-absorbed top-order adverse transport. -/
noncomputable def h3PathCanonicalLowerOrderSignedShareRemainder
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (ε : ℝ) : ℝ → ℝ :=
  fun t => max 0
    (((h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        (6 * velocityH3Energy1At u t + 18 * velocityH3Energy2At u t) +
        h3PathCanonicalTopAdverseAfterViscousShare u ε t) /
      velocityH3EnergyAt u t - 4422)

/-- Under `0<=ε<=2`, the refined, signed, dissipation-absorbed residual
still bounds the *actual* unabsorbed normalized growth. -/
theorem h3PathCanonical_unabsorbed_le_lowerOrderSignedShareRemainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hε : 0 ≤ ε) (hεTwo : ε ≤ 2) :
    h3PathCanonicalUnabsorbedRiccatiRate u t ≤
      h3PathCanonicalLowerOrderSignedShareRemainder u ε t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hD : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hRetained : 0 ≤ (2 - ε) * velocityH3DissipationAt u t :=
    mul_nonneg (sub_nonneg.mpr hεTwo) hD
  have hBound := h3PathCanonical_deriv_retainedDissipation_le_lowerOrderSignedShare
    hH3 hClass ht hε
  have hGrowth : deriv (velocityH3EnergyAt u) t ≤
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        (6 * velocityH3Energy1At u t + 18 * velocityH3Energy2At u t) +
        h3PathCanonicalTopAdverseAfterViscousShare u ε t := by
    linarith only [hBound, hRetained]
  have hSlope : deriv (velocityH3EnergyAt u) t /
      velocityH3EnergyAt u t ≤
      ((h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        (6 * velocityH3Energy1At u t + 18 * velocityH3Energy2At u t) +
        h3PathCanonicalTopAdverseAfterViscousShare u ε t) /
        velocityH3EnergyAt u t := by
    exact (div_le_div_iff_of_pos_right hEPos).2 hGrowth
  rw [h3PathCanonical_unabsorbedRiccatiRate_eq_positiveAboveBaseline
    hH3 hClass ht]
  unfold h3PathCanonicalLowerOrderSignedShareRemainder
  exact max_le_max_left 0 (sub_le_sub_right hSlope 4422)

/-- Keeping the actual lower-order energies never increases the older
`24 h E` signed Young remainder. This is a genuine pointwise improvement,
but the improved remainder is not thereby known to be integrable. -/
theorem h3PathCanonical_lowerOrderSignedRemainder_le_priorYoungRemainder
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (ε t : ℝ) :
    h3PathCanonicalLowerOrderSignedShareRemainder u ε t ≤
      h3PathCanonicalSignedTopAbsorptionRemainder u ε t := by
  let h : ℝ := h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
    Real.sqrt (velocityH3EnergyAt u t)
  let E : ℝ := velocityH3EnergyAt u t
  let A : ℝ := h3PathCanonicalTopAdverseAfterViscousShare u ε t
  have hEPos : 0 < E := by
    dsimp only [E]
    exact lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hCoeff : 0 ≤ h := by
    dsimp only [h]
    exact mul_nonneg
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
      (Real.sqrt_nonneg _)
  have h1 : velocityH3Energy1At u t ≤ E := by
    dsimp only [E]
    exact velocityH3Energy1At_le_velocityH3EnergyAt u t
  have h2 : velocityH3Energy2At u t ≤ E := by
    dsimp only [E]
    exact velocityH3Energy2At_le_velocityH3EnergyAt u t
  have hOrder :
      6 * velocityH3Energy1At u t + 18 * velocityH3Energy2At u t ≤
        24 * E := by
    linarith only [h1, h2]
  have hScaled := mul_le_mul_of_nonneg_left hOrder hCoeff
  have hSum := add_le_add_left hScaled A
  have hDiv := (div_le_div_iff_of_pos_right hEPos).2 hSum
  have hCompare :
      (h * (6 * velocityH3Energy1At u t + 18 * velocityH3Energy2At u t) + A) /
          E ≤ 24 * h + A / E := by
    calc
      _ ≤ (h * (24 * E) + A) / E := hDiv
      _ = 24 * h + A / E := by
        field_simp [ne_of_gt hEPos]
        <;> ring
  unfold h3PathCanonicalLowerOrderSignedShareRemainder
    h3PathCanonicalSignedTopAbsorptionRemainder
  dsimp only [h, E, A] at hCompare ⊢
  exact max_le_max_left 0 (sub_le_sub_right hCompare 4422)

/-- Integrability of the refined signed lower-plus-top remainder on one
terminal energy-class tail is a sufficient continuation criterion. -/
theorem h3PathCanonical_extension_of_integrable_lowerOrderSignedShareRemainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hε : 0 ≤ ε) (hεTwo : ε ≤ 2)
    (hInt : IntegrableOn (h3PathCanonicalLowerOrderSignedShareRemainder u ε)
      (Set.Ioo a T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hMeas := h3PathCanonical_unabsorbedRate_aestronglyMeasurableOnTail
    hH3 hClass
  have hDom : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo a T)),
      ‖h3PathCanonicalUnabsorbedRiccatiRate u t‖ ≤
        h3PathCanonicalLowerOrderSignedShareRemainder u ε t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg (h3PathCanonical_unabsorbedRiccatiRate_nonneg u t)]
    exact h3PathCanonical_unabsorbed_le_lowerOrderSignedShareRemainder
      hH3 hClass ht hε hεTwo
  have hU : IntegrableOn (h3PathCanonicalUnabsorbedRiccatiRate u)
      (Set.Ioo a T) := Integrable.mono' hInt hMeas hDom
  exact h3PathCanonical_extension_of_integrable_unabsorbedRiccatiRate
    hH3 hClass hU

/-- Hypothetical nonextension forces the new signed/retained-order scalar
remainder to be nonintegrable on every later energy-class subtail. -/
theorem h3PathCanonical_lowerOrderSignedShareRemainder_nonintegrable_on_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hε : 0 ≤ ε) (hεTwo : ε ≤ 2) :
    ¬ IntegrableOn (h3PathCanonicalLowerOrderSignedShareRemainder u ε)
      (Set.Ioo d T) := by
  have hClassD : PreterminalH3EnergyClass u d T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hd.1) hd.2
  intro hInt
  exact hNoExtension
    (h3PathCanonical_extension_of_integrable_lowerOrderSignedShareRemainder
      hH3 hClassD hε hεTwo hInt)

/-- At high actual unabsorbed growth, either the low-order commutator
budget itself exceeds the threshold, or *signed top-order transport* must
be more adverse than twice the entire physical viscous dissipation. -/
theorem h3PathCanonical_highUnabsorbed_lowerOrderOrTopAdversity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hM : 0 ≤ M)
    (hHigh : M < h3PathCanonicalUnabsorbedRiccatiRate u t) :
    (4422 + M) * velocityH3EnergyAt u t <
        (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) *
          (6 * velocityH3Energy1At u t + 18 * velocityH3Energy2At u t) ∨
      2 * velocityH3DissipationAt u t <
        -velocityH3TransportDerivative3At u t := by
  have hSlope :=
    (h3PathCanonical_unabsorbedAbove_iff_normalizedEnergySlopeAbove
      hH3 hClass ht hM).1 hHigh
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hPhysical := (lt_div_iff₀ hEPos).1 hSlope
  have hSigned := h3PathCanonical_deriv_add_dissipation_le_lowerOrderSignedTop
    hH3 hClass ht
  by_cases hLow :
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        (6 * velocityH3Energy1At u t + 18 * velocityH3Energy2At u t) ≤
        (4422 + M) * velocityH3EnergyAt u t
  · right
    linarith only [hPhysical, hSigned, hLow]
  · left
    exact lt_of_not_ge hLow

/-- The physical either/or alternative is forced arbitrarily late at
arbitrarily high unabsorbed rate on the hypothetical nonextension branch. -/
theorem h3PathCanonical_lowerOrderOrTopAdversity_witness_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hM : 0 ≤ M) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      ((4422 + M) * velocityH3EnergyAt u t <
          (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t)) *
            (6 * velocityH3Energy1At u t + 18 * velocityH3Energy2At u t) ∨
        2 * velocityH3DissipationAt u t <
          -velocityH3TransportDerivative3At u t) := by
  obtain ⟨t, ht, hHigh⟩ :=
    h3PathCanonical_unabsorbedRiccatiRate_unbounded_on_tail
      M hH3 hNoExtension hClass hd
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  exact ⟨t, ht, h3PathCanonical_highUnabsorbed_lowerOrderOrTopAdversity
    hH3 hClass htClass hM hHigh⟩

end Euclidean
end Bridge
end PrimeTensor
