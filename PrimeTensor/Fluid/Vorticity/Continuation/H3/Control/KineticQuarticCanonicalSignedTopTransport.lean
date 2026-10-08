import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalOrderwiseTransportRefinement

/-!
# Signed top-order H3 transport: retain the adverse sign before estimating

The order-one and order-two Landau estimates cost at most 24 h(t) E(t),
where h=C1 sqrt(E). The order-zero flux cancels exactly. Unlike the
previous absolute-value theorem, we do NOT replace the signed third-order
transport by its absolute value. The exact balance gives

  E' + 2D <= 24 h E - T3.

Hence the signed top-order rate

  S3 = 24 h - (T3+2D)/E

bounds E'/E. Integrability of max(0,S3-4422) suffices for continuation.
Conversely, nonextension makes that signed remainder nonintegrable on every
terminal subtail. Times with U>M must satisfy

  (4422+M) E + 2D < 24 h E - T3.

These are exact consequences of existing PDE bounds. They do not estimate
T3's adverse sign independently or prove unconditional continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- The first two commutator orders cost at most `24 h E`. This estimate
keeps the third-order transport completely untouched. -/
theorem h3PathCanonical_lowerTransport_abs_le_gradientEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    |velocityH3TransportDerivative1At u t +
        velocityH3TransportDerivative2At u t| ≤
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t := by
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
      6 * h t * velocityH3EnergyAt u t :=
    velocityH3TransportDerivative1At_le_totalEnergy
      hClass ht hFlux1 hPairing1 hH3At hGradient
  have h2 : |velocityH3TransportDerivative2At u t| ≤
      18 * h t * velocityH3EnergyAt u t :=
    velocityH3TransportDerivative2At_le_totalEnergy
      hClass ht hFlux2 hPairing2 hH3At hGradient
  calc
    |velocityH3TransportDerivative1At u t +
        velocityH3TransportDerivative2At u t| ≤
        |velocityH3TransportDerivative1At u t| +
          |velocityH3TransportDerivative2At u t| := abs_add_le _ _
    _ ≤ 24 * h t * velocityH3EnergyAt u t := by
      nlinarith only [h1, h2]
    _ = 24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t := rfl

/-- Signed top transport is not replaced by its absolute value: the exact
energy balance retains both its orientation and all physical dissipation. -/
theorem h3PathCanonical_deriv_add_dissipation_le_signedTopTransport
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t + 2 * velocityH3DissipationAt u t ≤
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t -
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
  have hLower := h3PathCanonical_lowerTransport_abs_le_gradientEnergy
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
    _ ≤ 24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t -
          velocityH3TransportDerivative3At u t :=
      sub_le_sub_right hLower _

/-- Signed third-order transport rate after using the worst-case lower-order
24hE bound and retaining the *actual* full viscous dissipation. -/
noncomputable def h3PathCanonicalSignedTopTransportRate
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : ℝ :=
  24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) -
    (velocityH3TransportDerivative3At u t +
      2 * velocityH3DissipationAt u t) / velocityH3EnergyAt u t

/-- Positive rate left after the signed top-order PDE channel and the fixed
4422 baseline. Unlike the earlier envelope this records the sign of T3. -/
noncomputable def h3PathCanonicalSignedTopTransportRemainder
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) : ℝ → ℝ :=
  fun t => max 0 (h3PathCanonicalSignedTopTransportRate u t - 4422)

/-- Signed top transport controls the actual normalized H3 energy derivative. -/
theorem h3PathCanonical_normalizedSlope_le_signedTopTransportRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t ≤
      h3PathCanonicalSignedTopTransportRate u t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hBound := h3PathCanonical_deriv_add_dissipation_le_signedTopTransport
    hH3 hClass ht
  apply (div_le_iff₀ hEPos).2
  have hEq : h3PathCanonicalSignedTopTransportRate u t *
      velocityH3EnergyAt u t =
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t -
        velocityH3TransportDerivative3At u t -
        2 * velocityH3DissipationAt u t := by
    unfold h3PathCanonicalSignedTopTransportRate
    field_simp [ne_of_gt hEPos]
    <;> ring
  rw [hEq]
  linarith only [hBound]

/-- The actual unabsorbed Riccati growth is dominated by the *signed*,
fully dissipative top-order positive remainder. -/
theorem h3PathCanonical_unabsorbed_le_signedTopTransportRemainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathCanonicalUnabsorbedRiccatiRate u t ≤
      h3PathCanonicalSignedTopTransportRemainder u t := by
  rw [h3PathCanonical_unabsorbedRiccatiRate_eq_positiveAboveBaseline
    hH3 hClass ht]
  have hSlope := h3PathCanonical_normalizedSlope_le_signedTopTransportRate
    hH3 hClass ht
  unfold h3PathCanonicalSignedTopTransportRemainder
  exact max_le_max_left 0 (sub_le_sub_right hSlope 4422)

/-- A time-integrable signed top-order excess is sufficient for continuation.
No estimate establishing this premise for all solutions is claimed. -/
theorem h3PathCanonical_extension_of_integrable_signedTopTransportRemainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hInt : IntegrableOn (h3PathCanonicalSignedTopTransportRemainder u)
      (Set.Ioo a T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hMeas := h3PathCanonical_unabsorbedRate_aestronglyMeasurableOnTail
    hH3 hClass
  have hDom : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo a T)),
      ‖h3PathCanonicalUnabsorbedRiccatiRate u t‖ ≤
        h3PathCanonicalSignedTopTransportRemainder u t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg (h3PathCanonical_unabsorbedRiccatiRate_nonneg u t)]
    exact h3PathCanonical_unabsorbed_le_signedTopTransportRemainder
      hH3 hClass ht
  have hU : IntegrableOn (h3PathCanonicalUnabsorbedRiccatiRate u)
      (Set.Ioo a T) := Integrable.mono' hInt hMeas hDom
  exact h3PathCanonical_extension_of_integrable_unabsorbedRiccatiRate
    hH3 hClass hU

/-- Nonextension precludes integrability of the signed-top remainder on every
strict H3 energy-class terminal subtail. -/
theorem h3PathCanonical_signedTopRemainder_nonintegrable_on_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T) :
    ¬ IntegrableOn (h3PathCanonicalSignedTopTransportRemainder u)
      (Set.Ioo d T) := by
  have hClassD : PreterminalH3EnergyClass u d T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hd.1) hd.2
  intro hInt
  exact hNoExtension
    (h3PathCanonical_extension_of_integrable_signedTopTransportRemainder
      hH3 hClassD hInt)

/-- Any high-unabsorbed instant forces a *signed adverse* third-order
transport condition after allowing for lower-order commutators and dissipation.
The inequality does not alone force `T3<0`: the lower-order allowance
`24hE` could itself exceed the chosen threshold. -/
theorem h3PathCanonical_highUnabsorbed_forces_signedTopAdversity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hM : 0 ≤ M)
    (hHigh : M < h3PathCanonicalUnabsorbedRiccatiRate u t) :
    (4422 + M) * velocityH3EnergyAt u t +
        2 * velocityH3DissipationAt u t <
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t -
        velocityH3TransportDerivative3At u t := by
  have hSlope :=
    (h3PathCanonical_unabsorbedAbove_iff_normalizedEnergySlopeAbove
      hH3 hClass ht hM).1 hHigh
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hGrowth := (lt_div_iff₀ hEPos).1 hSlope
  have hBound := h3PathCanonical_deriv_add_dissipation_le_signedTopTransport
    hH3 hClass ht
  linarith only [hGrowth, hBound]

/-- The necessary signed third-order transport condition occurs arbitrarily
late under hypothetical nonextension, for any nonnegative threshold. -/
theorem h3PathCanonical_signedTopAdversity_witness_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hM : 0 ≤ M) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      (4422 + M) * velocityH3EnergyAt u t +
          2 * velocityH3DissipationAt u t <
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t -
          velocityH3TransportDerivative3At u t := by
  obtain ⟨t, ht, hHigh⟩ :=
    h3PathCanonical_unabsorbedRiccatiRate_unbounded_on_tail
      M hH3 hNoExtension hClass hd
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  exact ⟨t, ht, h3PathCanonical_highUnabsorbed_forces_signedTopAdversity
    hH3 hClass htClass hM hHigh⟩

end Euclidean
end Bridge
end PrimeTensor
