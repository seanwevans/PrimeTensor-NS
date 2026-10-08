import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalMomentCorridorDegeneracy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Balance.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Growth.Dissipative

/-!
# Retain the top-order energy block in the actual H³ nonlinear transport estimate

The established Landau argument gives order-one and order-two commutator costs
`6 h E` and `18 h E`, while the order-three cost is `4398 h E₃`.
Its final published `4422 h E` bound replaces `E₃` by `E`. Here we retain
that distinction and instantiate the bound using the already-closed H³
path PDE-pairing, flux cancellation, Sobolev and Landau data.

With `h=C₁ sqrt(E)` and `D` the full nonnegative dissipation,

    |transport| ≤ C₁ sqrt(E) (24 E + 4398 E₃),
    E' + 2D ≤ C₁ sqrt(E) (24 E + 4398 E₃).

Consequently the exact unabsorbed nonlinear rate is bounded by the positive
part of the *refined, top-order-sensitive* transport coefficient minus 4422.
This is a refinement of the actual established PDE commutator estimate, not a
new time-integrability theorem or unconditional continuation result.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- Retain the `E₃` summand instead of replacing it by full H³ energy
in the third-order Landau commutator estimate. -/
theorem h3PathCanonical_abs_transport_le_refined_orderwise_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    |velocityH3TransportDerivativeAt u t| ≤
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        (24 * velocityH3EnergyAt u t +
          4398 * velocityH3Energy3At u t) := by
  let h : ℝ → ℝ := h3PathCanonicalSqrtEnergyGradientEnvelope u
  have hGradient : VelocityGradientEnvelope u h t := by
    simpa only [h] using
      h3PathCanonicalSqrtEnergyGradientEnvelope_at hH3 hClass ht
  have hSobolev6 : WholeSpaceC1H1ToL6 :=
    wholeSpaceC1H1ToL6_of_fderiv wholeSpaceC1FDerivL2ToL6_cutoff
  have hSobolev : WholeSpaceC1H1ToL4 :=
    wholeSpaceC1H1ToL4_of_wholeSpaceC1H1ToL6 hSobolev6
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hH3At : VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable t htAbs
  have hIBP0 : H3TransportEnergyIntegrationByPartsAt u t :=
    h3TransportEnergyIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradient
  have hIBP1 : H3FirstDerivativeTransportIntegrationByPartsAt u t :=
    h3FirstDerivativeTransportIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradient
  have hIBP2 : H3SecondDerivativeTransportIntegrationByPartsAt u t :=
    h3SecondDerivativeTransportIntegrationByPartsAt_of_energyClass
      hClass ht hH3At hGradient
  have hFlux0 : H3TransportEnergyFluxVanishesAt u t :=
    h3TransportEnergyFluxVanishesAt_of_integrationByParts hIBP0
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
  have hCore3 : H3OrderThreeInterpolationLandauCoreAnalyticDataAt u h t := by
    simpa [H3OrderThreeInterpolationLandauCoreAnalyticDataAt] using hGradient
  have hAnalytic3 : H3OrderThreeInterpolationLandauAnalyticDataAt u h t :=
    h3OrderThreeInterpolationLandauAnalyticDataAt_of_core
      hSobolev wholeSpaceQuarticDerivativeIntegrationByParts_cutoff
      hClass ht hH3At hCore3
  have hPairing1 : H3OrderOneTransportPairingIntegrableAt u t :=
    h3OrderOneTransportPairingIntegrableAt_of_pure
      hClass ht hH3At hGradient hPurePairing1
  have hPairing2 : H3OrderTwoTransportPairingIntegrableAt u t :=
    h3OrderTwoTransportPairingIntegrableAt_of_pure
      hClass ht hH3At hGradient hPurePairing2
  have hRegular3 : H3OrderThreeTransportRegularityAt u t :=
    h3OrderThreeTransportRegularityAt_of_energyClass hClass ht
  have hGradientPairing3 : H3OrderThreeGradientPairingIntegrableAt u t :=
    h3OrderThreeGradientPairingIntegrableAt_of_energyClass
      hClass ht hH3At hGradient
  have hMonomialPairing3 : H3OrderThreeInterpolationMonomialPairingIntegrableAt u t :=
    h3OrderThreeInterpolationMonomialPairingIntegrableAt_of_landauAnalyticData
      hAnalytic3
  have hInterpolationPairing3 : H3OrderThreeInterpolationPairingIntegrableAt u t :=
    h3OrderThreeInterpolationPairingIntegrableAt_of_monomials
      hMonomialPairing3
  have hPDEPairing : H3PDEPairingIntegrableAt u
      (h3EnergyClassSplitPressureAt hClass ht) t :=
    h3PathEnergyClassProducesPDEPairingIntegrability_closed
      u T hH3 a hClass t ht
  have hFlux3 : H3ThirdDerivativeTransportFluxVanishesAt u t :=
    h3ThirdDerivativeTransportFluxVanishesAt_of_pde
      hClass ht hH3At hPDEPairing hGradientPairing3 hInterpolationPairing3
  have hPairing3 : H3OrderThreeTransportPairingIntegrableAt u t :=
    h3OrderThreeTransportPairingIntegrableAt_of_pde
      hClass ht hPDEPairing hGradientPairing3 hInterpolationPairing3
  have h0 : velocityH3TransportDerivative0At u t = 0 :=
    velocityH3TransportDerivative0At_eq_zero_of_energyClass
      hClass ht hFlux0
  have h1 : |velocityH3TransportDerivative1At u t| ≤
      6 * h t * velocityH3EnergyAt u t :=
    velocityH3TransportDerivative1At_le_totalEnergy
      hClass ht hFlux1 hPairing1 hH3At hGradient
  have h2 : |velocityH3TransportDerivative2At u t| ≤
      18 * h t * velocityH3EnergyAt u t :=
    velocityH3TransportDerivative2At_le_totalEnergy
      hClass ht hFlux2 hPairing2 hH3At hGradient
  have h3 : |velocityH3TransportDerivative3At u t| ≤
      4398 * h t * velocityH3Energy3At u t :=
    velocityH3TransportDerivative3At_le_of_landauAnalyticData
      hClass ht hRegular3 hFlux3 hPairing3 hGradientPairing3 hH3At hAnalytic3
  have hTriangle :
      |velocityH3TransportDerivative1At u t +
        velocityH3TransportDerivative2At u t +
        velocityH3TransportDerivative3At u t| ≤
      |velocityH3TransportDerivative1At u t| +
        |velocityH3TransportDerivative2At u t| +
        |velocityH3TransportDerivative3At u t| := by
    calc
      _ ≤ |velocityH3TransportDerivative1At u t +
              velocityH3TransportDerivative2At u t| +
              |velocityH3TransportDerivative3At u t| := abs_add_le _ _
      _ ≤ (|velocityH3TransportDerivative1At u t| +
              |velocityH3TransportDerivative2At u t|) +
              |velocityH3TransportDerivative3At u t| := by
        simpa only [add_comm, add_left_comm, add_assoc] using
          (add_le_add_right
            (abs_add_le
              (velocityH3TransportDerivative1At u t)
              (velocityH3TransportDerivative2At u t))
            |velocityH3TransportDerivative3At u t|)
  have hSum : |velocityH3TransportDerivative1At u t| +
      |velocityH3TransportDerivative2At u t| +
      |velocityH3TransportDerivative3At u t| ≤
      24 * h t * velocityH3EnergyAt u t +
      4398 * h t * velocityH3Energy3At u t := by
    nlinarith only [h1, h2, h3]
  have hCore : |velocityH3TransportDerivativeAt u t| ≤
      24 * h t * velocityH3EnergyAt u t +
      4398 * h t * velocityH3Energy3At u t := by
    unfold velocityH3TransportDerivativeAt
    rw [h0]
    norm_num
    exact hTriangle.trans hSum
  calc
    |velocityH3TransportDerivativeAt u t| ≤
        24 * h t * velocityH3EnergyAt u t +
        4398 * h t * velocityH3Energy3At u t := hCore
    _ = (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) *
          (24 * velocityH3EnergyAt u t +
            4398 * velocityH3Energy3At u t) := by
      dsimp only [h, h3PathCanonicalSqrtEnergyGradientEnvelope]
      ring

/-- Real, nonnegative refined spectral transport rate, retaining E₃/E. -/
noncomputable def h3PathCanonicalOrderwiseTransportRate
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) : ℝ :=
  (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
    Real.sqrt (velocityH3EnergyAt u t)) *
    (24 + 4398 * (velocityH3Energy3At u t / velocityH3EnergyAt u t))

/-- The exact dissipative balance retains the 24/4398 split of the
physical nonlinear transport coefficient. -/
theorem h3PathCanonical_deriv_add_dissipation_le_orderwiseTransport
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t + 2 * velocityH3DissipationAt u t ≤
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        (24 * velocityH3EnergyAt u t +
          4398 * velocityH3Energy3At u t) := by
  have hExact := deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
    hH3 hClass ht
  have hBound := h3PathCanonical_abs_transport_le_refined_orderwise_energy
    hH3 hClass ht
  exact (le_of_eq hExact).trans ((neg_le_abs _).trans hBound)

/-- The normalized physical energy slope is bounded by the retained-order
spectral rate after subtracting the nonnegative viscous contribution. -/
theorem h3PathCanonical_normalizedSlope_le_orderwiseTransportRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t ≤
      h3PathCanonicalOrderwiseTransportRate u t := by
  have hPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hD : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hPhysical := h3PathCanonical_deriv_add_dissipation_le_orderwiseTransport
    hH3 hClass ht
  have hDeriv : deriv (velocityH3EnergyAt u) t ≤
      (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) *
        (24 * velocityH3EnergyAt u t +
          4398 * velocityH3Energy3At u t) := by
    linarith only [hPhysical, hD]
  apply (div_le_iff₀ hPos).2
  calc
    deriv (velocityH3EnergyAt u) t ≤
        (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) *
          (24 * velocityH3EnergyAt u t +
            4398 * velocityH3Energy3At u t) := hDeriv
    _ = h3PathCanonicalOrderwiseTransportRate u t *
          velocityH3EnergyAt u t := by
      unfold h3PathCanonicalOrderwiseTransportRate
      field_simp [ne_of_gt hPos]

/-- The actual positive unabsorbed Riccati rate inherits the refined
orderwise spectral bound with the original 4422 baseline subtracted. -/
theorem h3PathCanonical_unabsorbed_le_positive_orderwiseTransportRemainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    h3PathCanonicalUnabsorbedRiccatiRate u t ≤
      max 0 (h3PathCanonicalOrderwiseTransportRate u t - 4422) := by
  rw [h3PathCanonical_unabsorbedRiccatiRate_eq_positiveAboveBaseline
    hH3 hClass ht]
  have hSlope := h3PathCanonical_normalizedSlope_le_orderwiseTransportRate
    hH3 hClass ht
  exact max_le_max_left 0 (sub_le_sub_right hSlope 4422)

/-- Because canonical H³ energy includes a strictly positive baseline,
`E₃ < E` always. Thus the retained-order transport coefficient is strictly
smaller than the coefficient obtained by substituting `E₃ ≤ E`. The strict
improvement may become arbitrarily small at large energy. -/
theorem h3PathCanonical_orderwiseTransportRate_lt_fullEnergyEnvelope
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    h3PathCanonicalOrderwiseTransportRate u t <
      4422 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) := by
  have h0 : 0 ≤ velocityH3Energy0At u t :=
    velocityH3Energy0At_nonneg u t
  have h1 : 0 ≤ velocityH3Energy1At u t :=
    velocityH3Energy1At_nonneg u t
  have h2 : 0 ≤ velocityH3Energy2At u t :=
    velocityH3Energy2At_nonneg u t
  have hTopStrict : velocityH3Energy3At u t < velocityH3EnergyAt u t := by
    unfold velocityH3EnergyAt
    linarith only [h0, h1, h2]
  have hPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hRatio : velocityH3Energy3At u t / velocityH3EnergyAt u t < 1 := by
    apply (div_lt_iff₀ hPos).2
    simpa only [one_mul] using hTopStrict
  have hBracket :
      24 + 4398 * (velocityH3Energy3At u t / velocityH3EnergyAt u t) <
        4422 := by
    nlinarith only [hRatio]
  have hCoeff : 0 <
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t) :=
    mul_pos h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos
      (Real.sqrt_pos.2 hPos)
  calc
    h3PathCanonicalOrderwiseTransportRate u t =
        (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) *
          (24 + 4398 * (velocityH3Energy3At u t / velocityH3EnergyAt u t)) := rfl
    _ < (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * 4422 :=
      mul_lt_mul_of_pos_left hBracket hCoeff
    _ = 4422 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) := by ring

/-- Even after retaining the top-order structure, the unabsorbed spectral
envelope remains only a sufficient, conditional continuation mechanism. -/
theorem h3PathCanonical_extension_of_integrable_orderwiseTransportRemainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hInt : IntegrableOn
      (fun t : ℝ => max 0 (h3PathCanonicalOrderwiseTransportRate u t - 4422))
      (Set.Ioo a T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hMeas := h3PathCanonical_unabsorbedRate_aestronglyMeasurableOnTail
    hH3 hClass
  have hDom : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo a T)),
      ‖h3PathCanonicalUnabsorbedRiccatiRate u t‖ ≤
        max 0 (h3PathCanonicalOrderwiseTransportRate u t - 4422) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg (h3PathCanonical_unabsorbedRiccatiRate_nonneg u t)]
    exact h3PathCanonical_unabsorbed_le_positive_orderwiseTransportRemainder
      hH3 hClass ht
  have hU : IntegrableOn (h3PathCanonicalUnabsorbedRiccatiRate u)
      (Set.Ioo a T) := Integrable.mono' hInt hMeas hDom
  exact h3PathCanonical_extension_of_integrable_unabsorbedRiccatiRate
    hH3 hClass hU

end Euclidean
end Bridge
end PrimeTensor
