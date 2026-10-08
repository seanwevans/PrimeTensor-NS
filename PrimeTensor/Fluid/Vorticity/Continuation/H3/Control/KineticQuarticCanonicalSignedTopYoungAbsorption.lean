import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedTopTransport
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.ThirdOrderAbsorption

/-!
# Signed third-order transport: use actual top viscous dissipation in Young's estimate

The existing third-order Landau commutator theorem controls the *absolute*
transport pairing by `K E₃` with `K=4398 C₁ sqrt(E)`. Spatial Fourier
interpolation gives, for every positive `ε`,

  |T₃| ≤ ε D₃ + K^4 E₀ / ε^3.

But the signed energy identity only needs the *adverse* portion of the top
transport that remains after spending `ε D₃`:

  A₃,ε(t) := max(0, -T₃(t) - ε D₃(t)).

Prove the genuine PDE estimate

  0 ≤ A₃,ε ≤ K^4 E₀ / ε^3,
  E' + (2-ε) D ≤ 24 C₁ sqrt(E) E + A₃,ε.

The signed excess retains favorable orientation of T₃ and retains positive
full dissipation for ε≤2. Its temporal integrability, once normalized,
would imply continuation, but this estimate does NOT establish that
integrability. The explicit Young bound is typically quartic in the
square-root-energy coefficient, so no hidden regularity claim is made.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- The actual third-order commutator is bounded by its top-order energy,
with the canonical square-root-energy gradient coefficient. This is the
specific physical PDE ingredient consumed by top-order Fourier Young. -/
theorem h3PathCanonical_abs_thirdTransport_le_kineticGradientTopEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    |velocityH3TransportDerivative3At u t| ≤
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) * velocityH3Energy3At u t := by
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
  have hCore3 : H3OrderThreeInterpolationLandauCoreAnalyticDataAt u h t := by
    simpa [H3OrderThreeInterpolationLandauCoreAnalyticDataAt] using hGradient
  have hAnalytic3 : H3OrderThreeInterpolationLandauAnalyticDataAt u h t :=
    h3OrderThreeInterpolationLandauAnalyticDataAt_of_core
      hSobolev wholeSpaceQuarticDerivativeIntegrationByParts_cutoff
      hClass ht hH3At hCore3
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
  have hBound : |velocityH3TransportDerivative3At u t| ≤
      4398 * h t * velocityH3Energy3At u t :=
    velocityH3TransportDerivative3At_le_of_landauAnalyticData
      hClass ht hRegular3 hFlux3 hPairing3 hGradientPairing3 hH3At hAnalytic3
  simpa only [h, h3PathCanonicalSqrtEnergyGradientEnvelope, mul_assoc] using hBound

/-- The *signed* adverse top-transport energy not absorbed by the chosen
fraction ε of actual top H³ dissipation. Favorable top transport is never
charged to the remainder. -/
noncomputable def h3PathCanonicalTopAdverseAfterViscousShare
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (ε : ℝ) : ℝ → ℝ :=
  fun t => max 0
    (-velocityH3TransportDerivative3At u t -
      ε * velocityH3Dissipation3At u t)

/-- The signed, already-dissipation-absorbed adverse third-order cost is
nonnegative at every physical time. -/
theorem h3PathCanonical_topAdverseAfterViscousShare_nonneg
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (ε t : ℝ) :
    0 ≤ h3PathCanonicalTopAdverseAfterViscousShare u ε t := by
  unfold h3PathCanonicalTopAdverseAfterViscousShare
  exact le_max_left _ _

/-- Spatial Fourier interpolation controls the adverse signed third-order
transport left after taking ε D₃, instead of bounding the whole pairing
by a nonnegative energy term. The factor K^4 E₀ / ε^3 is explicit. -/
theorem h3PathCanonical_topAdverseAfterViscousShare_le_quarticRemainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hε : 0 < ε) :
    h3PathCanonicalTopAdverseAfterViscousShare u ε t ≤
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) ^ 4 *
        velocityH3Energy0At u t / ε ^ 3 := by
  let K : ℝ := 4398 *
    (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t))
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by norm_num)
      (mul_nonneg
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
        (Real.sqrt_nonneg _))
  have hTop := abs_velocityH3TransportDerivative3At_le_dissipation3_add_quartic_remainder
    hH3 hClass ht hK hε
      (h3PathCanonical_abs_thirdTransport_le_kineticGradientTopEnergy
        hH3 hClass ht)
  have hRaw : -velocityH3TransportDerivative3At u t -
      ε * velocityH3Dissipation3At u t ≤
      K ^ 4 * velocityH3Energy0At u t / ε ^ 3 := by
    have hNeg := neg_le_abs (velocityH3TransportDerivative3At u t)
    linarith only [hTop, hNeg]
  have hRNonneg : 0 ≤ K ^ 4 * velocityH3Energy0At u t / ε ^ 3 :=
    div_nonneg
      (mul_nonneg (pow_nonneg hK 4) (velocityH3Energy0At_nonneg u t))
      (pow_nonneg hε.le 3)
  unfold h3PathCanonicalTopAdverseAfterViscousShare
  change max 0 (-velocityH3TransportDerivative3At u t -
      ε * velocityH3Dissipation3At u t) ≤
    K ^ 4 * velocityH3Energy0At u t / ε ^ 3
  exact max_le hRNonneg hRaw

/-- Retain the signed top adverse cost and an explicit `(2-ε)` portion of
full viscous dissipation. Only ε>=0 is needed for the comparison D₃<=D. -/
theorem h3PathCanonical_deriv_add_retainedDissipation_le_topAdverseShare
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hε : 0 ≤ ε) :
    deriv (velocityH3EnergyAt u) t +
      (2 - ε) * velocityH3DissipationAt u t ≤
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t +
        h3PathCanonicalTopAdverseAfterViscousShare u ε t := by
  have hSigned := h3PathCanonical_deriv_add_dissipation_le_signedTopTransport
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

/-- The unconditional (but generally large) Young upper bound for the
signed third-order PDE remainder. This retains the exact 24 coefficient
from lower-order transport, rather than paying 4422 against all orders. -/
theorem h3PathCanonical_deriv_add_retainedDissipation_le_topYoungRemainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hε : 0 < ε) :
    deriv (velocityH3EnergyAt u) t +
      (2 - ε) * velocityH3DissipationAt u t ≤
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t +
      (4398 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t))) ^ 4 *
        velocityH3Energy0At u t / ε ^ 3 := by
  exact le_trans
    (h3PathCanonical_deriv_add_retainedDissipation_le_topAdverseShare
      hH3 hClass ht hε.le)
    (add_le_add_right
      (h3PathCanonical_topAdverseAfterViscousShare_le_quarticRemainder
        hH3 hClass ht hε)
      (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t))

/-- Normalized positive excess obtained by retaining the signed top-order
transport after spending ε D₃; the physical `(2-ε) D` stays nonnegative
when ε<=2. -/
noncomputable def h3PathCanonicalSignedTopAbsorptionRemainder
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (ε : ℝ) : ℝ → ℝ :=
  fun t => max 0
    (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t)) +
      h3PathCanonicalTopAdverseAfterViscousShare u ε t /
        velocityH3EnergyAt u t - 4422)

/-- The actual unabsorbed Riccati rate is bounded by the retained-dissipation
signed-top remainder at every H³ energy-class time, provided `0<=ε<=2`. -/
theorem h3PathCanonical_unabsorbed_le_signedTopAbsorptionRemainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hε : 0 ≤ ε) (hεTwo : ε ≤ 2) :
    h3PathCanonicalUnabsorbedRiccatiRate u t ≤
      h3PathCanonicalSignedTopAbsorptionRemainder u ε t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hDNonneg : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hRetained : 0 ≤ (2 - ε) * velocityH3DissipationAt u t :=
    mul_nonneg (sub_nonneg.mpr hεTwo) hDNonneg
  have hBound := h3PathCanonical_deriv_add_retainedDissipation_le_topAdverseShare
    hH3 hClass ht hε
  have hGrowth : deriv (velocityH3EnergyAt u) t ≤
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t +
        h3PathCanonicalTopAdverseAfterViscousShare u ε t := by
    linarith only [hBound, hRetained]
  have hSlope : deriv (velocityH3EnergyAt u) t /
      velocityH3EnergyAt u t ≤
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) +
        h3PathCanonicalTopAdverseAfterViscousShare u ε t /
          velocityH3EnergyAt u t := by
    apply (div_le_iff₀ hEPos).2
    calc
      deriv (velocityH3EnergyAt u) t ≤
          24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t +
            h3PathCanonicalTopAdverseAfterViscousShare u ε t := hGrowth
      _ = (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
            Real.sqrt (velocityH3EnergyAt u t)) +
            h3PathCanonicalTopAdverseAfterViscousShare u ε t /
              velocityH3EnergyAt u t) * velocityH3EnergyAt u t := by
          field_simp [ne_of_gt hEPos]
  rw [h3PathCanonical_unabsorbedRiccatiRate_eq_positiveAboveBaseline
    hH3 hClass ht]
  unfold h3PathCanonicalSignedTopAbsorptionRemainder
  exact max_le_max_left 0 (sub_le_sub_right hSlope 4422)

/-- A time-integrable *signed, top-dissipation-absorbed* remainder on one
terminal energy-class tail suffices for smooth continuation. It is an
explicit additional analytic premise, not a proved universal estimate. -/
theorem h3PathCanonical_extension_of_integrable_signedTopAbsorptionRemainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hε : 0 ≤ ε) (hεTwo : ε ≤ 2)
    (hInt : IntegrableOn (h3PathCanonicalSignedTopAbsorptionRemainder u ε)
      (Set.Ioo a T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hMeas := h3PathCanonical_unabsorbedRate_aestronglyMeasurableOnTail
    hH3 hClass
  have hDom : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioo a T)),
      ‖h3PathCanonicalUnabsorbedRiccatiRate u t‖ ≤
        h3PathCanonicalSignedTopAbsorptionRemainder u ε t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg (h3PathCanonical_unabsorbedRiccatiRate_nonneg u t)]
    exact h3PathCanonical_unabsorbed_le_signedTopAbsorptionRemainder
      hH3 hClass ht hε hεTwo
  have hU : IntegrableOn (h3PathCanonicalUnabsorbedRiccatiRate u)
      (Set.Ioo a T) := Integrable.mono' hInt hMeas hDom
  exact h3PathCanonical_extension_of_integrable_unabsorbedRiccatiRate
    hH3 hClass hU

/-- Hypothetical nonextension forces the signed top-order remainder,
*after* allowing an arbitrary fixed ε-share of top dissipation, to be
nonintegrable on every strict energy-class terminal tail. -/
theorem h3PathCanonical_signedTopAbsorptionRemainder_nonintegrable_on_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a d ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hd : d ∈ Set.Ioo a T)
    (hε : 0 ≤ ε) (hεTwo : ε ≤ 2) :
    ¬ IntegrableOn (h3PathCanonicalSignedTopAbsorptionRemainder u ε)
      (Set.Ioo d T) := by
  have hClassD : PreterminalH3EnergyClass u d T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hd.1) hd.2
  intro hInt
  exact hNoExtension
    (h3PathCanonical_extension_of_integrable_signedTopAbsorptionRemainder
      hH3 hClassD hε hεTwo hInt)

end Euclidean
end Bridge
end PrimeTensor
