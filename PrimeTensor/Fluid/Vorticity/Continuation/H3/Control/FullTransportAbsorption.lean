import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.ThirdOrderAbsorption
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.Transport.Dichotomy

/-!
# Full H³ transport absorption with an explicit low-order remainder

Combine E ≤ 1 + 3(E₀ + E₃), |T_H3| ≤ B E, and the spatial estimate
(3B) E₃ ≤ ε D₃ + (3B)⁴ E₀ / ε³. Since D₃ ≤ D, this gives

  |T_H3| ≤ ε D + R,   R = B + (3B + (3B)⁴ / ε³) E₀.

The exact balance therefore yields E' + (2 - ε)D ≤ R.
For 0 < ε < 2 this retains positive dissipation. Time integrability of the
remainder is not asserted. The final theorem obtains B from the existing
closed gradient-envelope transport estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable def h3FullTransportAbsorptionRemainderAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t B ε : ℝ) : ℝ :=
  B + (3 * B + (3 * B) ^ 4 / ε ^ 3) * velocityH3Energy0At u t

/-- Absorb the full transport bound into dissipation and a zeroth-order remainder. -/
theorem abs_velocityH3TransportDerivativeAt_le_dissipation_add_remainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t B ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (hB : 0 ≤ B) (hε : 0 < ε)
    (hTransport : |velocityH3TransportDerivativeAt u t| ≤
      B * velocityH3EnergyAt u t) :
    |velocityH3TransportDerivativeAt u t| ≤
      ε * velocityH3DissipationAt u t + h3FullTransportAbsorptionRemainderAt u t B ε := by
  have hEnergy :=
    velocityH3EnergyAt_le_one_add_three_mul_energy0_add_energy3_on_h3Path
      hH3 hClass ht
  have hTop := mul_velocityH3Energy3At_le_dissipation3_add_quartic_remainder
    hH3 hClass ht (show 0 ≤ 3 * B by positivity) hε
  have hD := velocityH3Dissipation3At_le_dissipationAt u t
  calc
    |velocityH3TransportDerivativeAt u t| ≤ B * velocityH3EnergyAt u t := hTransport
    _ ≤ B * (1 + 3 * (velocityH3Energy0At u t + velocityH3Energy3At u t)) :=
      mul_le_mul_of_nonneg_left hEnergy hB
    _ = B + 3 * B * velocityH3Energy0At u t + 3 * B * velocityH3Energy3At u t := by ring
    _ ≤ B + 3 * B * velocityH3Energy0At u t +
        (ε * velocityH3Dissipation3At u t +
          (3 * B) ^ 4 * velocityH3Energy0At u t / ε ^ 3) :=
      by linarith only [hTop]
    _ = ε * velocityH3Dissipation3At u t +
        h3FullTransportAbsorptionRemainderAt u t B ε := by
      unfold h3FullTransportAbsorptionRemainderAt
      ring
    _ ≤ ε * velocityH3DissipationAt u t +
        h3FullTransportAbsorptionRemainderAt u t B ε :=
      by
        have hScaled : ε * velocityH3Dissipation3At u t ≤
            ε * velocityH3DissipationAt u t :=
          mul_le_mul_of_nonneg_left hD hε.le
        linarith only [hScaled]

/-- The exact PDE balance retains the remaining fraction of full dissipation. -/
theorem deriv_velocityH3EnergyAt_add_remaining_dissipation_le_remainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t B ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (hB : 0 ≤ B) (hε : 0 < ε)
    (hTransport : |velocityH3TransportDerivativeAt u t| ≤
      B * velocityH3EnergyAt u t) :
    deriv (velocityH3EnergyAt u) t + (2 - ε) * velocityH3DissipationAt u t ≤
      h3FullTransportAbsorptionRemainderAt u t B ε := by
  have hAbs := abs_velocityH3TransportDerivativeAt_le_dissipation_add_remainder
    hH3 hClass ht hB hε hTransport
  have hBalance := deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
    hH3 hClass ht
  have hNeg := neg_le_abs (velocityH3TransportDerivativeAt u t)
  nlinarith

/-- Supply the coefficient from the closed gradient-envelope commutator estimate. -/
theorem abs_velocityH3TransportDerivativeAt_le_absorbed_gradient_remainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t ε : ℝ} {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hGradient : ∀ s : ℝ, s ∈ Set.Ioo a T → VelocityGradientEnvelope u h s)
    (ht : t ∈ Set.Ioo a T) (hε : 0 < ε) :
    |velocityH3TransportDerivativeAt u t| ≤
      ε * velocityH3DissipationAt u t +
        h3FullTransportAbsorptionRemainderAt u t (4422 * (1 + |h t|)) ε := by
  have hTransport :=
    (h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3 hClass hGradient t ht).2
  exact abs_velocityH3TransportDerivativeAt_le_dissipation_add_remainder
    hH3 hClass ht (by positivity) hε hTransport

end Euclidean
end Bridge
end PrimeTensor
