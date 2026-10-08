import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FullTransportAbsorption
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Integrability

/-!
# Continuation from the normalized spatial absorption remainder

For 0 < ε ≤ 2, full transport absorption gives E' ≤ R. Since E ≥ 1,
this is E' ≤ (R / E) E. Thus time integrability of R / E on one
energy-class tail suffices for continuation. The gradient specialization
uses ε = 2 and B(t) = 4422 (1 + |h(t)|).

The integrability hypothesis is retained explicitly: the spatial absorption
estimate alone does not establish it. No new Fourier interpolation estimate
or unconditional continuation statement is asserted here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Normalize the absorbed remainder by the strictly positive H³ energy. -/
theorem deriv_velocityH3EnergyAt_le_normalizedAbsorptionRemainder_mul_energy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t B ε : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (hB : 0 ≤ B)
    (hε : 0 < ε) (hεTwo : ε ≤ 2)
    (hTransport : |velocityH3TransportDerivativeAt u t| ≤
      B * velocityH3EnergyAt u t) :
    deriv (velocityH3EnergyAt u) t ≤
      (h3FullTransportAbsorptionRemainderAt u t B ε / velocityH3EnergyAt u t) *
        velocityH3EnergyAt u t := by
  have hAbsorbed := deriv_velocityH3EnergyAt_add_remaining_dissipation_le_remainder
    hH3 hClass ht hB hε hTransport
  have hRemaining : 0 ≤ (2 - ε) * velocityH3DissipationAt u t :=
    mul_nonneg (sub_nonneg.mpr hεTwo) (velocityH3DissipationAt_nonneg u t)
  have hEnergyPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hCancel :
      (h3FullTransportAbsorptionRemainderAt u t B ε / velocityH3EnergyAt u t) *
        velocityH3EnergyAt u t = h3FullTransportAbsorptionRemainderAt u t B ε := by
    have hEnergyNe : velocityH3EnergyAt u t ≠ 0 := ne_of_gt hEnergyPos
    field_simp [hEnergyNe]
  rw [hCancel]
  linarith only [hAbsorbed, hRemaining]

/-- Integrability is needed only after division by the energy. -/
theorem h3PathExtension_of_integrableNormalizedAbsorptionRemainderOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a ε : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hε : 0 < ε) (hεTwo : ε ≤ 2)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo a T → 0 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo a T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hRemainder : MeasureTheory.IntegrableOn
      (fun t : ℝ => h3FullTransportAbsorptionRemainderAt u t (B t) ε /
        velocityH3EnergyAt u t) (Set.Ioo a T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  apply h3PathExtension_of_integrableLinearEnergyGrowthMajorantOnTail
    hH3 hClass hRemainder
  intro t ht
  exact deriv_velocityH3EnergyAt_le_normalizedAbsorptionRemainder_mul_energy
    hH3 hClass ht (hB t ht) hε hεTwo (hTransport t ht)

/-- Use the actual gradient envelope and the full absorption budget ε = 2. -/
theorem h3PathExtension_of_integrableNormalizedGradientRemainderOnTail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hGradient : ∀ t : ℝ, t ∈ Set.Ioo a T → VelocityGradientEnvelope u h t)
    (hRemainder : MeasureTheory.IntegrableOn
      (fun t : ℝ => h3FullTransportAbsorptionRemainderAt u t
        (4422 * (1 + |h t|)) 2 / velocityH3EnergyAt u t) (Set.Ioo a T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  apply h3PathExtension_of_integrableNormalizedAbsorptionRemainderOnTail
    hH3 hClass (by norm_num) (by norm_num) _ _ hRemainder
  · intro t ht
    positivity
  · intro t ht
    exact (h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3 hClass hGradient t ht).2

end Euclidean
end Bridge
end PrimeTensor
