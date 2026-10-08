import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.NormalizedRemainder
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Tail.Low.From.Derivative.Identities
import PrimeTensor.Fluid.Vorticity.Continuation.H3.BKM.Closure

/-!
# Remove the kinetic factor from the normalized absorption remainder

The closed kinetic-energy identity bounds E₀(t) by E₀(b) after an interior
anchor b. For B ≥ 1 and absorption budget ε = 2, the explicit remainder is
at most (1 + 14 E₀(b)) B⁴. Thus integrability of B⁴/E on that later tail
suffices for continuation. The kinetic bound is derived from the PDE;
the quartic normalized coefficient remains an explicit temporal hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- A kinetic ceiling absorbs all lower powers of a coefficient B ≥ 1. -/
theorem h3FullTransportAbsorptionRemainderAt_le_kinetic_quartic
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t B M : ℝ} (hB : 1 ≤ B)
    (hKinetic : velocityH3Energy0At u t ≤ M) :
    h3FullTransportAbsorptionRemainderAt u t B 2 ≤ (1 + 14 * M) * B ^ 4 := by
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hSquare : B ≤ B ^ 2 := by
    nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hB)]
  have hSquareOne : 1 ≤ B ^ 2 := le_trans hB hSquare
  have hFourth : B ≤ B ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg B) (sub_nonneg.mpr hSquareOne)]
  have hCoefficient : 3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3 ≤ 14 * B ^ 4 := by
    nlinarith [sq_nonneg (B ^ 2)]
  have hE0 := velocityH3Energy0At_nonneg u t
  have hProduct := mul_le_mul_of_nonneg_right hCoefficient hE0
  have hCeiling := mul_le_mul_of_nonneg_left hKinetic
    (show 0 ≤ 14 * B ^ 4 by positivity)
  unfold h3FullTransportAbsorptionRemainderAt
  nlinarith only [hFourth, hProduct, hCeiling]

/-- The kinetic-energy ceiling is automatic on each anchored strict subtail. -/
theorem deriv_velocityH3EnergyAt_le_anchored_quartic_majorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo b T) (hB : 1 ≤ B)
    (hTransport : |velocityH3TransportDerivativeAt u t| ≤
      B * velocityH3EnergyAt u t) :
    deriv (velocityH3EnergyAt u) t ≤
      ((1 + 14 * velocityH3Energy0At u b) * (B ^ 4 / velocityH3EnergyAt u t)) *
        velocityH3EnergyAt u t := by
  have htOld : t ∈ Set.Ioo a T := ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hAnti := antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed hH3 hClass
  have hKinetic : velocityH3Energy0At u t ≤ velocityH3Energy0At u b :=
    hAnti hb htOld (le_of_lt ht.1)
  have hRemainder := h3FullTransportAbsorptionRemainderAt_le_kinetic_quartic hB hKinetic
  have hAbsorbed := deriv_velocityH3EnergyAt_add_remaining_dissipation_le_remainder
    hH3 hClass htOld (le_trans zero_le_one hB) (show (0 : ℝ) < 2 by norm_num)
    hTransport
  have hDerivative : deriv (velocityH3EnergyAt u) t ≤
      h3FullTransportAbsorptionRemainderAt u t B 2 := by
    simpa only [sub_self, zero_mul, add_zero] using hAbsorbed
  have hEnergyPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hEnergyNe : velocityH3EnergyAt u t ≠ 0 := ne_of_gt hEnergyPos
  calc
    deriv (velocityH3EnergyAt u) t ≤ (1 + 14 * velocityH3Energy0At u b) * B ^ 4 :=
      le_trans hDerivative hRemainder
    _ = ((1 + 14 * velocityH3Energy0At u b) * (B ^ 4 / velocityH3EnergyAt u t)) *
        velocityH3EnergyAt u t := by
      field_simp [hEnergyNe]

/-- Only the normalized quartic coefficient needs a temporal integrability input. -/
theorem h3PathExtension_of_integrableQuarticTransportCoefficientOnSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) (hb : b ∈ Set.Ioo a T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo b T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo b T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hQuartic : MeasureTheory.IntegrableOn
      (fun t : ℝ => (B t) ^ 4 / velocityH3EnergyAt u t) (Set.Ioo b T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hClassB : PreterminalH3EnergyClass u b T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hb.1) hb.2
  have hMajorant : MeasureTheory.IntegrableOn
      (fun t : ℝ => (1 + 14 * velocityH3Energy0At u b) *
        ((B t) ^ 4 / velocityH3EnergyAt u t)) (Set.Ioo b T) :=
    hQuartic.const_mul _
  apply h3PathExtension_of_integrableLinearEnergyGrowthMajorantOnTail
    hH3 hClassB hMajorant
  intro t ht
  exact deriv_velocityH3EnergyAt_le_anchored_quartic_majorant
    hH3 hClass hb ht (hB t ht) (hTransport t ht)

/-- Specialize the quartic criterion to the closed gradient-envelope coefficient. -/
theorem h3PathExtension_of_integrableQuarticGradientCoefficientOnSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) (hb : b ∈ Set.Ioo a T)
    (hGradient : ∀ t : ℝ, t ∈ Set.Ioo b T → VelocityGradientEnvelope u h t)
    (hQuartic : MeasureTheory.IntegrableOn
      (fun t : ℝ => (4422 * (1 + |h t|)) ^ 4 / velocityH3EnergyAt u t)
      (Set.Ioo b T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hClassB : PreterminalH3EnergyClass u b T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hb.1) hb.2
  apply h3PathExtension_of_integrableQuarticTransportCoefficientOnSubtail
    hH3 hClass hb _ _ hQuartic
  · intro t ht
    nlinarith [abs_nonneg (h t)]
  · intro t ht
    exact (h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3 hClassB hGradient t ht).2

/-- The quartic coefficient is strictly better exactly above this energy threshold. -/
theorem h3_quartic_coefficient_lt_direct_iff
    {B C E : ℝ} (hB : 0 < B) (hE : 0 < E) :
    C * (B ^ 4 / E) < B ↔ C * B ^ 3 < E := by
  have hRewrite : C * (B ^ 4 / E) = (B * (C * B ^ 3)) / E := by ring
  rw [hRewrite, div_lt_iff₀ hE]
  constructor
  · intro h
    exact lt_of_mul_lt_mul_left h (le_of_lt hB)
  · intro h
    exact mul_lt_mul_of_pos_left h hB

/-- Retain the better of direct transport growth and spatial absorption at each time. -/
theorem deriv_velocityH3EnergyAt_le_min_direct_quartic_majorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo b T) (hB : 1 ≤ B)
    (hTransport : |velocityH3TransportDerivativeAt u t| ≤
      B * velocityH3EnergyAt u t) :
    deriv (velocityH3EnergyAt u) t ≤
      min B ((1 + 14 * velocityH3Energy0At u b) * (B ^ 4 / velocityH3EnergyAt u t)) *
        velocityH3EnergyAt u t := by
  have htOld : t ∈ Set.Ioo a T := ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hBalance := deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
    hH3 hClass htOld
  have hDirect : deriv (velocityH3EnergyAt u) t ≤ B * velocityH3EnergyAt u t := by
    have hD := velocityH3DissipationAt_nonneg u t
    have hNeg := neg_le_abs (velocityH3TransportDerivativeAt u t)
    linarith only [hBalance, hD, hNeg, hTransport]
  have hQuartic := deriv_velocityH3EnergyAt_le_anchored_quartic_majorant
    hH3 hClass hb ht hB hTransport
  by_cases hCompare : B ≤
      (1 + 14 * velocityH3Energy0At u b) * (B ^ 4 / velocityH3EnergyAt u t)
  · simpa only [min_eq_left hCompare] using hDirect
  · simpa only [min_eq_right (le_of_not_ge hCompare)] using hQuartic

/-- Neither coefficient must be integrable separately when their minimum is integrable. -/
theorem h3PathExtension_of_integrableMinDirectQuarticCoefficientOnSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) (hb : b ∈ Set.Ioo a T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo b T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo b T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hMinimum : MeasureTheory.IntegrableOn
      (fun t : ℝ => min (B t)
        ((1 + 14 * velocityH3Energy0At u b) * ((B t) ^ 4 / velocityH3EnergyAt u t)))
      (Set.Ioo b T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hClassB : PreterminalH3EnergyClass u b T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hb.1) hb.2
  apply h3PathExtension_of_integrableLinearEnergyGrowthMajorantOnTail
    hH3 hClassB hMinimum
  intro t ht
  exact deriv_velocityH3EnergyAt_le_min_direct_quartic_majorant
    hH3 hClass hb ht (hB t ht) (hTransport t ht)

/-- Apply the minimum criterion to the actual gradient-envelope coefficient. -/
theorem h3PathExtension_of_integrableMinDirectQuarticGradientOnSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) (hb : b ∈ Set.Ioo a T)
    (hGradient : ∀ t : ℝ, t ∈ Set.Ioo b T → VelocityGradientEnvelope u h t)
    (hMinimum : MeasureTheory.IntegrableOn
      (fun t : ℝ => min (4422 * (1 + |h t|))
        ((1 + 14 * velocityH3Energy0At u b) *
          ((4422 * (1 + |h t|)) ^ 4 / velocityH3EnergyAt u t))) (Set.Ioo b T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hClassB : PreterminalH3EnergyClass u b T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hb.1) hb.2
  apply h3PathExtension_of_integrableMinDirectQuarticCoefficientOnSubtail
    hH3 hClass hb _ _ hMinimum
  · intro t ht
    nlinarith [abs_nonneg (h t)]
  · intro t ht
    exact (h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3 hClassB hGradient t ht).2

end Euclidean
end Bridge
end PrimeTensor
