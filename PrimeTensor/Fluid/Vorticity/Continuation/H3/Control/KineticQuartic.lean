import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.NormalizedRemainder
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Tail.Low.From.Derivative.Identities
import PrimeTensor.Fluid.Vorticity.Continuation.H3.BKM.Closure

/-!
# Remove the kinetic factor from the normalized absorption remainder

The closed kinetic-energy identity bounds E₀(t) by E₀(b) after an interior
anchor b. For B ≥ 1 and absorption budget ε = 2, the explicit remainder is
at most (1 + (105/8) E₀(b)) B⁴. Thus integrability of B⁴/E on that later tail
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
    h3FullTransportAbsorptionRemainderAt u t B 2 ≤ (1 + (105 / 8) * M) * B ^ 4 := by
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hSquare : B ≤ B ^ 2 := by
    nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hB)]
  have hSquareOne : 1 ≤ B ^ 2 := le_trans hB hSquare
  have hFourth : B ≤ B ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg B) (sub_nonneg.mpr hSquareOne)]
  have hCoefficient : 3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3 ≤ (105 / 8) * B ^ 4 := by
    nlinarith [sq_nonneg (B ^ 2)]
  have hE0 := velocityH3Energy0At_nonneg u t
  have hProduct := mul_le_mul_of_nonneg_right hCoefficient hE0
  have hCeiling := mul_le_mul_of_nonneg_left hKinetic
    (show 0 ≤ (105 / 8) * B ^ 4 by positivity)
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
      ((1 + (105 / 8) * velocityH3Energy0At u b) * (B ^ 4 / velocityH3EnergyAt u t)) *
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
    deriv (velocityH3EnergyAt u) t ≤ (1 + (105 / 8) * velocityH3Energy0At u b) * B ^ 4 :=
      le_trans hDerivative hRemainder
    _ = ((1 + (105 / 8) * velocityH3Energy0At u b) * (B ^ 4 / velocityH3EnergyAt u t)) *
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
      (fun t : ℝ => (1 + (105 / 8) * velocityH3Energy0At u b) *
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
      min B ((1 + (105 / 8) * velocityH3Energy0At u b) * (B ^ 4 / velocityH3EnergyAt u t)) *
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
      (1 + (105 / 8) * velocityH3Energy0At u b) * (B ^ 4 / velocityH3EnergyAt u t)
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
        ((1 + (105 / 8) * velocityH3Energy0At u b) * ((B t) ^ 4 / velocityH3EnergyAt u t)))
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
        ((1 + (105 / 8) * velocityH3Energy0At u b) *
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

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Under nonextension, the adaptive minimum coefficient is nonintegrable on
 every strict anchored subtail. -/
theorem not_integrableOn_minDirectQuarticCoefficient_on_strictSubtail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) (hb : b ∈ Set.Ioo a T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo b T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo b T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t) :
    ¬ MeasureTheory.IntegrableOn
      (fun t : ℝ => min (B t)
        ((1 + (105 / 8) * velocityH3Energy0At u b) *
          ((B t) ^ 4 / velocityH3EnergyAt u t))) (Set.Ioo b T) := by
  intro hMinimum
  exact hNoExtension
    (h3PathExtension_of_integrableMinDirectQuarticCoefficientOnSubtail
      hH3 hClass hb hB hTransport hMinimum)

end Euclidean
end Bridge
end PrimeTensor

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Retain the exact ε = 2 remainder before bounding lower powers of B. -/
theorem h3FullTransportAbsorptionRemainderAt_le_exact_kinetic_remainder
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t B M : ℝ} (hB : 0 ≤ B)
    (hKinetic : velocityH3Energy0At u t ≤ M) :
    h3FullTransportAbsorptionRemainderAt u t B 2 ≤
      B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M := by
  have hCoefficient : 0 ≤ 3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3 := by
    positivity
  have hProduct := mul_le_mul_of_nonneg_right hKinetic hCoefficient
  unfold h3FullTransportAbsorptionRemainderAt
  nlinarith

/-- The exact anchored remainder gives a sharper normalized growth majorant. -/
theorem deriv_velocityH3EnergyAt_le_anchored_exact_quartic_majorant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo b T)
    (hB : 0 ≤ B)
    (hTransport : |velocityH3TransportDerivativeAt u t| ≤
      B * velocityH3EnergyAt u t) :
    deriv (velocityH3EnergyAt u) t ≤
      ((B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) *
        velocityH3Energy0At u b) / velocityH3EnergyAt u t) *
        velocityH3EnergyAt u t := by
  have htOld : t ∈ Set.Ioo a T := ⟨lt_trans hb.1 ht.1, ht.2⟩
  have hAnti := antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed hH3 hClass
  have hKinetic : velocityH3Energy0At u t ≤ velocityH3Energy0At u b :=
    hAnti hb htOld (le_of_lt ht.1)
  have hRemainder := h3FullTransportAbsorptionRemainderAt_le_exact_kinetic_remainder
    (B := B) hB hKinetic
  have hAbsorbed := deriv_velocityH3EnergyAt_add_remaining_dissipation_le_remainder
    hH3 hClass htOld (by positivity) (show (0 : ℝ) < 2 by norm_num) hTransport
  have hDerivative : deriv (velocityH3EnergyAt u) t ≤
      h3FullTransportAbsorptionRemainderAt u t B 2 := by
    simpa only [sub_self, zero_mul, add_zero] using hAbsorbed
  have hEnergyPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hEnergyNe : velocityH3EnergyAt u t ≠ 0 := ne_of_gt hEnergyPos
  calc
    deriv (velocityH3EnergyAt u) t ≤
        B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * velocityH3Energy0At u b :=
      le_trans hDerivative hRemainder
    _ = ((B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) *
        velocityH3Energy0At u b) / velocityH3EnergyAt u t) *
        velocityH3EnergyAt u t := by
      field_simp [hEnergyNe]

/-- Integrability of the minimum of direct and exact anchored growth suffices. -/
theorem h3PathExtension_of_integrableMinDirectExactQuarticCoefficientOnSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) (hb : b ∈ Set.Ioo a T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo b T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo b T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t)
    (hMinimum : MeasureTheory.IntegrableOn
      (fun t : ℝ => min (B t)
        ((B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
          velocityH3Energy0At u b) / velocityH3EnergyAt u t)) (Set.Ioo b T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hClassB : PreterminalH3EnergyClass u b T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hb.1) hb.2
  apply h3PathExtension_of_integrableLinearEnergyGrowthMajorantOnTail
    hH3 hClassB hMinimum
  intro t ht
  have hDirect : deriv (velocityH3EnergyAt u) t ≤ B t * velocityH3EnergyAt u t := by
    have hBalance := deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass (⟨lt_trans hb.1 ht.1, ht.2⟩)
    have hD := velocityH3DissipationAt_nonneg u t
    have hNeg := neg_le_abs (velocityH3TransportDerivativeAt u t)
    linarith only [hBalance, hD, hNeg, hTransport t ht]
  have hExact := deriv_velocityH3EnergyAt_le_anchored_exact_quartic_majorant
    hH3 hClass hb ht (le_trans zero_le_one (hB t ht)) (hTransport t ht)
  by_cases hCompare : B t ≤
      (B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
        velocityH3Energy0At u b) / velocityH3EnergyAt u t
  · simpa only [min_eq_left hCompare] using hDirect
  · simpa only [min_eq_right (le_of_not_ge hCompare)] using hExact

end Euclidean
end Bridge
end PrimeTensor

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Under nonextension, the exact adaptive minimum coefficient is
nonintegrable on every strict anchored subtail. -/
theorem not_integrableOn_minDirectExactQuarticCoefficient_on_strictSubtail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) (hb : b ∈ Set.Ioo a T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo b T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo b T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t) :
    ¬ MeasureTheory.IntegrableOn
      (fun t : ℝ => min (B t)
        ((B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
          velocityH3Energy0At u b) / velocityH3EnergyAt u t)) (Set.Ioo b T) := by
  intro hMinimum
  exact hNoExtension
    (h3PathExtension_of_integrableMinDirectExactQuarticCoefficientOnSubtail
      hH3 hClass hb hB hTransport hMinimum)

end Euclidean
end Bridge
end PrimeTensor

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- The exact absorbed coefficient beats direct transport precisely above its
anchored energy threshold. -/
theorem h3_exact_quartic_coefficient_lt_direct_iff
    {B M E : ℝ} (hB : 0 < B) (hE : 0 < E) :
    (B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M) / E < B ↔
      1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M < E := by
  have hRewrite :
      B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M =
        B * (1 + (3 + (81 / 8 : ℝ) * B ^ 3) * M) := by
    ring
  rw [hRewrite, div_lt_iff₀ hE]
  constructor
  · intro h
    exact lt_of_mul_lt_mul_left h (le_of_lt hB)
  · intro h
    exact mul_lt_mul_of_pos_left h hB

end Euclidean
end Bridge
end PrimeTensor

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- The exact anchored coefficient is bounded by the coarser 105/8 coefficient. -/
theorem exact_kinetic_quartic_coefficient_le_sharp_coefficient
    {B M E : ℝ} (hB : 1 ≤ B) (hM : 0 ≤ M) (hE : 0 < E) :
    (B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M) / E ≤
      ((1 + (105 / 8 : ℝ) * M) * B ^ 4) / E := by
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hSquare : B ≤ B ^ 2 := by
    nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hB)]
  have hFourth : B ≤ B ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg B) (sub_nonneg.mpr (le_trans hB hSquare))]
  have hThree : 3 * B ≤ 3 * B ^ 4 := by
    exact mul_le_mul_of_nonneg_left hFourth (by norm_num)
  have hThreeM := mul_le_mul_of_nonneg_right hThree hM
  have hBM := mul_le_mul_of_nonneg_right hFourth hM
  have hNumerator :
      B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M ≤
        (1 + (105 / 8 : ℝ) * M) * B ^ 4 := by
    nlinarith [hThreeM, hBM]
  exact div_le_div_of_nonneg_right hNumerator (le_of_lt hE)

end Euclidean
end Bridge
end PrimeTensor

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Exact adaptive continuation criterion for the closed gradient envelope. -/
theorem h3PathExtension_of_integrableMinDirectExactQuarticGradientOnSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) (hb : b ∈ Set.Ioo a T)
    (hGradient : ∀ t : ℝ, t ∈ Set.Ioo b T → VelocityGradientEnvelope u h t)
    (hMinimum : MeasureTheory.IntegrableOn
      (fun t : ℝ => min (4422 * (1 + |h t|))
        ((4422 * (1 + |h t|) +
          (3 * (4422 * (1 + |h t|)) +
            (3 * (4422 * (1 + |h t|))) ^ 4 / (2 : ℝ) ^ 3) *
            velocityH3Energy0At u b) /
          velocityH3EnergyAt u t)) (Set.Ioo b T)) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  have hClassB : PreterminalH3EnergyClass u b T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hb.1) hb.2
  apply h3PathExtension_of_integrableMinDirectExactQuarticCoefficientOnSubtail
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

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Under nonextension, the exact gradient-specialized adaptive coefficient is
nonintegrable on every strict anchored subtail. -/
theorem not_integrableOn_minDirectExactQuarticGradient_on_strictSubtail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) (hb : b ∈ Set.Ioo a T)
    (hGradient : ∀ t : ℝ, t ∈ Set.Ioo b T → VelocityGradientEnvelope u h t) :
    ¬ MeasureTheory.IntegrableOn
      (fun t : ℝ => min (4422 * (1 + |h t|))
        ((4422 * (1 + |h t|) +
          (3 * (4422 * (1 + |h t|)) +
            (3 * (4422 * (1 + |h t|))) ^ 4 / (2 : ℝ) ^ 3) *
            velocityH3Energy0At u b) /
          velocityH3EnergyAt u t)) (Set.Ioo b T) := by
  intro hMinimum
  exact hNoExtension
    (h3PathExtension_of_integrableMinDirectExactQuarticGradientOnSubtail
      hH3 hClass hb hGradient hMinimum)

end Euclidean
end Bridge
end PrimeTensor

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- The ε = 2 remainder is no larger than any remainder with 0 < ε ≤ 2. -/
theorem h3FullTransportAbsorptionRemainderAt_two_le_of_epsilon
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {t B ε : ℝ} (hε : 0 < ε) (hεTwo : ε ≤ 2) :
    h3FullTransportAbsorptionRemainderAt u t B 2 ≤
      h3FullTransportAbsorptionRemainderAt u t B ε := by
  have hE0 := velocityH3Energy0At_nonneg u t
  have hε3 : ε ^ 3 ≤ (2 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hε.le hεTwo 3
  have hFraction :
      (3 * B) ^ 4 / (2 : ℝ) ^ 3 ≤ (3 * B) ^ 4 / ε ^ 3 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    exact mul_le_mul_of_nonneg_left hε3 (by positivity)
  have hProduct := mul_le_mul_of_nonneg_right hFraction hE0
  unfold h3FullTransportAbsorptionRemainderAt
  nlinarith

end Euclidean
end Bridge
end PrimeTensor

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Exact adaptive continuation/nonextension dichotomy on one anchored tail. -/
theorem h3PathExactAdaptiveQuarticContinuationOrObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {B : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) (hb : b ∈ Set.Ioo a T)
    (hB : ∀ t : ℝ, t ∈ Set.Ioo b T → 1 ≤ B t)
    (hTransport : ∀ t : ℝ, t ∈ Set.Ioo b T →
      |velocityH3TransportDerivativeAt u t| ≤ B t * velocityH3EnergyAt u t) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ¬ MeasureTheory.IntegrableOn
      (fun t : ℝ => min (B t)
        ((B t + (3 * B t + (3 * B t) ^ 4 / (2 : ℝ) ^ 3) *
          velocityH3Energy0At u b) / velocityH3EnergyAt u t)) (Set.Ioo b T) := by
  by_cases hExtension : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (not_integrableOn_minDirectExactQuarticCoefficient_on_strictSubtail_of_noH3PathExtension
        hH3 hExtension hClass hb hB hTransport)

/-- Gradient-envelope specialization of the exact adaptive dichotomy. -/
theorem h3PathExactAdaptiveGradientContinuationOrObstruction
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ} {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) (hb : b ∈ Set.Ioo a T)
    (hGradient : ∀ t : ℝ, t ∈ Set.Ioo b T → VelocityGradientEnvelope u h t) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ¬ MeasureTheory.IntegrableOn
      (fun t : ℝ => min (4422 * (1 + |h t|))
        ((4422 * (1 + |h t|) +
          (3 * (4422 * (1 + |h t|)) +
            (3 * (4422 * (1 + |h t|))) ^ 4 / (2 : ℝ) ^ 3) *
            velocityH3Energy0At u b) /
          velocityH3EnergyAt u t)) (Set.Ioo b T) := by
  have hB : ∀ t : ℝ, t ∈ Set.Ioo b T → 1 ≤ 4422 * (1 + |h t|) := by
    intro t ht
    nlinarith [abs_nonneg (h t)]
  have hClassB : PreterminalH3EnergyClass u b T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hb.1) hb.2
  have hTransport : ∀ t : ℝ, t ∈ Set.Ioo b T →
      |velocityH3TransportDerivativeAt u t| ≤
        (4422 * (1 + |h t|)) * velocityH3EnergyAt u t := by
    intro t ht
    exact (h3TransportControlledOnTail_of_h3Path_exactPDEPairing
      h3PathEnergyClassProducesPDEPairingIntegrability_closed
      hH3 hClassB hGradient t ht).2
  exact h3PathExactAdaptiveQuarticContinuationOrObstruction
    hH3 hClass hb hB hTransport

end Euclidean
end Bridge
end PrimeTensor

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Universal strict-subtail form of the exact gradient adaptive dichotomy. -/
theorem h3PathExactAdaptiveGradientContinuationOrObstruction_on_every_strictSubtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {h : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hGradient : ∀ t : ℝ, t ∈ Set.Ioo a T → VelocityGradientEnvelope u h t) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ¬ MeasureTheory.IntegrableOn
        (fun t : ℝ => min (4422 * (1 + |h t|))
          ((4422 * (1 + |h t|) +
            (3 * (4422 * (1 + |h t|)) +
              (3 * (4422 * (1 + |h t|))) ^ 4 / (2 : ℝ) ^ 3) *
              velocityH3Energy0At u b) /
            velocityH3EnergyAt u t)) (Set.Ioo b T) := by
  by_cases hExtension : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · right
    intro b hb
    apply not_integrableOn_minDirectExactQuarticGradient_on_strictSubtail_of_noH3PathExtension
      hH3 hExtension hClass hb
    intro t ht
    exact hGradient t ⟨lt_trans hb.1 ht.1, ht.2⟩

end Euclidean
end Bridge
end PrimeTensor

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- The exact normalized coefficient is monotone in the anchored kinetic
ceiling. -/
theorem exact_kinetic_quartic_coefficient_mono_mass
    {B M₁ M₂ E : ℝ} (hB : 0 ≤ B) (hMass : M₁ ≤ M₂) (hE : 0 < E) :
    (B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M₁) / E ≤
      (B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) * M₂) / E := by
  have hCoefficient : 0 ≤ 3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3 := by
    positivity
  have hNumerator :=
    add_le_add_left (mul_le_mul_of_nonneg_left hMass hCoefficient) B
  exact div_le_div_of_nonneg_right (by simpa [add_comm] using hNumerator) (le_of_lt hE)

end Euclidean
end Bridge
end PrimeTensor

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Later anchors improve the exact coefficient because kinetic energy is
antitone on the closed energy-class tail. -/
theorem exact_kinetic_quartic_coefficient_mono_anchor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b c t B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) (hc : c ∈ Set.Ioo b T)
    (ht : t ∈ Set.Ioo c T) (hB : 0 ≤ B) :
    (B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) *
      velocityH3Energy0At u c) / velocityH3EnergyAt u t ≤
    (B + (3 * B + (3 * B) ^ 4 / (2 : ℝ) ^ 3) *
      velocityH3Energy0At u b) / velocityH3EnergyAt u t := by
  have hAnti := antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed hH3 hClass
  have hMass : velocityH3Energy0At u c ≤ velocityH3Energy0At u b :=
    hAnti hb ⟨lt_trans hb.1 hc.1, hc.2⟩ (le_of_lt hc.1)
  have hEnergyPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  exact exact_kinetic_quartic_coefficient_mono_mass
    hB hMass hEnergyPos

end Euclidean
end Bridge
end PrimeTensor
