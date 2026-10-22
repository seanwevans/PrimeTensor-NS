import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalIntegratedKineticLogPhaseBudget244
import Mathlib.Tactic

/-!
# Signed fifth-order phase action is constrained by downward log variation of D3

The actual physical top-phase source is exactly

  Ctop = -(E2^2 E0 / (E0 D3)^2) * D3'.

The positive spectral factor has the sharp Cauchy ceiling

  0 <= (E2^2 E0 / (E0 D3)^2) * D3 <= 1.

Consequently

  Ctop <= max (-D3', 0) / D3.

A positive top contribution requires decreasing top dissipation D3, even
though the fifth mass and the nonnegative phase defect contribute with
positive signs in the alternative fifth-plus-phase-minus-cubic expression.
An integrated bound holds when the displayed rates are integrable on a
strict compact physical time interval. It makes no monotonicity claim for D3
and does not infer a uniform terminal bound on its negative log variation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- Exact scalar Fourier Cauchy constraint on the coefficient multiplying
negative top-dissipation growth, with no assumption on the sign of D3'. -/
theorem h3_scalar_topPhaseWeight_nonneg_mulTop_le_one244
    (E0 E2 D : ℝ) (hE0 : 0 < E0) (hD : 0 < D)
    (hCauchy : E2 ^ 2 ≤ E0 * D) :
    0 ≤ E2 ^ 2 * E0 / (E0 * D) ^ 2 ∧
      (E2 ^ 2 * E0 / (E0 * D) ^ 2) * D ≤ 1 := by
  have hA : 0 < E0 * D := mul_pos hE0 hD
  have hProduct : E2 ^ 2 * (E0 * D) ≤ (E0 * D) ^ 2 := by
    calc
      E2 ^ 2 * (E0 * D) ≤ (E0 * D) * (E0 * D) :=
        mul_le_mul_of_nonneg_right hCauchy hA.le
      _ = (E0 * D) ^ 2 := by ring
  constructor
  · exact div_nonneg (mul_nonneg (sq_nonneg _) hE0.le) (sq_nonneg _)
  · calc
      (E2 ^ 2 * E0 / (E0 * D) ^ 2) * D =
          (E2 ^ 2 * (E0 * D)) / (E0 * D) ^ 2 := by ring
      _ ≤ 1 := (div_le_iff₀ (pow_pos hA 2)).2 (by
        simpa only [one_mul] using hProduct)

/-- A weighted negative derivative can only supply the DOWNWARD part of
logarithmic variation, provided its weight times D is at most one. -/
theorem h3_scalar_weightedTop_le_negativeLogVariation244
    (w D d : ℝ) (hw : 0 ≤ w) (hD : 0 < D) (hwD : w * D ≤ 1) :
    -(w * d) ≤ max (-d) 0 / D := by
  have hWeightBound : w ≤ 1 / D := by
    apply (mul_le_mul_iff_of_pos_right hD).mp
    calc
      w * D ≤ 1 := hwD
      _ = (1 / D) * D := by field_simp [ne_of_gt hD]
  by_cases hd : d ≤ 0
  · have hMinusNonneg : 0 ≤ -d := neg_nonneg.mpr hd
    have hMax : max (-d) 0 = -d := max_eq_left hMinusNonneg
    calc
      -(w * d) = w * (-d) := by ring
      _ ≤ (1 / D) * (-d) :=
        mul_le_mul_of_nonneg_right hWeightBound hMinusNonneg
      _ = max (-d) 0 / D := by rw [hMax]; ring
  · have hdNonneg : 0 ≤ d := le_of_lt (lt_of_not_ge hd)
    have hTopNonpos : -(w * d) ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg hw hdNonneg)
    have hVariationNonneg : 0 ≤ max (-d) 0 / D :=
      div_nonneg (le_max_right _ _) hD.le
    exact hTopNonpos.trans hVariationNonneg

/-- Exact actual-PDE identification, preserving the complete fifth-order
Fourier mass and the signed phase remainder: the top source is the weighted
NEGATIVE ordinary derivative of the physical fourth-radial top mass. -/
theorem h3Path_globalTopPhase_eq_weighted_negativeTopDerivative244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T) :
    h3PathTopFourierGlobalTopPhaseNormalizedRate244 hH3 hClass r hr =
      -((velocityH3Energy2At u r ^ 2 * velocityH3Energy0At u r /
          (velocityH3Energy0At u r *
            h3TerminalPhysicalTopDissipation3Path hClass r) ^ 2) *
        deriv (h3TerminalPhysicalTopDissipation3Path hClass) r) := by
  have hDerivative :
      deriv (h3TerminalPhysicalTopDissipation3Path hClass) r =
        h3PathTopFourierFourthRadialPairingRate244 hH3 hClass r :=
    (h3TerminalPhysicalTopDissipation3Path_hasDerivAt hH3 hClass hr).deriv
  have hBalance :=
    h3Path_globalFourthRadialPairing_add_fifth_add_phase_eq_cubic244
      hH3 hClass hr
  have hSigned :
      h3PathTopFourierGlobalFifthMass244 hH3 hClass r hr +
          h3PathTopFourierGlobalSignedPhaseDefect244 hH3 hClass r hr -
          h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
            hH3 hClass hr =
        -(deriv (h3TerminalPhysicalTopDissipation3Path hClass) r) := by
    rw [hDerivative]
    linarith only [hBalance]
  unfold h3PathTopFourierGlobalTopPhaseNormalizedRate244
  rw [hSigned]
  ring

/-- The positive part of the physical top concentration channel is
supported solely on intervals of decreasing D3; no monotonicity of D3 is
assumed. The actual spectral Cauchy inequality supplies the sharp weight. -/
theorem h3Path_globalTopPhase_le_negativeLogVariation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u r)
    (hD : 0 < velocityH3Dissipation3At u r) :
    h3PathTopFourierGlobalTopPhaseNormalizedRate244 hH3 hClass r hr ≤
      max (-(deriv (h3TerminalPhysicalTopDissipation3Path hClass) r)) 0 /
        h3TerminalPhysicalTopDissipation3Path hClass r := by
  have hTopValue := h3TerminalPhysicalTopDissipation3Path_eq hClass hr
  have hTopPos : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    rw [hTopValue]
    exact hD
  have hMoment :=
    (h3Path_topFourier_normalizedMoment_strictRange244
      hH3 hClass hr hMass hD).2.2
  have hCauchy : velocityH3Energy2At u r ^ 2 ≤
      velocityH3Energy0At u r *
        h3TerminalPhysicalTopDissipation3Path hClass r := by
    unfold h3PathTopFourierNormalizedMiddleMoment244 at hMoment
    have hBound := le_of_lt hMoment
    have hDenOld : 0 < velocityH3Energy0At u r *
        velocityH3Dissipation3At u r := mul_pos hMass hD
    have hBound' := (div_le_iff₀ hDenOld).mp hBound
    rw [hTopValue]
    simpa only [one_mul] using hBound'
  obtain ⟨hWeightNonneg, hWeightCeiling⟩ :=
    h3_scalar_topPhaseWeight_nonneg_mulTop_le_one244
      (velocityH3Energy0At u r) (velocityH3Energy2At u r)
      (h3TerminalPhysicalTopDissipation3Path hClass r)
      hMass hTopPos hCauchy
  rw [h3Path_globalTopPhase_eq_weighted_negativeTopDerivative244
    hH3 hClass hr]
  exact h3_scalar_weightedTop_le_negativeLogVariation244
    _ _ _ hWeightNonneg hTopPos hWeightCeiling

/-- Strictly positive signed top-phase concentration production requires a
strict DECREASE of the genuine physical top-dissipation mass. -/
theorem h3Path_positiveTopPhase_forces_topDissipation_decrease244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T)
    (hMass : 0 < velocityH3Energy0At u r)
    (hD : 0 < velocityH3Dissipation3At u r)
    (hPositive : 0 < h3PathTopFourierGlobalTopPhaseNormalizedRate244
      hH3 hClass r hr) :
    deriv (h3TerminalPhysicalTopDissipation3Path hClass) r < 0 := by
  have hBound := h3Path_globalTopPhase_le_negativeLogVariation244
    hH3 hClass hr hMass hD
  have hTopPos : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hr]
    exact hD
  by_contra hNot
  have hd : 0 ≤ deriv (h3TerminalPhysicalTopDissipation3Path hClass) r :=
    le_of_not_gt hNot
  have hMax : max (-(deriv (h3TerminalPhysicalTopDissipation3Path hClass) r)) 0 = 0 :=
    max_eq_right (neg_nonpos.mpr hd)
  rw [hMax] at hBound
  simp only [zero_div] at hBound
  exact (not_lt_of_ge hBound) hPositive

/-- The downward logarithmic variation of the actual fourth-radial mass,
using zero extension outside the strict physical energy-class interval. -/
noncomputable def h3PathPhysicalTopNegativeLogVariationRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (hClass : PreterminalH3EnergyClass u a T)
    (r : ℝ) : ℝ :=
  if hr : r ∈ Set.Ioo a T then
    max (-(deriv (h3TerminalPhysicalTopDissipation3Path hClass) r)) 0 /
      h3TerminalPhysicalTopDissipation3Path hClass r
  else 0

/-- Signed nonlinear fifth-phase action cannot exceed the integrated
DOWNWARD logarithmic variation of D3 on any compact strict-time interval.
Only time-integrability of the two displayed sources is assumed. -/
theorem h3Path_integratedTopPhase_le_negativeLogVariation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hTopIntegrable : IntervalIntegrable
      (h3PathPhysicalIntegratedTopPhaseProfile244 hH3 hClass) volume s t)
    (hVariationIntegrable : IntervalIntegrable
      (h3PathPhysicalTopNegativeLogVariationRate244 hClass) volume s t) :
    (∫ r in s..t, h3PathPhysicalIntegratedTopPhaseProfile244 hH3 hClass r) ≤
      ∫ r in s..t, h3PathPhysicalTopNegativeLogVariationRate244 hClass r := by
  apply intervalIntegral.integral_mono_on hst hTopIntegrable hVariationIntegrable
  intro r hr
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hAt := h3Path_globalTopPhase_le_negativeLogVariation244
    hH3 hClass hrClass (hMass r hr) (hD r hr)
  simpa only [h3PathPhysicalIntegratedTopPhaseProfile244,
    h3PathPhysicalTopNegativeLogVariationRate244, dif_pos hrClass] using hAt

/-- The quantitative near-Young obstruction now becomes a lower bound on
actual DOWNWARD log variation of physical top dissipation. No monotonicity
assumption, no arbitrary heat ceiling, and no arbitrary middle-source
budget enters; compact source integrability remains explicit. -/
theorem h3Path_nearYoung_forces_downwardTopLogVariation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t K δ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s < t)
    (hMass : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Energy0At u r)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDerivativeIntegrable : IntervalIntegrable
      (deriv (h3PathTopFourierNormalizedVarianceOnClass244 hClass)) volume s t)
    (hMiddleIntegrable : IntervalIntegrable
      (h3PathTopFourierGlobalMiddleCouplingNormalizedRate244 hClass) volume s t)
    (hTopIntegrable : IntervalIntegrable
      (h3PathPhysicalIntegratedTopPhaseProfile244 hH3 hClass) volume s t)
    (hLossIntegrable : IntervalIntegrable
      (h3PathPhysicalKineticLogLossRate244 u) volume s t)
    (hVariationIntegrable : IntervalIntegrable
      (h3PathPhysicalTopNegativeLogVariationRate244 hClass) volume s t)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    h3PathTopFourierNormalizedRadialVariance244 u s -
      (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t) -
      (Real.log (velocityH3Energy0At u s) -
        Real.log (velocityH3Energy0At u t)) -
      36 * (∫ r in s..t,
        h3PathCanonicalSqrtEnergyGradientEnvelope u r) ≤
      ∫ r in s..t, h3PathPhysicalTopNegativeLogVariationRate244 hClass r := by
  have hNeeded := h3Path_nearYoung_forces_integratedTopPhase_after_kineticLog244
    hH3 hClass hs ht hst hMass hD hDerivativeIntegrable
    hMiddleIntegrable hTopIntegrable hLossIntegrable hK hNear
  have hCeiling := h3Path_integratedTopPhase_le_negativeLogVariation244
    hH3 hClass hs ht hst.le hMass hD hTopIntegrable hVariationIntegrable
  exact hNeeded.trans hCeiling

end
end PrimeTensor.FirstMonomialTriad
