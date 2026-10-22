import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopCubicExactAction244
import Mathlib.Tactic

/-!
# Automatic compact-time integrability of the joint physical fifth/phase expenditure

The actual physical fourth-radial PDE balance gives

  M3 / D3 = (log D3)' + M5 / D3 + P / D3.

The preceding file proved that M3/D3 is interval-integrable automatically on
compact strict intervals with D3 > 0. The signed logarithmic rate is retained
as an explicit integrability hypothesis. Their difference is therefore
interval-integrable and agrees with the *actual sum* M5/D3 + P/D3.

This removes the two separate fifth and phase temporal-integrability
hypotheses from the exact joint expenditure identity and the near-Young
necessary condition. It does NOT prove terminal-uniform integrability or
separate individual integrability of fifth and phase profiles.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- At each strict physical time, the genuine combined fifth/phase cost is
exactly cubic forcing minus signed top-logarithmic production. -/
theorem h3Path_topFifthPhaseJoint_eq_cubic_sub_signedLog244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T) :
    h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
      h3PathPhysicalTopPhaseActionRate244 hH3 hClass r =
    h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r -
      h3PathPhysicalTopSignedLogRate244 hClass r := by
  have hBalance :=
    h3Path_topCubic_eq_signedLog_add_fifth_add_phase244 hH3 hClass hr
  linarith only [hBalance]

/-- The physical fifth/phase cost is jointly nonnegative. This assertion
is pointwise and does not depend on any temporal regularity assumptions. -/
theorem h3Path_topFifthPhaseJoint_nonneg244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T)
    (hD : 0 < velocityH3Dissipation3At u r) :
    0 ≤ h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
      h3PathPhysicalTopPhaseActionRate244 hH3 hClass r := by
  exact add_nonneg
    (h3Path_topFifthAction_nonneg244 hH3 hClass hr hD)
    (h3Path_topPhaseAction_nonneg244 hH3 hClass hr hD)

/-- Both expenditure channels *together* are automatically interval-
integrable once the signed log rate is integrable. No separate fifth-moment
or phase temporal-integrability hypotheses are needed. -/
theorem h3Path_topFifthPhaseJoint_intervalIntegrable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hLogIntegrable : IntervalIntegrable
      (h3PathPhysicalTopSignedLogRate244 hClass) volume s t) :
    IntervalIntegrable
      (fun r : ℝ =>
        h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
        h3PathPhysicalTopPhaseActionRate244 hH3 hClass r)
      volume s t := by
  have hDifferenceIntegrable : IntervalIntegrable
      (fun r : ℝ =>
        h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r -
        h3PathPhysicalTopSignedLogRate244 hClass r) volume s t :=
    (h3Path_topCubic_intervalIntegrable244 hH3 hClass hs ht hst hD).sub
      hLogIntegrable
  have hEqual : Set.EqOn
      (fun r : ℝ =>
        h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r -
        h3PathPhysicalTopSignedLogRate244 hClass r)
      (fun r : ℝ =>
        h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
        h3PathPhysicalTopPhaseActionRate244 hH3 hClass r)
      (Set.uIoc s t) := by
    intro r hr
    rw [Set.uIoc_of_le hst] at hr
    have hrClass : r ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le hs.1 hr.1.le, lt_of_le_of_lt hr.2 ht.2⟩
    exact (h3Path_topFifthPhaseJoint_eq_cubic_sub_signedLog244
      hH3 hClass hrClass).symm
  exact hDifferenceIntegrable.congr hEqual

/-- Exact combined physical fifth/phase budget, now requiring only signed-
logarithmic temporal integrability. The normalized cubic rate and joint
expenditure are both integrable on every compact strict interval. -/
theorem h3Path_topFifthPhaseJointAction_eq_cubic_sub_endpointLog244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hLogIntegrable : IntervalIntegrable
      (h3PathPhysicalTopSignedLogRate244 hClass) volume s t) :
    (∫ r in s..t,
      h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
        h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) =
      (∫ r in s..t,
        h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r) -
        (Real.log (h3TerminalPhysicalTopDissipation3Path hClass t) -
          Real.log (h3TerminalPhysicalTopDissipation3Path hClass s)) := by
  have hCubicIntegrable :=
    h3Path_topCubic_intervalIntegrable244 hH3 hClass hs ht hst hD
  have hSameIntegral :
      (∫ r in s..t,
        h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
          h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) =
        ∫ r in s..t,
          h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r -
            h3PathPhysicalTopSignedLogRate244 hClass r := by
    apply intervalIntegral.integral_congr_Ioo_of_le hst
    intro r hr
    have hrClass : r ∈ Set.Ioo a T :=
      ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
    exact h3Path_topFifthPhaseJoint_eq_cubic_sub_signedLog244
      hH3 hClass hrClass
  rw [hSameIntegral,
    intervalIntegral.integral_sub hCubicIntegrable hLogIntegrable,
    h3Path_topSignedLog_integral_eq_endpoint244
      hH3 hClass hs ht hst hD hLogIntegrable]

/-- The near-Young necessary cost can be expressed as a SINGLE jointly
integrable physical fifth-plus-phase expenditure, without assuming the
individual expenditure rates are time-integrable. -/
theorem h3Path_nearYoung_forces_jointFifthPhaseAction244
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
    (hDownIntegrable : IntervalIntegrable
      (h3PathPhysicalTopNegativeLogVariationRate244 hClass) volume s t)
    (hUpIntegrable : IntervalIntegrable
      (h3PathPhysicalTopPositiveLogVariationRate244 hClass) volume s t)
    (hLogIntegrable : IntervalIntegrable
      (h3PathPhysicalTopSignedLogRate244 hClass) volume s t)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    h3PathTopFourierNormalizedRadialVariance244 u s -
      (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t) -
      (Real.log (velocityH3Energy0At u s) -
        Real.log (velocityH3Energy0At u t)) -
      36 * (∫ r in s..t, h3PathCanonicalSqrtEnergyGradientEnvelope u r) ≤
      ∫ r in s..t,
        h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
          h3PathPhysicalTopPhaseActionRate244 hH3 hClass r := by
  have hCubicIntegrable :=
    h3Path_topCubic_intervalIntegrable244 hH3 hClass hs ht hst.le hD
  have hRequired := h3Path_nearYoung_forces_cubicReplenishmentAction244
    hH3 hClass hs ht hst hMass hD
    hDerivativeIntegrable hMiddleIntegrable hTopIntegrable hLossIntegrable
    hDownIntegrable hUpIntegrable hLogIntegrable hCubicIntegrable hK hNear
  have hExact := h3Path_topFifthPhaseJointAction_eq_cubic_sub_endpointLog244
    hH3 hClass hs ht hst.le hD hLogIntegrable
  rw [hExact]
  linarith only [hRequired]

end
end PrimeTensor.FirstMonomialTriad
