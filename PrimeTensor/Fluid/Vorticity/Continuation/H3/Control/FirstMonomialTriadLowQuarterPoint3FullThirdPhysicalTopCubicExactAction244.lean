import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopCubicReplenishment244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Local
import Mathlib.Tactic

/-!
# Exact physical cubic forcing action, normalized fifth dissipation and phase

The physical fourth-radial PDE balance is

    D3' + M5 + P = M3,      M5 >= 0, P >= 0.

Divide by positive D3 and integrate over a compact strict time interval:

    integral (M3/D3) = log(D3(t)) - log(D3(s))
                        + integral (M5/D3) + integral (P/D3).

This identity exposes a precise cost of nonlinear replenishment: forcing must
pay both the fifth radial velocity mass and the nonnegative signed Fourier
phase defect. The earlier near-Young lower bound on the cubic forcing action
then cancels its endpoint D3 logarithm, giving a necessary LOWER bound on
integrated normalized fifth-plus-phase expenditure. It is not a uniform
terminal estimate and does not claim unconditional Navier--Stokes regularity.

All temporal interval-integrability assumptions remain explicit.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- Normalized fifth-radial velocity dissipation on a strict physical H3 class. -/
noncomputable def h3PathPhysicalTopFifthActionRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (r : ℝ) : ℝ :=
  if hr : r ∈ Set.Ioo a T then
    h3PathTopFourierGlobalFifthMass244 hH3 hClass r hr /
      h3TerminalPhysicalTopDissipation3Path hClass r
  else 0

/-- Normalized nonnegative Fourier phase mismatch on a strict physical H3 class. -/
noncomputable def h3PathPhysicalTopPhaseActionRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (r : ℝ) : ℝ :=
  if hr : r ∈ Set.Ioo a T then
    h3PathTopFourierGlobalSignedPhaseDefect244 hH3 hClass r hr /
      h3TerminalPhysicalTopDissipation3Path hClass r
  else 0

/-- The normalized cubic action is the genuine physical third-radial
Leray forcing L2 norm-square mass, not an artificial scalar rate. -/
theorem h3Path_topCubic_eq_thirdRadialLerayNormSquares244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T) :
    h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r =
      ((2 * Real.pi) ^ 6 *
        ∑ j : Fin 3,
          (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
            hH3 hClass j r‖ : ℝ) ^ 2) /
        h3TerminalPhysicalTopDissipation3Path hClass r := by
  have hNorm :=
    h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq_sum_norm_sq_thirdRadialPath
      hH3 hClass hr
  rw [h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq
    hH3 hClass hr] at hNorm
  unfold h3PathPhysicalTopCubicReplenishmentRate244
  simpa only [dif_pos hr] using congrArg
    (fun z : ℝ => z / h3TerminalPhysicalTopDissipation3Path hClass r) hNorm

/-- The complete cubic source, *without absolute values*, consists exactly
of top logarithmic growth, viscous fifth expenditure, and phase expenditure. -/
theorem h3Path_topCubic_eq_signedLog_add_fifth_add_phase244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T) :
    h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r =
      h3PathPhysicalTopSignedLogRate244 hClass r +
      h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
      h3PathPhysicalTopPhaseActionRate244 hH3 hClass r := by
  have hBalance := h3Path_topDerivative_add_fifth_add_phase_eq_cubic244
    hH3 hClass hr
  unfold h3PathPhysicalTopCubicReplenishmentRate244
    h3PathPhysicalTopSignedLogRate244
    h3PathPhysicalTopFifthActionRate244
    h3PathPhysicalTopPhaseActionRate244
  simp only [dif_pos hr]
  rw [← hBalance]
  ring

/-- The normalized fifth velocity expenditure is nonnegative at all
strict physical times of positive top dissipation. -/
theorem h3Path_topFifthAction_nonneg244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T)
    (hD : 0 < velocityH3Dissipation3At u r) :
    0 ≤ h3PathPhysicalTopFifthActionRate244 hH3 hClass r := by
  have hTop : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hr]
    exact hD
  unfold h3PathPhysicalTopFifthActionRate244
  simp only [dif_pos hr]
  exact div_nonneg (h3Path_globalFifthMass_nonneg_for_replenishment244
    hH3 hClass hr) hTop.le

/-- The normalized signed phase-mismatch expenditure is nonnegative at
all strict physical times of positive top dissipation. -/
theorem h3Path_topPhaseAction_nonneg244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T)
    (hD : 0 < velocityH3Dissipation3At u r) :
    0 ≤ h3PathPhysicalTopPhaseActionRate244 hH3 hClass r := by
  have hTop : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hr]
    exact hD
  unfold h3PathPhysicalTopPhaseActionRate244
  simp only [dif_pos hr]
  exact div_nonneg (h3Path_globalSignedPhaseDefect_nonneg244
    hH3 hClass hr) hTop.le

/-- An immediate physical inequality: cubic forcing must fund the signed
logarithmic top growth plus the entire normalized fifth and phase expenditure. -/
theorem h3Path_topCubic_ge_signedLog_add_phase244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T)
    (hD : 0 < velocityH3Dissipation3At u r) :
    h3PathPhysicalTopSignedLogRate244 hClass r +
        h3PathPhysicalTopPhaseActionRate244 hH3 hClass r ≤
      h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r := by
  rw [h3Path_topCubic_eq_signedLog_add_fifth_add_phase244 hH3 hClass hr]
  have hFifth := h3Path_topFifthAction_nonneg244 hH3 hClass hr hD
  linarith only [hFifth]

/-- The genuine cubic forcing-to-top-mass ratio is automatically
interval-integrable on compact strict intervals with positive D3. This uses
the PREVIOUSLY PROVED continuity of the physical third-radial forcing mass,
not any terminal a priori estimate or auxiliary temporal majorant. -/
theorem h3Path_topCubic_intervalIntegrable244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r) :
    IntervalIntegrable
      (h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass) volume s t := by
  have hInside : Set.Icc s t ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hForcingCont : ContinuousOn
      (h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile hH3 hClass)
      (Set.Icc s t) :=
    (h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_continuousOn
      hH3 hClass).mono hInside
  have hTopCont : ContinuousOn
      (h3TerminalPhysicalTopDissipation3Path hClass) (Set.Icc s t) := by
    intro r hr
    exact (h3TerminalPhysicalTopDissipation3Path_hasDerivAt
      hH3 hClass (hInside hr)).continuousAt.continuousWithinAt
  have hRatioCont : ContinuousOn (fun r : ℝ =>
      h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
        hH3 hClass r / h3TerminalPhysicalTopDissipation3Path hClass r)
      (Set.Icc s t) := by
    apply hForcingCont.div hTopCont
    intro r hr
    have hrClass := hInside hr
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hrClass]
    exact ne_of_gt (hD r hr)
  have hSame : Set.EqOn (fun r : ℝ =>
      h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile
        hH3 hClass r / h3TerminalPhysicalTopDissipation3Path hClass r)
      (h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass)
      (Set.Icc s t) := by
    intro r hr
    have hrClass := hInside hr
    change
      h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile hH3 hClass r /
        h3TerminalPhysicalTopDissipation3Path hClass r =
      h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r
    rw [h3TerminalPhysicalTopDissipationFullForcingCubicMassProfile_eq
      hH3 hClass hrClass]
    simp only [h3PathPhysicalTopCubicReplenishmentRate244, dif_pos hrClass]
  exact (hRatioCont.congr hSame.symm).intervalIntegrable_of_Icc hst

/-- Exact compact-time balance of normalized cubic forcing and the physical
fifth/phase dissipative expenditures. The sign of the phase is preserved.
Integrability of the individual real-time profiles is NOT automatic here. -/
theorem h3Path_topCubicAction_eq_endpointLog_add_fifth_phase244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hLogIntegrable : IntervalIntegrable
      (h3PathPhysicalTopSignedLogRate244 hClass) volume s t)
    (hFifthIntegrable : IntervalIntegrable
      (h3PathPhysicalTopFifthActionRate244 hH3 hClass) volume s t)
    (hPhaseIntegrable : IntervalIntegrable
      (h3PathPhysicalTopPhaseActionRate244 hH3 hClass) volume s t) :
    (∫ r in s..t, h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r) =
      (Real.log (h3TerminalPhysicalTopDissipation3Path hClass t) -
        Real.log (h3TerminalPhysicalTopDissipation3Path hClass s)) +
      (∫ r in s..t, h3PathPhysicalTopFifthActionRate244 hH3 hClass r) +
      (∫ r in s..t, h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) := by
  have hPointIntegral :
      (∫ r in s..t, h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r) =
        ∫ r in s..t,
          (h3PathPhysicalTopSignedLogRate244 hClass r +
            h3PathPhysicalTopFifthActionRate244 hH3 hClass r) +
            h3PathPhysicalTopPhaseActionRate244 hH3 hClass r := by
    apply intervalIntegral.integral_congr_Ioo_of_le hst
    intro r hr
    have hrClass : r ∈ Set.Ioo a T :=
      ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
    exact h3Path_topCubic_eq_signedLog_add_fifth_add_phase244
      hH3 hClass hrClass
  have hSplit :
      (∫ r in s..t, h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r) =
        (∫ r in s..t, h3PathPhysicalTopSignedLogRate244 hClass r) +
        (∫ r in s..t, h3PathPhysicalTopFifthActionRate244 hH3 hClass r) +
        (∫ r in s..t, h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) := by
    rw [hPointIntegral,
      intervalIntegral.integral_add (hLogIntegrable.add hFifthIntegrable)
        hPhaseIntegrable,
      intervalIntegral.integral_add hLogIntegrable hFifthIntegrable]
  have hLog := h3Path_topSignedLog_integral_eq_endpoint244
    hH3 hClass hs ht hst hD hLogIntegrable
  rw [hLog] at hSplit
  exact hSplit

/-- On any interval with no NET loss of physical top dissipation,
the normalized cubic forcing action pays for all fifth and phase losses.
Unlike the pointwise statement, top dissipation may decrease temporarily. -/
theorem h3Path_topCubicAction_ge_fifth_phase_of_netTopGrowth244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hNetGrowth : h3TerminalPhysicalTopDissipation3Path hClass s ≤
      h3TerminalPhysicalTopDissipation3Path hClass t)
    (hLogIntegrable : IntervalIntegrable
      (h3PathPhysicalTopSignedLogRate244 hClass) volume s t)
    (hFifthIntegrable : IntervalIntegrable
      (h3PathPhysicalTopFifthActionRate244 hH3 hClass) volume s t)
    (hPhaseIntegrable : IntervalIntegrable
      (h3PathPhysicalTopPhaseActionRate244 hH3 hClass) volume s t) :
    (∫ r in s..t, h3PathPhysicalTopFifthActionRate244 hH3 hClass r) +
      (∫ r in s..t, h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) ≤
      ∫ r in s..t,
        h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r := by
  have hExact := h3Path_topCubicAction_eq_endpointLog_add_fifth_phase244
    hH3 hClass hs ht hst hD
    hLogIntegrable hFifthIntegrable hPhaseIntegrable
  have hDs : 0 < h3TerminalPhysicalTopDissipation3Path hClass s := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hs]
    exact hD s ⟨le_refl s, hst⟩
  have hLogLe := Real.log_le_log hDs hNetGrowth
  rw [hExact]
  linarith only [hLogLe]

/-- Near-Young saturation forces fifth velocity and phase expenditures
*even after* net top logarithmic growth is canceled from the physical cubic
source. This is a necessary dissipative action inequality, not an upper
bound on these expenditures. -/
theorem h3Path_nearYoung_forces_fifth_phase_action244
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
    (hFifthIntegrable : IntervalIntegrable
      (h3PathPhysicalTopFifthActionRate244 hH3 hClass) volume s t)
    (hPhaseIntegrable : IntervalIntegrable
      (h3PathPhysicalTopPhaseActionRate244 hH3 hClass) volume s t)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    h3PathTopFourierNormalizedRadialVariance244 u s -
      (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t) -
      (Real.log (velocityH3Energy0At u s) -
        Real.log (velocityH3Energy0At u t)) -
      36 * (∫ r in s..t, h3PathCanonicalSqrtEnergyGradientEnvelope u r) ≤
      (∫ r in s..t, h3PathPhysicalTopFifthActionRate244 hH3 hClass r) +
      (∫ r in s..t, h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) := by
  have hCubicIntegrable := h3Path_topCubic_intervalIntegrable244
    hH3 hClass hs ht hst.le hD
  have hRequired := h3Path_nearYoung_forces_cubicReplenishmentAction244
    hH3 hClass hs ht hst hMass hD
    hDerivativeIntegrable hMiddleIntegrable hTopIntegrable hLossIntegrable
    hDownIntegrable hUpIntegrable hLogIntegrable hCubicIntegrable hK hNear
  have hExact := h3Path_topCubicAction_eq_endpointLog_add_fifth_phase244
    hH3 hClass hs ht hst.le hD
    hLogIntegrable hFifthIntegrable hPhaseIntegrable
  rw [hExact] at hRequired
  linarith only [hRequired]

end
end PrimeTensor.FirstMonomialTriad
