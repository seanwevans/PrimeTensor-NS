import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopLogReplenishment244
import Mathlib.Tactic

/-!
# Physical top logarithmic replenishment is paid by signed cubic forcing

The exact fourth-radial physical Hilbert energy law is

  D3'(t) + M5(t) + P(t) = M3(t),

where the unrestricted fifth velocity moment M5, the complete Fourier phase
square P and the cubic Leray-forcing mass M3 are all nonnegative. Therefore

  (D3')_+ / D3 = (M3-M5-P)_+ / D3 <= M3 / D3.

This equality retains both the viscous and signed-phase losses; the last
inequality bounds *positive replenishment* by actual cubic forcing. Combining
it with the previously established top-log variation obstruction forces an
integrated cubic forcing budget whenever a genuine physical near-Young gap
collapses. All temporal integrability hypotheses are explicit. Neither a
terminal-uniform cubic bound nor unconditional continuation is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- The actual fifth radial velocity square mass is nonnegative. Reuse the
previous global negative-heat sign and its exact fifth-moment identity. -/
theorem h3Path_globalFifthMass_nonneg_for_replenishment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T) :
    0 ≤ h3PathTopFourierGlobalFifthMass244 hH3 hClass r hr := by
  have hHeat := h3Path_globalHeatRate_nonpos244 hH3 r
    ⟨lt_trans hClass.terminal_start.1 hr.1, hr.2⟩
  rw [h3Path_globalHeatRate_eq_negTwoFifthMass244 hH3 hClass hr] at hHeat
  linarith only [hHeat]

/-- The true fourth-radial time derivative is exactly cubic forcing minus
fifth velocity dissipation minus the nonnegative phase mismatch. -/
theorem h3Path_topDerivative_add_fifth_add_phase_eq_cubic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T) :
    deriv (h3TerminalPhysicalTopDissipation3Path hClass) r +
      h3PathTopFourierGlobalFifthMass244 hH3 hClass r hr +
      h3PathTopFourierGlobalSignedPhaseDefect244 hH3 hClass r hr =
        h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
          hH3 hClass hr := by
  have hDerivative :=
    (h3TerminalPhysicalTopDissipation3Path_hasDerivAt hH3 hClass hr).deriv
  rw [hDerivative]
  exact h3Path_globalFourthRadialPairing_add_fifth_add_phase_eq_cubic244
    hH3 hClass hr

/-- Cubic forcing is the only positive source in the actual D3 derivative;
the fifth velocity mass and exact phase defect can only subtract from it. -/
theorem h3Path_topDerivative_le_cubic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T) :
    deriv (h3TerminalPhysicalTopDissipation3Path hClass) r ≤
      h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
        hH3 hClass hr := by
  have hExact := h3Path_topDerivative_add_fifth_add_phase_eq_cubic244
    hH3 hClass hr
  have hFifth := h3Path_globalFifthMass_nonneg_for_replenishment244
    hH3 hClass hr
  have hPhase := h3Path_globalSignedPhaseDefect_nonneg244 hH3 hClass hr
  linarith only [hExact, hFifth, hPhase]

/-- Strict positive top-mass growth has to overcome BOTH fifth velocity
mass and the complete signed Fourier phase defect. -/
theorem h3Path_positiveTopGrowth_forces_cubic_gt_fifth_add_phase244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T)
    (hGrowth : 0 < deriv (h3TerminalPhysicalTopDissipation3Path hClass) r) :
    h3PathTopFourierGlobalFifthMass244 hH3 hClass r hr +
      h3PathTopFourierGlobalSignedPhaseDefect244 hH3 hClass r hr <
        h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
          hH3 hClass hr := by
  have hExact := h3Path_topDerivative_add_fifth_add_phase_eq_cubic244
    hH3 hClass hr
  linarith only [hExact, hGrowth]

/-- The *exact* signed cubic surplus, retaining fifth velocity dissipation
and phase mismatch, normalized by current positive fourth-radial mass. -/
noncomputable def h3PathPhysicalTopNetCubicPhaseSurplusRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (r : ℝ) : ℝ :=
  if hr : r ∈ Set.Ioo a T then
    max (h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
      hH3 hClass hr -
      (h3PathTopFourierGlobalFifthMass244 hH3 hClass r hr +
       h3PathTopFourierGlobalSignedPhaseDefect244 hH3 hClass r hr)) 0 /
      h3TerminalPhysicalTopDissipation3Path hClass r
  else 0

/-- Nonnegative physical cubic forcing, divided by the actual top mass,
zero-extended outside the strict energy-class interval. -/
noncomputable def h3PathPhysicalTopCubicReplenishmentRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (r : ℝ) : ℝ :=
  if hr : r ∈ Set.Ioo a T then
    h3TerminalPhysicalTopDissipationFullForcingCubicMassAt hH3 hClass hr /
      h3TerminalPhysicalTopDissipation3Path hClass r
  else 0

/-- The positive D3 logarithmic replenishment is EXACTLY the nonnegative
surplus of cubic forcing above fifth velocity and signed phase losses. -/
theorem h3Path_topPositiveLog_eq_netCubicPhaseSurplus244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T) :
    h3PathPhysicalTopPositiveLogVariationRate244 hClass r =
      h3PathPhysicalTopNetCubicPhaseSurplusRate244 hH3 hClass r := by
  have hExact := h3Path_topDerivative_add_fifth_add_phase_eq_cubic244
    hH3 hClass hr
  have hRate :
      deriv (h3TerminalPhysicalTopDissipation3Path hClass) r =
        h3TerminalPhysicalTopDissipationFullForcingCubicMassAt hH3 hClass hr -
          (h3PathTopFourierGlobalFifthMass244 hH3 hClass r hr +
           h3PathTopFourierGlobalSignedPhaseDefect244 hH3 hClass r hr) := by
    linarith only [hExact]
  unfold h3PathPhysicalTopPositiveLogVariationRate244
    h3PathPhysicalTopNetCubicPhaseSurplusRate244
  simp only [dif_pos hr]
  rw [hRate]

/-- The cubic forcing ratio bounds replenishment with no discarded phase
in the preceding exact identity. Its numerator is a genuine nonnegative
Fourier squared-forcing mass, not an assumed PDE source ceiling. -/
theorem h3Path_topPositiveLog_le_cubicReplenishment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T)
    (hD : 0 < velocityH3Dissipation3At u r) :
    h3PathPhysicalTopPositiveLogVariationRate244 hClass r ≤
      h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r := by
  have hTop : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hr]
    exact hD
  have hDerivative := h3Path_topDerivative_le_cubic244 hH3 hClass hr
  have hCubic := h3TerminalPhysicalTopDissipationFullForcingCubicMassAt_nonneg
    hH3 hClass hr
  have hMax :
      max (deriv (h3TerminalPhysicalTopDissipation3Path hClass) r) 0 ≤
        h3TerminalPhysicalTopDissipationFullForcingCubicMassAt
          hH3 hClass hr :=
    max_le hDerivative hCubic
  have hQuotient := (div_le_div_iff_of_pos_right hTop).2 hMax
  unfold h3PathPhysicalTopPositiveLogVariationRate244
    h3PathPhysicalTopCubicReplenishmentRate244
  simpa only [dif_pos hr] using hQuotient

/-- In the absence of a positive cubic surplus over fifth mass and phase,
actual positive top logarithmic variation vanishes at that strict time. -/
theorem h3Path_topPositiveLog_eq_zero_of_cubic_le_fifth_add_phase244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T)
    (hDominated :
      h3TerminalPhysicalTopDissipationFullForcingCubicMassAt hH3 hClass hr ≤
        h3PathTopFourierGlobalFifthMass244 hH3 hClass r hr +
          h3PathTopFourierGlobalSignedPhaseDefect244 hH3 hClass r hr) :
    h3PathPhysicalTopPositiveLogVariationRate244 hClass r = 0 := by
  rw [h3Path_topPositiveLog_eq_netCubicPhaseSurplus244 hH3 hClass hr]
  unfold h3PathPhysicalTopNetCubicPhaseSurplusRate244
  simp only [dif_pos hr]
  have hDifference :
      h3TerminalPhysicalTopDissipationFullForcingCubicMassAt hH3 hClass hr -
        (h3PathTopFourierGlobalFifthMass244 hH3 hClass r hr +
          h3PathTopFourierGlobalSignedPhaseDefect244 hH3 hClass r hr) ≤ 0 :=
    sub_nonpos.mpr hDominated
  rw [max_eq_right hDifference]
  simp

/-- On a genuine compact physical time interval, the integral of positive
D3 logarithmic replenishment cannot exceed the normalized cubic forcing
action. Temporal integrability of both scalar rates is explicit. -/
theorem h3Path_integratedTopReplenishment_le_cubicAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hUpIntegrable : IntervalIntegrable
      (h3PathPhysicalTopPositiveLogVariationRate244 hClass) volume s t)
    (hCubicIntegrable : IntervalIntegrable
      (h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass) volume s t) :
    (∫ r in s..t, h3PathPhysicalTopPositiveLogVariationRate244 hClass r) ≤
      ∫ r in s..t,
        h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r := by
  apply intervalIntegral.integral_mono_on hst hUpIntegrable hCubicIntegrable
  intro r hr
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  exact h3Path_topPositiveLog_le_cubicReplenishment244
    hH3 hClass hrClass (hD r hr)

/-- A near-Young physical variance collapse forces a quantitative, time-
integrated REAL cubic Leray-forcing-to-D3 budget. The previous kinetic-loss,
compact gradient-action and net top-mass endpoint terms are retained. -/
theorem h3Path_nearYoung_forces_cubicReplenishmentAction244
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
    (hCubicIntegrable : IntervalIntegrable
      (h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass) volume s t)
    (hK : 0 < K)
    (hNear : velocityH3Dissipation3At u t +
      (27 / 256 : ℝ) * K ^ 4 * velocityH3Energy0At u t -
      K * velocityH3Energy3At u t ≤ δ) :
    h3PathTopFourierNormalizedRadialVariance244 u s -
      (256 * δ) / (27 * K ^ 4 * velocityH3Energy0At u t) -
      (Real.log (velocityH3Energy0At u s) -
        Real.log (velocityH3Energy0At u t)) -
      36 * (∫ r in s..t, h3PathCanonicalSqrtEnergyGradientEnvelope u r) -
      (Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) -
        Real.log (h3TerminalPhysicalTopDissipation3Path hClass t)) ≤
      ∫ r in s..t,
        h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r := by
  have hRequired := h3Path_nearYoung_forces_topLogReplenishment244
    hH3 hClass hs ht hst hMass hD
    hDerivativeIntegrable hMiddleIntegrable hTopIntegrable hLossIntegrable
    hDownIntegrable hUpIntegrable hLogIntegrable hK hNear
  have hBudget := h3Path_integratedTopReplenishment_le_cubicAction244
    hH3 hClass hs ht hst.le hD hUpIntegrable hCubicIntegrable
  exact hRequired.trans hBudget

end
end PrimeTensor.FirstMonomialTriad
