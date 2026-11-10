import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalDyadicAdaptiveHighpassGate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopAutomaticLogClock244
import Mathlib.Tactic

/-!
# Critical dyadic net-growth peaks and exact physical fifth/phase source expenditure

The previous all-cutoff theorem found a genuine physical time where the
*gross* cubic Leray source exceeded a threshold, but did not charge the
fifth-order viscous and positive Fourier-phase expenditure at that same time.

The terminal cubic rate and a near-critical earlier anchor also imply an
increase of the actual logarithm of top-third dissipation by more than
`K*(t-s)`. The physical logarithmic derivative exists at each strict time.
The ordinary mean-value estimate therefore forces an attained point at which
that *signed* rate exceeds K. At precisely this point, the established exact
Navier--Stokes balance gives

  M3/D3 = (log D3)' + M5/D3 + phase/D3.

The actual kinetic lowpass / highpass theorem can now be applied at every
Fourier cutoff *after* the net-growth witness has been selected. Thus the
physical highpass source must pay not merely K*D3, but the additional genuine
fifth-order and phase loss. This adds no raw order-eight velocity moments,
no higher-derivative hypotheses, and no claim of a highpass upper bound.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- A near-critical dyadic anchor forces a STRICT-time peak of the *net*
physical log growth. Unlike a gross cubic source peak, this already accounts
for both the viscous fifth-order and nonnegative phase expenditures. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_netSignedLogPeak244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDouble : T - s = 2 * (T - t))
    (B : ℝ) (hB : 0 < B)
    (hRate : 1 ≤ B * (T - t) ^ 8 *
      (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3)
    (K : ℝ)
    (hNear : Real.log B + 8 * Real.log (T - s) +
        3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) <
        8 * Real.log 2 - 3 * K * (t - s)) :
    ∃ r : ℝ, r ∈ Set.Ioo s t ∧
      K < h3PathPhysicalTopSignedLogRate244 hClass r := by
  have hCharge :=
    thirdFullPhysical_criticalCubicRate_forces_dyadicSourceCharge244
      hH3 hClass hs ht hst hD hDouble B hB hRate
  have hExact :=
    h3Path_topJointAction_eq_cubic_sub_log_automatic244
      hH3 hClass hs ht hst hD
  have hGrowth :
      K * (t - s) <
        Real.log (h3TerminalPhysicalTopDissipation3Path hClass t) -
          Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) := by
    linarith only [hCharge, hExact, hNear]
  let F : ℝ → ℝ :=
    fun r => Real.log (h3TerminalPhysicalTopDissipation3Path hClass r)
  have hInside (r : ℝ) (hr : r ∈ Set.Icc s t) : r ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hDerivative (r : ℝ) (hr : r ∈ Set.Icc s t) :
      HasDerivAt F (h3PathPhysicalTopSignedLogRate244 hClass r) r :=
    h3Path_topLog_hasDerivAt244
      hH3 hClass (hInside r hr) (hD r hr)
  have hContinuous : ContinuousOn F (Set.Icc s t) := by
    intro r hr
    exact (hDerivative r hr).continuousAt.continuousWithinAt
  have hDiff : DifferentiableOn ℝ F (interior (Set.Icc s t)) := by
    intro r hr
    exact (hDerivative r (interior_subset hr)).differentiableAt.differentiableWithinAt
  by_contra hNo
  have hBound : ∀ r ∈ interior (Set.Icc s t), deriv F r ≤ K := by
    intro r hr
    have hrc : r ∈ Set.Icc s t := interior_subset hr
    rw [(hDerivative r hrc).deriv]
    have hri : r ∈ Set.Ioo s t := by
      simpa only [interior_Icc] using hr
    exact le_of_not_gt (by
      intro hHigh
      exact hNo ⟨r, hri, hHigh⟩)
  have hUpper := h3_scalar_oneSidedDerivativeCeiling244
    F s t K hst hContinuous hDiff hBound
  exact (not_lt_of_ge hUpper) hGrowth

/-- An H3-native PDE upper inequality: the actual logarithmic production,
plus the TRUE normalized fifth-order viscous and phase expenditure, is paid
by the kinetically bounded lowpass and the exact third-radial highpass.
No order-eight Fourier moment assumption occurs. -/
theorem thirdFullPhysical_signedLogPlusFifthPhase_le_kineticLowHigh244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (r : ℝ) (hr : r ∈ Set.Ioo b T)
    (hD : 0 < velocityH3Dissipation3At u r)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (h3PathPhysicalTopSignedLogRate244 hClass r +
        h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
        h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
      h3TerminalPhysicalTopDissipation3Path hClass r ≤
      2 * (2 * Real.pi) ^ 6 *
        (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
          ρ (velocityH3Energy0At u b) +
         ∑ j : Fin 3,
           (‖thirdFullPhysicalCriticalThirdForcingHighpass244
             hH3 hClass ρ j r‖ : ℝ) ^ 2) := by
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hr.1, hr.2⟩
  have hDr : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hrClass]
    exact hD
  have hBalance :=
    h3Path_topCubic_eq_signedLog_add_fifth_add_phase244
      hH3 hClass hrClass
  have hCubic :=
    h3Path_topCubic_eq_thirdRadialLerayNormSquares244
      hH3 hClass hrClass
  rw [hBalance] at hCubic
  have hIdentity :
      (h3PathPhysicalTopSignedLogRate244 hClass r +
          h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
          h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
        h3TerminalPhysicalTopDissipation3Path hClass r =
        (2 * Real.pi) ^ 6 *
          (∑ j : Fin 3,
            (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
              hH3 hClass j r‖ : ℝ) ^ 2) :=
    (eq_div_iff hDr.ne').mp hCubic
  calc
    _ = (2 * Real.pi) ^ 6 *
        (∑ j : Fin 3,
          (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
            hH3 hClass j r‖ : ℝ) ^ 2) := hIdentity
    _ ≤ 2 * (2 * Real.pi) ^ 6 *
        (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
          ρ (velocityH3Energy0At u b) +
         ∑ j : Fin 3,
           (‖thirdFullPhysicalCriticalThirdForcingHighpass244
             hH3 hClass ρ j r‖ : ℝ) ^ 2) :=
      thirdFullPhysical_criticalThirdForcingMass_kineticLowHigh244
        hH3 hClass b hb ρ hρ r hr

/-- One real net-growth witness works at EVERY subsequent Fourier cutoff.
Its physical third-radial source must pay K D3 PLUS both genuine fifth
viscous and phase losses at that same time, in the exact low/high budget. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_adaptiveJointHighpassCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hs : s ∈ Set.Ioo b T) (ht : t ∈ Set.Ioo b T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDouble : T - s = 2 * (T - t))
    (B : ℝ) (hB : 0 < B)
    (hRate : 1 ≤ B * (T - t) ^ 8 *
      (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3)
    (K : ℝ)
    (hNear : Real.log B + 8 * Real.log (T - s) +
        3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) <
        8 * Real.log 2 - 3 * K * (t - s)) :
    ∃ r : ℝ, r ∈ Set.Ioo s t ∧
      K < h3PathPhysicalTopSignedLogRate244 hClass r ∧
      ∀ ρ : ℝ, 0 ≤ ρ →
        (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
            h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
          h3TerminalPhysicalTopDissipation3Path hClass r <
          2 * (2 * Real.pi) ^ 6 *
            (3 * thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
              ρ (velocityH3Energy0At u b) +
             ∑ j : Fin 3,
               (‖thirdFullPhysicalCriticalThirdForcingHighpass244
                 hH3 hClass ρ j r‖ : ℝ) ^ 2) := by
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hs.1, hs.2⟩
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  obtain ⟨r, hr, hNet⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_netSignedLogPeak244
      hH3 hClass hsClass htClass hst hD hDouble B hB hRate K hNear
  refine ⟨r, hr, hNet, ?_⟩
  have hrTail : r ∈ Set.Ioo b T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  have hDr : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    have hrClass : r ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 hrTail.1, hrTail.2⟩
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hrClass]
    exact hD r ⟨hr.1.le, hr.2.le⟩
  intro ρ hρ
  have hRatePlus :
      K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
          h3PathPhysicalTopPhaseActionRate244 hH3 hClass r <
        h3PathPhysicalTopSignedLogRate244 hClass r +
          h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
          h3PathPhysicalTopPhaseActionRate244 hH3 hClass r := by
    linarith only [hNet]
  exact lt_of_lt_of_le
    (mul_lt_mul_of_pos_right hRatePlus hDr)
    (thirdFullPhysical_signedLogPlusFifthPhase_le_kineticLowHigh244
      hH3 hClass b hb r hrTail (hD r ⟨hr.1.le, hr.2.le⟩) ρ hρ)

/-- If an adaptive kinetic lowpass cannot pay even half the true combined
net-growth+fifth+phase charge at the single selected physical peak, the
actual third-radial highpass must pay at least the remaining quarter scale.
The low-budget premise is explicit; it is NOT deduced from H3 alone. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_viscousPhaseHighpassDefect244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hs : s ∈ Set.Ioo b T) (ht : t ∈ Set.Ioo b T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hDouble : T - s = 2 * (T - t))
    (B : ℝ) (hB : 0 < B)
    (hRate : 1 ≤ B * (T - t) ^ 8 *
      (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3)
    (K : ℝ)
    (hNear : Real.log B + 8 * Real.log (T - s) +
        3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) <
        8 * Real.log 2 - 3 * K * (t - s)) :
    ∃ r : ℝ, r ∈ Set.Ioo s t ∧
      ∀ ρ : ℝ, 0 ≤ ρ →
        (6 * (2 * Real.pi) ^ 6 *
          thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
            ρ (velocityH3Energy0At u b) ≤
          ((K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
              h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
            h3TerminalPhysicalTopDissipation3Path hClass r) / 2) →
        (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
            h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
          h3TerminalPhysicalTopDissipation3Path hClass r <
          4 * (2 * Real.pi) ^ 6 *
            ∑ j : Fin 3,
              (‖thirdFullPhysicalCriticalThirdForcingHighpass244
                hH3 hClass ρ j r‖ : ℝ) ^ 2 := by
  obtain ⟨r, hr, _, hAll⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_adaptiveJointHighpassCharge244
      hH3 hClass b hb hs ht hst hD hDouble B hB hRate K hNear
  refine ⟨r, hr, ?_⟩
  intro ρ hρ hLow
  let A : ℝ :=
    (K + h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
        h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) *
      h3TerminalPhysicalTopDissipation3Path hClass r
  let C : ℝ := (2 * Real.pi) ^ 6
  let L : ℝ := thirdFullPhysicalCriticalThirdForcingKineticLowBudget244
    ρ (velocityH3Energy0At u b)
  let H : ℝ := ∑ j : Fin 3,
    (‖thirdFullPhysicalCriticalThirdForcingHighpass244
      hH3 hClass ρ j r‖ : ℝ) ^ 2
  have hCharge : A < 2 * C * (3 * L + H) := by
    simpa only [A, C, L, H] using hAll ρ hρ
  have hLow' : 6 * C * L ≤ A / 2 := by
    simpa only [A, C, L] using hLow
  change A < 4 * C * H
  nlinarith only [hCharge, hLow']

end
end PrimeTensor.FirstMonomialTriad
