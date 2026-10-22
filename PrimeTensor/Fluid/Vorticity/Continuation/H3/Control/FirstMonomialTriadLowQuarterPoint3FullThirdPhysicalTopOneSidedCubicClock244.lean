import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopJointExpenditure244
import Mathlib.Tactic

/-!
# The one-sided physical top logarithmic clock

At every strict time where D3 > 0, the exact PDE balance gives

  (log D3)' = M3 / D3 - (M5 + P) / D3 <= M3 / D3.

A compact strict interval has a continuous physical cubic ratio M3 / D3.
The mean value theorem therefore bounds forward logarithmic growth of the
actual fourth-radial top mass by a *finite local cubic ceiling* even without
assuming time integrability of the signed log derivative, fifth moment,
or phase defect. The ceiling is not uniform as t approaches terminal time.

This is a one-sided estimate: arbitrarily rapid decreases in D3 are not
excluded. No upper bound on the joint fifth/phase expenditure is obtained.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- Positive joint fifth/phase loss makes the signed logarithmic top
derivative no larger than the genuine physical cubic forcing ratio. -/
theorem h3Path_topSignedLog_le_actualCubicRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a r : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hr : r ∈ Set.Ioo a T)
    (hD : 0 < velocityH3Dissipation3At u r) :
    h3PathPhysicalTopSignedLogRate244 hClass r ≤
      h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r := by
  have hBalance :=
    h3Path_topFifthPhaseJoint_eq_cubic_sub_signedLog244 hH3 hClass hr
  have hNonneg := h3Path_topFifthPhaseJoint_nonneg244
    hH3 hClass hr hD
  linarith only [hBalance, hNonneg]

/-- Ordinary real calculus: a derivative with a constant ceiling cannot
produce a larger endpoint secant on a closed interval. This does not
require the derivative to be integrable. -/
theorem h3_scalar_oneSidedDerivativeCeiling244
    (f : ℝ → ℝ) (s t K : ℝ) (hst : s ≤ t)
    (hContinuous : ContinuousOn f (Set.Icc s t))
    (hDifferentiable : DifferentiableOn ℝ f (interior (Set.Icc s t)))
    (hBound : ∀ r ∈ interior (Set.Icc s t), deriv f r ≤ K) :
    f t - f s ≤ K * (t - s) := by
  exact (convex_Icc s t).image_sub_le_mul_sub_of_deriv_le
    hContinuous hDifferentiable hBound
    s ⟨le_refl s, hst⟩ t ⟨hst, le_refl t⟩ hst

/-- Actual physical D3 logarithmic growth is controlled by any genuine
pointwise ceiling on the cubic-to-D3 ratio. NO signed-log integrability,
phase integrability, or fifth moment integrability is assumed. -/
theorem h3Path_topLogGrowth_le_actualCubicCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hCeiling : ∀ r, r ∈ Set.Ioo s t →
      h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r ≤ K) :
    Real.log (h3TerminalPhysicalTopDissipation3Path hClass t) -
      Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) ≤
      K * (t - s) := by
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
  have hBound : ∀ r ∈ interior (Set.Icc s t), deriv F r ≤ K := by
    intro r hr
    have hrc : r ∈ Set.Icc s t := interior_subset hr
    rw [(hDerivative r hrc).deriv]
    have hri : r ∈ Set.Ioo s t := by
      simpa only [interior_Icc] using hr
    exact (h3Path_topSignedLog_le_actualCubicRate244
      hH3 hClass (hInside r hrc) (hD r hrc)).trans (hCeiling r hri)
  exact h3_scalar_oneSidedDerivativeCeiling244 F s t K hst
    hContinuous hDiff hBound

/-- Continuity of the actual cubic-to-top-mass ratio on every strict
compact positive-D3 interval. It is NOT a terminal-uniform bound. -/
theorem h3Path_topActualCubicRate_continuousOn_Icc244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r) :
    ContinuousOn (h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass)
      (Set.Icc s t) := by
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
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass (hInside hr)]
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
  exact hRatioCont.congr hSame.symm

/-- The true cubic ratio admits an attained finite maximum on each
positive-D3 compact strict physical interval; this gives an *automatic*
one-sided forward logarithmic clock estimate, without temporal L1 hypotheses. -/
theorem h3Path_topLogGrowth_has_finite_actualCubicClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r) :
    ∃ r₀ : ℝ, r₀ ∈ Set.Icc s t ∧
      (∀ r, r ∈ Set.Icc s t →
        h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r ≤
          h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r₀) ∧
      Real.log (h3TerminalPhysicalTopDissipation3Path hClass t) -
        Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) ≤
          h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r₀ *
            (t - s) := by
  have hCont := h3Path_topActualCubicRate_continuousOn_Icc244
    hH3 hClass hs ht hst hD
  obtain ⟨r₀, hr₀, hMax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hst) hCont
  have hCeiling : ∀ r, r ∈ Set.Icc s t →
      h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r ≤
        h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r₀ := by
    intro r hr
    exact hMax hr
  refine ⟨r₀, hr₀, hCeiling, ?_⟩
  exact h3Path_topLogGrowth_le_actualCubicCeiling244
    hH3 hClass hs ht hst hD (fun r hr =>
      hCeiling r ⟨hr.1.le, hr.2.le⟩)

/-- A log-growth secant above K forces the ACTUAL cubic-to-top-mass
ratio above K at some interior physical time. This is the contrapositive
of the one-sided physical mean-value estimate, not a terminal estimate. -/
theorem h3Path_topLogGrowth_forces_actualCubicHighPoint244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t K : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (hGrowth : K * (t - s) <
      Real.log (h3TerminalPhysicalTopDissipation3Path hClass t) -
        Real.log (h3TerminalPhysicalTopDissipation3Path hClass s)) :
    ∃ r : ℝ, r ∈ Set.Ioo s t ∧
      K < h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r := by
  by_contra hNo
  have hCeiling : ∀ r, r ∈ Set.Ioo s t →
      h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r ≤ K := by
    intro r hr
    exact le_of_not_gt (by
      intro hHigh
      exact hNo ⟨r, hr, hHigh⟩)
  have hBound := h3Path_topLogGrowth_le_actualCubicCeiling244
    hH3 hClass hs ht hst hD hCeiling
  exact (not_lt_of_ge hBound) hGrowth

end
end PrimeTensor.FirstMonomialTriad
