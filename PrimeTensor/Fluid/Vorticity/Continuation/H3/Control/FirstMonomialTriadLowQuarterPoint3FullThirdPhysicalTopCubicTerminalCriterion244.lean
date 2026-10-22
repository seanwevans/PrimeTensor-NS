import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopAutomaticLogClock244
import Mathlib.Tactic

/-!
# Physical top dissipation: exponential cubic-clock criterion and cofinal spikes

The exact positive Fourier phase defect and fifth moment imply
  (log D3)' <= C3 := M3/D3,
while the preceding module establishes automatic compact-interval
integrability and the sharper integrated logarithmic estimate.

Exponentiation now gives a physical upper bound
  D3(t) <= D3(s) exp (integral_s^t C3).
A uniform cumulative source clock therefore bounds the actual fourth-radial
moment through the terminal tail. Conversely, escape of that moment forces
unbounded cubic action. Moreover, the older pointwise one-sided PDE ceiling
shows that such escape forces genuinely unbounded cubic source ratios on
arbitrarily late intervals, not merely a large compact-time maximum.

These are necessary terminal criteria. They do not assert a uniform bound on
cubic forcing or prove an unconditional continuation theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- Real logarithmic comparison in multiplicative (not additive) coordinates. -/
theorem h3_scalar_logGrowth_implies_exponentialBound244
    {A B L : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hClock : Real.log B - Real.log A ≤ L) :
    B ≤ A * Real.exp L := by
  have hExp :
      Real.exp (Real.log B - Real.log A) ≤ Real.exp L :=
    Real.exp_le_exp.mpr hClock
  have hRatio : B / A ≤ Real.exp L := by
    simpa only [Real.exp_sub, Real.exp_log hB, Real.exp_log hA] using hExp
  have hProduct : B ≤ Real.exp L * A :=
    (div_le_iff₀ hA).mp hRatio
  calc
    B ≤ Real.exp L * A := hProduct
    _ = A * Real.exp L := mul_comm _ _

/-- The exact PHYSICAL fourth-radial dissipation mass obeys an exponential
bound governed by the integrated genuine cubic Leray forcing / dissipation
ratio. No separate temporal-integrability assumptions remain. -/
theorem h3Path_topPhysicalDissipation_le_expCubicAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r) :
    velocityH3Dissipation3At u t ≤
      velocityH3Dissipation3At u s *
        Real.exp (∫ r in s..t,
          h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r) := by
  have hPosS : 0 < h3TerminalPhysicalTopDissipation3Path hClass s := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hs]
    exact hD s ⟨le_refl s, hst⟩
  have hPosT : 0 < h3TerminalPhysicalTopDissipation3Path hClass t := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass ht]
    exact hD t ⟨hst, le_refl t⟩
  have hLog := h3Path_topLogGrowth_le_integratedActualCubicClock244
    hH3 hClass hs ht hst hD
  have hExp := h3_scalar_logGrowth_implies_exponentialBound244
    hPosS hPosT hLog
  rw [h3TerminalPhysicalTopDissipation3Path_eq hClass ht,
      h3TerminalPhysicalTopDissipation3Path_eq hClass hs] at hExp
  exact hExp

/-- Bounded cumulative physical cubic action on a fixed strict terminal
subtail bounds the actual top Fourier dissipation there. This is a concrete
conditional continuation criterion for the top moment, not an assumption
that a uniformly bounded cubic source automatically exists. -/
theorem h3Path_boundedCubicAction_bounds_topPhysicalDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s B : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hD : ∀ r, r ∈ Set.Ioo a T → 0 < velocityH3Dissipation3At u r)
    (hAction : ∀ t, t ∈ Set.Ioo s T →
      (∫ r in s..t,
        h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r) ≤ B) :
    ∀ t, t ∈ Set.Ioo s T →
      velocityH3Dissipation3At u t ≤
        velocityH3Dissipation3At u s * Real.exp B := by
  intro t ht
  have htClass : t ∈ Set.Ioo a T := ⟨lt_trans hs.1 ht.1, ht.2⟩
  have hClosed : ∀ r, r ∈ Set.Icc s t →
      0 < velocityH3Dissipation3At u r := by
    intro r hr
    exact hD r ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hPhysical := h3Path_topPhysicalDissipation_le_expCubicAction244
    hH3 hClass hs htClass ht.1.le hClosed
  have hExp :
      Real.exp (∫ r in s..t,
        h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r) ≤
        Real.exp B := Real.exp_le_exp.mpr (hAction t ht)
  exact hPhysical.trans
    (mul_le_mul_of_nonneg_left hExp (hD s hs).le)

/-- If the actual physical fourth-radial top dissipation escapes every
finite ceiling along a fixed strict tail, the integrated third-radial
Leray forcing clock is necessarily unbounded on that tail. -/
theorem h3Path_unboundedPhysicalTop_forces_unboundedCubicAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hD : ∀ r, r ∈ Set.Ioo a T → 0 < velocityH3Dissipation3At u r)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t) :
    ∀ B : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      B < ∫ r in s..t,
        h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r := by
  intro B
  by_contra hNo
  have hClockBound : ∀ t, t ∈ Set.Ioo s T →
      (∫ r in s..t,
        h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r) ≤ B := by
    intro t ht
    exact le_of_not_gt (by
      intro hExcess
      exact hNo ⟨t, ht, hExcess⟩)
  have hPhysical := h3Path_boundedCubicAction_bounds_topPhysicalDissipation244
    hH3 hClass hs hD hClockBound
  obtain ⟨t, ht, hLarge⟩ := hEscape
    (velocityH3Dissipation3At u s * Real.exp B)
  exact (not_lt_of_ge (hPhysical t ht)) hLarge

/-- Physical top-moment escape forces the ACTUAL cubic ratio above every
chosen threshold at a later strict physical time. This uses the signed
PDE derivative ceiling, not just an abstract escaping Fourier moment. -/
theorem h3Path_unboundedPhysicalTop_forces_highCubicRatio244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hD : ∀ r, r ∈ Set.Ioo a T → 0 < velocityH3Dissipation3At u r)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t) :
    ∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r := by
  intro K
  by_contra hNo
  let L : ℝ := max K 0
  have hL : 0 ≤ L := le_max_right K 0
  have hCeiling : ∀ r, r ∈ Set.Ioo s T →
      h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r ≤ L := by
    intro r hr
    have hNot : ¬ K < h3PathPhysicalTopCubicReplenishmentRate244
        hH3 hClass r := by
      intro hHigh
      exact hNo ⟨r, hr, hHigh⟩
    exact (le_of_not_gt hNot).trans (le_max_left K 0)
  have hBound : ∀ t, t ∈ Set.Ioo s T →
      velocityH3Dissipation3At u t ≤
        velocityH3Dissipation3At u s * Real.exp (L * (T - s)) := by
    intro t ht
    have htClass : t ∈ Set.Ioo a T := ⟨lt_trans hs.1 ht.1, ht.2⟩
    have hClosed : ∀ r, r ∈ Set.Icc s t →
        0 < velocityH3Dissipation3At u r := by
      intro r hr
      exact hD r ⟨lt_of_lt_of_le hs.1 hr.1,
        lt_of_le_of_lt hr.2 ht.2⟩
    have hLog := h3Path_topLogGrowth_le_actualCubicCeiling244
      hH3 hClass hs htClass ht.1.le hClosed
      (fun r hr => hCeiling r ⟨hr.1, lt_trans hr.2 ht.2⟩)
    have hDuration : L * (t - s) ≤ L * (T - s) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le s) hL
    have hGrowth := h3_scalar_logGrowth_implies_exponentialBound244
      (by
        rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hs]
        exact hD s hs)
      (by
        rw [h3TerminalPhysicalTopDissipation3Path_eq hClass htClass]
        exact hD t htClass)
      (hLog.trans hDuration)
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass htClass,
        h3TerminalPhysicalTopDissipation3Path_eq hClass hs] at hGrowth
    exact hGrowth
  obtain ⟨t, ht, hLarge⟩ := hEscape
    (velocityH3Dissipation3At u s * Real.exp (L * (T - s)))
  exact (not_lt_of_ge (hBound t ht)) hLarge

/-- The near-Young signed physical obstruction no longer needs a separate
hypothesis that the top signed logarithmic derivative is integrable. That
integrability follows from the physical PDE on the strict interval. -/
theorem h3Path_nearYoung_forces_jointAction_automaticLog244
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
  exact h3Path_nearYoung_forces_jointFifthPhaseAction244
    hH3 hClass hs ht hst hMass hD
    hDerivativeIntegrable hMiddleIntegrable hTopIntegrable
    hLossIntegrable hDownIntegrable hUpIntegrable
    (h3Path_topSignedLog_intervalIntegrable_automatic244
      hH3 hClass hs ht hst.le hD)
    hK hNear

end
end PrimeTensor.FirstMonomialTriad
