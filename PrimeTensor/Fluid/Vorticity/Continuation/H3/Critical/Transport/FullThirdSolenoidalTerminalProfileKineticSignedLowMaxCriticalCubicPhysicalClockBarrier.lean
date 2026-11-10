import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalFiveThirdsScalarSharpness
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopAutomaticLogClock244
import Mathlib.Tactic

/-!
# Physical cubic source clock at the critical H3 terminal scale

The scalar critical five-thirds counterprofile saturates `1 ≤ B * d^8 * D3^3`.
For a genuine physical H3 path there is an additional EXACT PDE balance

  D3' + M5 + P = M3,   M5 ≥ 0, P ≥ 0.

On a compact strict positive-D3 interval [s,t], the previously established
physical action identity gives

  ∫ (M3/D3) - ∫ ((M5+P)/D3) = log D3(t) - log D3(s).

If the cubic rate is in force at t, taking logarithms, with d=T-t>0,
gives `0 ≤ log B + 8 log d + 3 log D3(t)`. The resulting quantitative
physical gate is

  8 log((T-s)/(T-t))
    ≤ 3 (actual cubic action - actual fifth-plus-phase action)
      + log(B * (T-s)^8 * D3(s)^3).

In particular each last-half terminal clock incurs eight log-two units
of normalized *net* source charge, up to a fixed initial log offset.
This uses the actual physical cubic Leray forcing and the genuine fifth and
phase losses, not an artificial scalar path. It does NOT bound those charges
from above or exclude singularity; it identifies the missing upper PDE
estimate needed to cross the scalar critical frontier.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The genuine cubic physical rate forces a quantitative *net* source clock,
with the fifth-order viscous and Fourier-phase expenditure retained. -/
theorem thirdFullPhysical_criticalCubicRate_forces_actualSourceClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (B : ℝ) (hB : 0 < B)
    (hRate : 1 ≤ B * (T - t) ^ 8 *
      (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3) :
    8 * (Real.log (T - s) - Real.log (T - t)) ≤
      3 * ((∫ r in s..t,
          h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r) -
        (∫ r in s..t,
          h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
            h3PathPhysicalTopPhaseActionRate244 hH3 hClass r)) +
        Real.log B + 8 * Real.log (T - s) +
          3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) := by
  have hd : 0 < T - t := sub_pos.mpr ht.2
  have hDt : 0 < h3TerminalPhysicalTopDissipation3Path hClass t := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass ht]
    exact hD t ⟨hst, le_refl t⟩
  have hExpansion :
      Real.log (B * (T - t) ^ 8 *
          (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3) =
        Real.log B + 8 * Real.log (T - t) +
          3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass t) := by
    rw [Real.log_mul
          (ne_of_gt (mul_pos hB (pow_pos hd 8)))
          (ne_of_gt (pow_pos hDt 3)),
        Real.log_mul (ne_of_gt hB) (ne_of_gt (pow_pos hd 8)),
        Real.log_pow, Real.log_pow]
    ring
  have hLogRate :
      0 ≤ Real.log B + 8 * Real.log (T - t) +
        3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass t) := by
    have hLog := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hRate
    rw [Real.log_one, hExpansion] at hLog
    exact hLog
  have hPhysical := h3Path_topJointAction_eq_cubic_sub_log_automatic244
    hH3 hClass hs ht hst hD
  linarith only [hLogRate, hPhysical]

/-- A genuine normalized physical source deficit rules out the cubic
terminal rate at the later physical time. This is the explicit missing
PDE upper-budget gate, not an unconditional upper bound. -/
theorem thirdFullPhysical_actualSourceClock_deficit_excludesCriticalCubicRate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r)
    (B : ℝ) (hB : 0 < B)
    (hDeficit :
      3 * ((∫ r in s..t,
          h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r) -
        (∫ r in s..t,
          h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
            h3PathPhysicalTopPhaseActionRate244 hH3 hClass r)) +
        Real.log B + 8 * Real.log (T - s) +
          3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) <
        8 * (Real.log (T - s) - Real.log (T - t))) :
    B * (T - t) ^ 8 *
      (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3 < 1 := by
  apply lt_of_not_ge
  intro hRate
  have hCharge :=
    thirdFullPhysical_criticalCubicRate_forces_actualSourceClock244
      hH3 hClass hs ht hst hD B hB hRate
  exact (not_lt_of_ge hCharge) hDeficit

/-- On an exact last-half terminal window, the full physical normalized
source must pay eight log-two units, including the true fifth/phase loss. -/
theorem thirdFullPhysical_criticalCubicRate_forces_dyadicSourceCharge244
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
      (h3TerminalPhysicalTopDissipation3Path hClass t) ^ 3) :
    8 * Real.log 2 ≤
      3 * ((∫ r in s..t,
          h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r) -
        (∫ r in s..t,
          h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
            h3PathPhysicalTopPhaseActionRate244 hH3 hClass r)) +
        Real.log B + 8 * Real.log (T - s) +
          3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) := by
  have hd : 0 < T - t := sub_pos.mpr ht.2
  have hClock :
      Real.log (T - s) - Real.log (T - t) = Real.log 2 := by
    calc
      Real.log (T - s) - Real.log (T - t) =
          (Real.log 2 + Real.log (T - t)) - Real.log (T - t) := by
        rw [hDouble,
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hd)]
      _ = Real.log 2 := by ring
  have hCharge :=
    thirdFullPhysical_criticalCubicRate_forces_actualSourceClock244
      hH3 hClass hs ht hst hD B hB hRate
  rw [hClock] at hCharge
  exact hCharge

end
end PrimeTensor.FirstMonomialTriad
