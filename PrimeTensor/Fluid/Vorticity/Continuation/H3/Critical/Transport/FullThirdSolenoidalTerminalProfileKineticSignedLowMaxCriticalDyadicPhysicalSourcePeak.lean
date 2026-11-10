import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalCubicPhysicalClockBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopOneSidedCubicClock244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopCubicExactAction244
import Mathlib.Tactic

/-!
# Critical dyadic H3 physical source-peak alternative

At the cubic rate's sharp exponent, the pointwise estimate alone permits
D3(t) ~ (T-t)^(-8/3). The exact physical PDE adds an independent relation:

  (log D3)' = (M3 - M5 - P) / D3,    M5 >= 0, P >= 0.

The existing physical source-clock theorem gives eight log-two units of
necessary terminal charge over a last-half window. Combining that clock
with the exact fifth/phase balance and the one-sided physical mean-value
estimate gives the following unconditional *alternative* on that window:

  8 log 2 - 3 K (t-s)
      <= log B + 8 log (T-s) + 3 log D3(s),

or the ACTUAL normalized cubic Leray forcing M3/D3 exceeds K at some
strict physical time r in (s,t). A near-critical anchor thus forces an
attained physical source peak of inverse-window-duration magnitude.
The final theorem transfers the peak through the previously proved Fourier
norm-square identity to a real third-radial Leray forcing certificate.

This is a necessary conditional PDE constraint, not an unconditional upper
bound on M3/D3 and not a proof of Navier--Stokes continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- If the genuine physical cubic rate never exceeds K on a dyadic window,
then its earlier normalized critical dissipation factor must carry the
missing eight log-two units. The positive fifth/phase cost is retained in
the proof through the exact physical balance. -/
theorem thirdFullPhysical_dyadicCubicCeiling_forces_criticalAnchorExcess244
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
    (hCeiling : ∀ r, r ∈ Set.Ioo s t →
      h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r ≤ K) :
    8 * Real.log 2 - 3 * K * (t - s) ≤
      Real.log B + 8 * Real.log (T - s) +
        3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) := by
  have hCharge :=
    thirdFullPhysical_criticalCubicRate_forces_dyadicSourceCharge244
      hH3 hClass hs ht hst hD hDouble B hB hRate
  have hBalance :=
    h3Path_topJointAction_eq_cubic_sub_log_automatic244
      hH3 hClass hs ht hst hD
  have hGrowth :=
    h3Path_topLogGrowth_le_actualCubicCeiling244
      hH3 hClass hs ht hst hD hCeiling
  linarith only [hCharge, hBalance, hGrowth]

/-- No assumed forcing bound: at a genuine critical dyadic PDE window,
either the earlier critical-normalized top dissipation is excessive, or
there is an attained STRICT-time physical cubic source peak above K. -/
theorem thirdFullPhysical_criticalDyadicAnchorOrActualCubicSourcePeak244
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
    (K : ℝ) :
    (8 * Real.log 2 - 3 * K * (t - s) ≤
      Real.log B + 8 * Real.log (T - s) +
        3 * Real.log (h3TerminalPhysicalTopDissipation3Path hClass s)) ∨
      ∃ r : ℝ, r ∈ Set.Ioo s t ∧
        K < h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r := by
  classical
  by_cases hPeak : ∃ r : ℝ, r ∈ Set.Ioo s t ∧
      K < h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r
  · exact Or.inr hPeak
  · left
    apply thirdFullPhysical_dyadicCubicCeiling_forces_criticalAnchorExcess244
      hH3 hClass hs ht hst hD hDouble B hB hRate K
    intro r hr
    exact le_of_not_gt (by
      intro hHigh
      exact hPeak ⟨r, hr, hHigh⟩)

/-- A near-critical earlier anchor forces a true later physical source
peak. This consequence needs no separate temporal integrability assumption:
the exact PDE provides automatic compact-time integrability. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_actualCubicSourcePeak244
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
      K < h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r := by
  rcases thirdFullPhysical_criticalDyadicAnchorOrActualCubicSourcePeak244
      hH3 hClass hs ht hst hD hDouble B hB hRate K with hLarge | hPeak
  · exact False.elim ((not_lt_of_ge hLarge) hNear)
  · exact hPeak

/-- New physical Fourier-facing obstruction: on a near-critical dyadic
window some ACTUAL third-radial Leray forcing sum of squared Fourier L2
norms must beat K times the true top-third dissipation at that time. -/
theorem thirdFullPhysical_nearCriticalAnchor_forces_thirdRadialLerayPeak244
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
      K * h3TerminalPhysicalTopDissipation3Path hClass r <
        (2 * Real.pi) ^ 6 *
          ∑ j : Fin 3,
            (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
              hH3 hClass j r‖ : ℝ) ^ 2 := by
  obtain ⟨r, hr, hHigh⟩ :=
    thirdFullPhysical_nearCriticalAnchor_forces_actualCubicSourcePeak244
      hH3 hClass hs ht hst hD hDouble B hB hRate K hNear
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  have hDr : 0 < h3TerminalPhysicalTopDissipation3Path hClass r := by
    rw [h3TerminalPhysicalTopDissipation3Path_eq hClass hrClass]
    exact hD r ⟨hr.1.le, hr.2.le⟩
  rw [h3Path_topCubic_eq_thirdRadialLerayNormSquares244
    hH3 hClass hrClass] at hHigh
  exact ⟨r, hr, (lt_div_iff₀ hDr).mp hHigh⟩

end
end PrimeTensor.FirstMonomialTriad
