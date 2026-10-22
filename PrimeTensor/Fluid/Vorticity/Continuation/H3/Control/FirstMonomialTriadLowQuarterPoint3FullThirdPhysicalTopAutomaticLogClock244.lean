import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopOneSidedCubicClock244
import Mathlib.Tactic

/-!
# Automatic compact physical top logarithmic integrability

On a compact strict physical H3 interval with positive D3, the genuine cubic
rate C = M3/D3 is continuous and has an attained finite maximum K. The
physical PDE gives (log D3)' <= C <= K. Consequently the corrected function

    G(r) = K*r - log(D3(r))

has nonnegative derivative. Mathlib's integrability theorem for derivatives
of nondecreasing functions proves that K - (log D3)' is integrable, even
without assuming continuity or integrability of (log D3)' a priori.
Subtracting from the integrable constant K establishes automatic L1
integrability of the signed logarithmic derivative itself. This removes the
last signed-log integrability hypothesis from the joint fifth/phase action.

There is no uniform terminal estimate. The compact K may diverge as r -> T.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- An elementary but useful measure-theoretic consequence of a *one-sided*
derivative ceiling: the derivative is automatically interval-integrable.
The proof applies the nonnegative-derivative theorem to K*x-F(x). -/
theorem h3_scalar_signedRate_intervalIntegrable_of_upperDerivative244
    (F rate : ℝ → ℝ) (s t K : ℝ)
    (hst : s ≤ t)
    (hCont : ContinuousOn F (Set.Icc s t))
    (hDeriv : ∀ r, r ∈ Set.Ioo s t → HasDerivAt F (rate r) r)
    (hBound : ∀ r, r ∈ Set.Ioo s t → rate r ≤ K) :
    IntervalIntegrable rate volume s t := by
  let G : ℝ → ℝ := fun r => K * r - F r
  have hGCont : ContinuousOn G (Set.uIcc s t) := by
    rw [Set.uIcc_of_le hst]
    exact (continuousOn_const.mul continuousOn_id).sub hCont
  have hGDeriv :
      ∀ r, r ∈ Set.Ioo (min s t) (max s t) →
        HasDerivAt G (K - rate r) r := by
    intro r hr
    have hr' : r ∈ Set.Ioo s t := by
      simpa only [min_eq_left hst, max_eq_right hst] using hr
    have hLinear : HasDerivAt (fun x : ℝ => K * x) K r := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id r).const_mul K
    exact hLinear.sub (hDeriv r hr')
  have hGNonneg :
      ∀ r, r ∈ Set.Ioo (min s t) (max s t) → 0 ≤ K - rate r := by
    intro r hr
    have hr' : r ∈ Set.Ioo s t := by
      simpa only [min_eq_left hst, max_eq_right hst] using hr
    exact sub_nonneg.mpr (hBound r hr')
  have hDefectIntegrable :
      IntervalIntegrable (fun r : ℝ => K - rate r) volume s t :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg
      hGCont hGDeriv hGNonneg
  have hConst : IntervalIntegrable (fun _ : ℝ => K) volume s t :=
    intervalIntegrable_const
  have hIdentity : (fun r : ℝ => K - (K - rate r)) = rate := by
    funext r
    ring
  rw [← hIdentity]
  exact hConst.sub hDefectIntegrable

/-- The SIGNED top logarithmic rate is automatically integrable on every
compact strict physical interval with D3>0. No temporal L1 hypothesis for
fifth mass, cubic forcing, signed log, or phase is supplied. The only bound
used is the locally attained maximum of the actual continuous cubic ratio. -/
theorem h3Path_topSignedLog_intervalIntegrable_automatic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r) :
    IntervalIntegrable
      (h3PathPhysicalTopSignedLogRate244 hClass) volume s t := by
  obtain ⟨r₀, _hr₀, hMax, _⟩ :=
    h3Path_topLogGrowth_has_finite_actualCubicClock244
      hH3 hClass hs ht hst hD
  let F : ℝ → ℝ :=
    fun r => Real.log (h3TerminalPhysicalTopDissipation3Path hClass r)
  have hInside (r : ℝ) (hr : r ∈ Set.Icc s t) : r ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hLogDeriv (r : ℝ) (hr : r ∈ Set.Icc s t) :
      HasDerivAt F (h3PathPhysicalTopSignedLogRate244 hClass r) r :=
    h3Path_topLog_hasDerivAt244 hH3 hClass (hInside r hr) (hD r hr)
  have hCont : ContinuousOn F (Set.Icc s t) := by
    intro r hr
    exact (hLogDeriv r hr).continuousAt.continuousWithinAt
  have hDeriv : ∀ r, r ∈ Set.Ioo s t →
      HasDerivAt F (h3PathPhysicalTopSignedLogRate244 hClass r) r := by
    intro r hr
    exact hLogDeriv r ⟨hr.1.le, hr.2.le⟩
  have hBound : ∀ r, r ∈ Set.Ioo s t →
      h3PathPhysicalTopSignedLogRate244 hClass r ≤
        h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r₀ := by
    intro r hr
    have hrClosed : r ∈ Set.Icc s t := ⟨hr.1.le, hr.2.le⟩
    exact (h3Path_topSignedLog_le_actualCubicRate244
      hH3 hClass (hInside r hrClosed) (hD r hrClosed)).trans
      (hMax r hrClosed)
  exact h3_scalar_signedRate_intervalIntegrable_of_upperDerivative244
    F (h3PathPhysicalTopSignedLogRate244 hClass) s t
    (h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r₀)
    hst hCont hDeriv hBound

/-- The genuine combined normalized fifth plus phase action is now
integrable without ANY separate signed-log integrability hypothesis. -/
theorem h3Path_topFifthPhaseJoint_intervalIntegrable_automatic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r) :
    IntervalIntegrable
      (fun r : ℝ =>
        h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
          h3PathPhysicalTopPhaseActionRate244 hH3 hClass r)
      volume s t :=
  h3Path_topFifthPhaseJoint_intervalIntegrable244
    hH3 hClass hs ht hst hD
    (h3Path_topSignedLog_intervalIntegrable_automatic244
      hH3 hClass hs ht hst hD)

/-- The physical cubic/phase/fifth exact action identity has NO temporal
integrability assumptions left for its three genuine source channels. -/
theorem h3Path_topJointAction_eq_cubic_sub_log_automatic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r) :
    (∫ r in s..t,
      h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
        h3PathPhysicalTopPhaseActionRate244 hH3 hClass r) =
      (∫ r in s..t,
        h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r) -
        (Real.log (h3TerminalPhysicalTopDissipation3Path hClass t) -
          Real.log (h3TerminalPhysicalTopDissipation3Path hClass s)) := by
  exact h3Path_topFifthPhaseJointAction_eq_cubic_sub_endpointLog244
    hH3 hClass hs ht hst hD
    (h3Path_topSignedLog_intervalIntegrable_automatic244
      hH3 hClass hs ht hst hD)

/-- The exact time-integrated cubic forcing (rather than its compact
maximum) bounds forward logarithmic top-mass growth, without assuming any
signed-log or fifth/phase temporal integrability. -/
theorem h3Path_topLogGrowth_le_integratedActualCubicClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t)
    (hD : ∀ r, r ∈ Set.Icc s t → 0 < velocityH3Dissipation3At u r) :
    Real.log (h3TerminalPhysicalTopDissipation3Path hClass t) -
      Real.log (h3TerminalPhysicalTopDissipation3Path hClass s) ≤
      ∫ r in s..t,
        h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r := by
  have hExact := h3Path_topJointAction_eq_cubic_sub_log_automatic244
    hH3 hClass hs ht hst hD
  have hJointNonneg :
      0 ≤ ∫ r in s..t,
        h3PathPhysicalTopFifthActionRate244 hH3 hClass r +
          h3PathPhysicalTopPhaseActionRate244 hH3 hClass r := by
    apply intervalIntegral.integral_nonneg hst
    intro r hr
    have hrClass : r ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
    exact h3Path_topFifthPhaseJoint_nonneg244 hH3 hClass hrClass (hD r hr)
  linarith only [hExact, hJointNonneg]

/-- Unbounded forward logarithmic physical top mass on a fixed positive
tail forces the TRUE cumulative cubic forcing clock to be unbounded.
This is a necessary blowup-channel condition, not a regularity theorem. -/
theorem h3Path_unboundedTopLog_forces_unboundedCubicAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hD : ∀ r, r ∈ Set.Ioo a T → 0 < velocityH3Dissipation3At u r)
    (hUnbounded : ∀ K : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      K < Real.log (h3TerminalPhysicalTopDissipation3Path hClass t) -
        Real.log (h3TerminalPhysicalTopDissipation3Path hClass s)) :
    ∀ K : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      K < ∫ r in s..t,
        h3PathPhysicalTopCubicReplenishmentRate244 hH3 hClass r := by
  intro K
  obtain ⟨t, ht, hLarge⟩ := hUnbounded K
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 ht.1, ht.2⟩
  have hDClosed : ∀ r, r ∈ Set.Icc s t →
      0 < velocityH3Dissipation3At u r := by
    intro r hr
    exact hD r ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hBound := h3Path_topLogGrowth_le_integratedActualCubicClock244
    hH3 hClass hs htClass ht.1.le hDClosed
  exact ⟨t, ht, lt_of_lt_of_le hLarge hBound⟩

end
end PrimeTensor.FirstMonomialTriad
