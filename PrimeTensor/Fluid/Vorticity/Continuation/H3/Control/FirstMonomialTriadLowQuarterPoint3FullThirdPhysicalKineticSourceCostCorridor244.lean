import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticSourceDissipation244
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Exact physical kinetic source cost and persistent-dissipation corridor

The latest checkpoint identifies the kinetic component of the *actual* physical
projected source R(t):

    inner U(t) R(t) = -D0(t).

By Hilbert Cauchy-Schwarz this forces the magnitude of R to pay the kinetic
viscous dissipation D0, without asserting a sign for the other components of R.
The exact kinetic balance also prevents a strictly positive dissipation floor
from persisting longer than its kinetic energy permits.

These estimates do not bound H3 transport, rule out terminal concentration of
higher derivatives, or assume any endpoint trace.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The magnitude of the signed physical momentum-source pairing is exactly
its zeroth-order dissipation. This is the kinetic projection, not a norm
identity for the full projected source. -/
theorem h3Path_physicalSourcePairing_abs_eq_dissipation0_positiveTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    |inner ℝ
        (h3AuditInitialOldPhysicalHilbertTotal hH3 t)
        (h3PathActualProjectedMomentumSource244 hH3 t)| =
      velocityH3Dissipation0At u t := by
  rw [h3Path_physicalHilbertPairing_eq_negDissipation0_positiveTime244 hH3 t ht,
    abs_neg, abs_of_nonneg (velocityH3Dissipation0At_nonneg u t)]

/-- The physical projected momentum source pays for the genuine kinetic
viscous dissipation in the Hilbert Cauchy-Schwarz inequality. -/
theorem h3Path_dissipation0_le_physicalVelocity_mul_source_positiveTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    velocityH3Dissipation0At u t ≤
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ *
        ‖h3PathActualProjectedMomentumSource244 hH3 t‖ := by
  rw [← h3Path_physicalSourcePairing_abs_eq_dissipation0_positiveTime244
    hH3 t ht]
  exact abs_real_inner_le_norm _ _

/-- The scalar order-zero H3 kinetic energy is *exactly* the old physical
Hilbert norm square, so source magnitude also controls dissipation with the
square root of the actual physical kinetic mass. -/
theorem h3Path_dissipation0_le_sqrtKinetic_mul_source_positiveTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    velocityH3Dissipation0At u t ≤
      Real.sqrt (velocityH3Energy0At u t) *
        ‖h3PathActualProjectedMomentumSource244 hH3 t‖ := by
  have hCauchy :=
    h3Path_dissipation0_le_physicalVelocity_mul_source_positiveTime244
      hH3 t ht
  rwa [h3Audit_initialOldPhysicalHilbert_norm_eq_sqrt_kineticEnergy
    hH3 t ht] at hCauchy

/-- If the actual projected physical momentum source vanishes at a strict
time, its entire order-zero dissipation mass vanishes there. This does NOT
imply vanishing of the full third-order dissipation. -/
theorem h3Path_physicalSource_zero_implies_dissipation0_zero_positiveTime244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hZero : h3PathActualProjectedMomentumSource244 hH3 t = 0) :
    velocityH3Dissipation0At u t = 0 := by
  have hCost :=
    h3Path_dissipation0_le_physicalVelocity_mul_source_positiveTime244
      hH3 t ht
  rw [hZero, norm_zero, mul_zero] at hCost
  exact le_antisymm hCost (velocityH3Dissipation0At_nonneg u t)

/-- Nonnegativity of actual terminal kinetic energy bounds the total
order-zero dissipation spent on any compact positive-time interval. -/
theorem h3Path_dissipation0_integral_le_half_initialKinetic_positiveTimes244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t) :
    2 * (∫ r in s..t, velocityH3Dissipation0At u r) ≤
      velocityH3Energy0At u s := by
  have hBudget := h3Path_energy0_integratedDissipation0_positiveTimes244
    hH3 s t hs ht hst
  have hEndNonneg : 0 ≤ velocityH3Energy0At u t :=
    velocityH3Energy0At_nonneg u t
  linarith only [hBudget, hEndNonneg]

/-- A persistent scalar kinetic-dissipation floor on [s,t] must be paid by
the initial physical kinetic energy, with the exact factor two. -/
theorem h3Path_persistentDissipation0_floor_cost_positiveTimes244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s t κ : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t)
    (hFloor : ∀ r : ℝ, r ∈ Set.Icc s t →
      κ ≤ velocityH3Dissipation0At u r) :
    2 * κ * (t - s) ≤ velocityH3Energy0At u s := by
  have hSubset : Set.Icc s t ⊆ Set.Ioo (0 : ℝ) T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hDCont : ContinuousOn (velocityH3Dissipation0At u)
      (Set.Icc s t) :=
    (h3Path_dissipation0_continuousOn_positiveTime244 hH3).mono hSubset
  have hDInt : IntervalIntegrable (velocityH3Dissipation0At u)
      volume s t := hDCont.intervalIntegrable_of_Icc hst
  have hConstInt : IntervalIntegrable (fun _ : ℝ => κ)
      volume s t := continuousOn_const.intervalIntegrable_of_Icc hst
  have hComparison :
      (∫ _r in s..t, κ) ≤
        ∫ r in s..t, velocityH3Dissipation0At u r :=
    intervalIntegral.integral_mono_on hst hConstInt hDInt hFloor
  have hConstant : (∫ _r in s..t, κ) = κ * (t - s) := by
    simp [mul_comm]
  rw [hConstant] at hComparison
  have hBudget :=
    h3Path_dissipation0_integral_le_half_initialKinetic_positiveTimes244
      hH3 s t hs ht hst
  linarith only [hComparison, hBudget]

/-- If the proposed persistent rate κ is too expensive for the available
kinetic mass, a strict time with D0 < κ must occur on the interval. -/
theorem h3Path_exists_subcriticalDissipation0_witness_positiveTimes244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s t κ : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t)
    (hExcess : velocityH3Energy0At u s < 2 * κ * (t - s)) :
    ∃ r : ℝ, r ∈ Set.Icc s t ∧
      velocityH3Dissipation0At u r < κ := by
  by_contra hNo
  have hFloor : ∀ r : ℝ, r ∈ Set.Icc s t →
      κ ≤ velocityH3Dissipation0At u r := by
    intro r hr
    by_contra hNot
    have hLt : velocityH3Dissipation0At u r < κ :=
      lt_of_not_ge hNot
    exact hNo ⟨r, hr, hLt⟩
  have hCost :=
    h3Path_persistentDissipation0_floor_cost_positiveTimes244
      hH3 s t κ hs ht hst hFloor
  exact (not_lt_of_ge hCost) hExcess

/-- Quantitative terminal-midpoint obstruction: order-zero kinetic
viscous dissipation cannot stay strictly above κ throughout [s,(s+T)/2]
when κ(T-s) exceeds the initial kinetic mass. No limit at T is assumed. -/
theorem h3Path_terminalMidpoint_subcriticalDissipation0_witness244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s κ : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (hExcess : velocityH3Energy0At u s < κ * (T - s)) :
    ∃ r : ℝ, r ∈ Set.Icc s ((s + T) / 2) ∧
      velocityH3Dissipation0At u r < κ := by
  have hMidAbove : s ≤ (s + T) / 2 := by
    linarith only [hs.2]
  have hMidTime : (s + T) / 2 ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith only [hs.1, hs.2]
    · linarith only [hs.2]
  have hIdentity : 2 * κ * ((s + T) / 2 - s) = κ * (T - s) := by
    ring
  apply h3Path_exists_subcriticalDissipation0_witness_positiveTimes244
    hH3 s ((s + T) / 2) κ hs hMidTime hMidAbove
  rwa [hIdentity]

end
end PrimeTensor.FirstMonomialTriad
