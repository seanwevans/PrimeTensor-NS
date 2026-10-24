import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticGramTerminalAction244
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Scalar physical angular Gram action and strong terminal direction

On positive canonical terminal kinetic mass L, the normalized physical Hilbert
velocity N has unit norm and exact derivative N' = Q / sqrt(E0). The already
established scalar Gram determinant Delta obeys

  sqrt(Delta) / E0 = ||N'||.

This file integrates that identity on every ordered strict-time interval and
shows that vanishing terminal *angular length* is sufficient for a strong
terminal trace of N. Since sqrt(E0) tends to sqrt(L), the original physical
velocity U = sqrt(E0) N then has a strong terminal Hilbert trace with squared
norm L. The condition is NOT proved here and is not necessary for a terminal
trace: a convergent unit-direction curve can have infinite total variation.
No H3 continuation result follows from this theorem alone.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Scalar Gram angular length is precisely the integrated speed of the
actual physical Hilbert unit direction on strict ordered intervals. -/
theorem h3Path_physicalAngularGramAction_integral_eq_unitSpeed244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (s t : ℝ) (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t) :
    (∫ r in s..t,
      Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
        velocityH3Energy0At u r) =
      (∫ r in s..t, ‖deriv (h3PathPhysicalUnitVelocity244 hH3) r‖) := by
  apply intervalIntegral.integral_congr_Ioo_of_le hst
  intro r hr
  have hrTail : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
  have hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hrTail.1, hrTail.2⟩
  exact h3Path_physicalSourceGram_sqrt_div_kinetic_eq_angularSpeed244
    hH3 r hrAbs
      (h3Path_physicalKinetic_positive_of_positiveTerminal244
        hH3 hClass hL r hrTail)

/-- The endpoint-independent angular chord is bounded by the physical
scalar Gram length, with no choice of tangential direction or vector phase. -/
theorem h3Path_physicalUnitVelocity_chord_le_scalarAngularGramAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (s t : ℝ) (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t) :
    ‖h3PathPhysicalUnitVelocity244 hH3 t -
        h3PathPhysicalUnitVelocity244 hH3 s‖ ≤
      (∫ r in s..t,
        Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
          velocityH3Energy0At u r) := by
  have hOld := h3Path_physicalUnitVelocity_increment_le_angularAction244
    hH3 hClass hL s t hs ht hst
  have hAction :
      (∫ r in s..t,
        Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
          velocityH3Energy0At u r) =
      (∫ r in s..t,
        ‖(Real.sqrt (velocityH3Energy0At u r))⁻¹ •
          h3PathPhysicalTransverseSource244 hH3 r‖) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hst
    intro r hr
    have hrTail : r ∈ Set.Ioo a T :=
      ⟨lt_trans hs.1 hr.1, lt_trans hr.2 ht.2⟩
    have hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 hrTail.1, hrTail.2⟩
    have hRate := h3Path_physicalSourceGram_sqrt_div_kinetic_eq_angularSpeed244
      hH3 r hrAbs
        (h3Path_physicalKinetic_positive_of_positiveTerminal244
          hH3 hClass hL r hrTail)
    rw [(h3Path_physicalUnitVelocity_hasDerivAt_angular244 hH3 r hrAbs
      (h3Path_physicalKinetic_positive_of_positiveTerminal244
        hH3 hClass hL r hrTail)).deriv] at hRate
    exact hRate
  rw [hAction]
  exact hOld

/-- The scalar normalized angular Gram length becomes uniformly small on
later strict terminal intervals. This is an additional analytic hypothesis. -/
def H3PhysicalAngularGramTerminalTailVanishing244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ s : ℝ in 𝓝[<] T,
      s ∈ Set.Ioo a T ∧
        ∀ t : ℝ, t ∈ Set.Ioo a T → s ≤ t →
          (∫ r in s..t,
            Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
              velocityH3Energy0At u r) < ε

/-- Uniform vanishing scalar angular length directly forces a small
physical Hilbert-sphere chord over every later strict time interval. -/
theorem h3Path_physicalUnitVelocity_uniformTerminalChordSmall_of_angularGram244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hGram : H3PhysicalAngularGramTerminalTailVanishing244 (a := a) hH3)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in 𝓝[<] T,
      s ∈ Set.Ioo a T ∧
        ∀ t : ℝ, t ∈ Set.Ioo a T → s ≤ t →
          ‖h3PathPhysicalUnitVelocity244 hH3 t -
            h3PathPhysicalUnitVelocity244 hH3 s‖ < ε := by
  filter_upwards [hGram ε hε] with s hs
  refine ⟨hs.1, ?_⟩
  intro t ht hst
  exact (h3Path_physicalUnitVelocity_chord_le_scalarAngularGramAction244
    hH3 hClass hL s t hs.1 ht hst).trans_lt (hs.2 t ht hst)

/-- In the positive-terminal-mass case, scalar angular action alone gives
a strong limit of the actual normalized physical Hilbert unit direction. -/
theorem h3Path_physicalUnitVelocity_existsTerminalTrace_of_angularGram244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hGram : H3PhysicalAngularGramTerminalTailVanishing244 (a := a) hH3) :
    ∃ N : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3PathPhysicalUnitVelocity244 hH3) (𝓝[<] T) (𝓝 N) := by
  let F : ℝ → H3PhysicalRealFinVectorL2Hilbert :=
    h3PathPhysicalUnitVelocity244 hH3
  have hCauchy : Cauchy (Filter.map F (𝓝[<] T)) := by
    apply Metric.cauchy_iff.mpr
    constructor
    · infer_instance
    · intro ε hε
      have hSmall :=
        h3Path_physicalUnitVelocity_uniformTerminalChordSmall_of_angularGram244
          hH3 hClass hL hGram ε hε
      let A : Set ℝ :=
        {s | s ∈ Set.Ioo a T ∧
          ∀ t : ℝ, t ∈ Set.Ioo a T → s ≤ t → ‖F t - F s‖ < ε}
      have hAMem : A ∈ 𝓝[<] T := hSmall
      refine ⟨F '' A, ?_, ?_⟩
      · change F ⁻¹' (F '' A) ∈ 𝓝[<] T
        exact Filter.mem_of_superset hAMem (fun s hs => ⟨s, hs, rfl⟩)
      · intro x hx y hy
        obtain ⟨s, hs, rfl⟩ := hx
        obtain ⟨t, ht, rfl⟩ := hy
        change dist (F s) (F t) < ε
        change s ∈ Set.Ioo a T ∧
          (∀ z : ℝ, z ∈ Set.Ioo a T → s ≤ z → ‖F z - F s‖ < ε) at hs
        change t ∈ Set.Ioo a T ∧
          (∀ z : ℝ, z ∈ Set.Ioo a T → t ≤ z → ‖F z - F t‖ < ε) at ht
        by_cases hst : s ≤ t
        · rw [dist_eq_norm, norm_sub_rev]
          exact hs.2 t ht.1 hst
        · have hts : t ≤ s := le_of_not_ge hst
          rw [dist_eq_norm]
          exact ht.2 s hs.1 hts
  obtain ⟨N, hN⟩ := (cauchy_map_iff_exists_tendsto).mp hCauchy
  exact ⟨N, hN⟩

/-- A terminal limit of the physical unit-direction path necessarily lies
on the Hilbert unit sphere; no angular action assumption is needed here. -/
theorem h3Path_physicalUnitVelocity_terminalTrace_norm_eq_one244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (N : H3PhysicalRealFinVectorL2Hilbert)
    (hN : Tendsto (h3PathPhysicalUnitVelocity244 hH3) (𝓝[<] T) (𝓝 N)) :
    ‖N‖ = 1 := by
  have hNear : ∀ᶠ t : ℝ in 𝓝[<] T, t ∈ Set.Ioo a T := by
    have hAfter : ∀ᶠ t : ℝ in 𝓝 T, a < t :=
      Ioi_mem_nhds hClass.terminal_start.2
    filter_upwards [hAfter.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t hpos hlt
    exact ⟨hpos, hlt⟩
  have hNorm : Tendsto
      (fun t : ℝ => ‖h3PathPhysicalUnitVelocity244 hH3 t‖)
      (𝓝[<] T) (𝓝 (‖N‖)) :=
    (continuous_norm.tendsto N).comp hN
  have hUnit : Tendsto
      (fun t : ℝ => ‖h3PathPhysicalUnitVelocity244 hH3 t‖)
      (𝓝[<] T) (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hNear] with t ht
    exact (h3Path_physicalUnitVelocity_norm_eq_one244 hH3 t
      ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
      (h3Path_physicalKinetic_positive_of_positiveTerminal244
        hH3 hClass hL t ht)).symm
  exact tendsto_nhds_unique hNorm hUnit

/-- A terminal unit direction together with L>0 and the already established
kinetic limit reconstructs the actual physical L2 velocity trace. -/
theorem h3Path_physicalVelocity_terminalTrace_of_unitDirection244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (N : H3PhysicalRealFinVectorL2Hilbert)
    (hN : Tendsto (h3PathPhysicalUnitVelocity244 hH3) (𝓝[<] T) (𝓝 N)) :
    Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (𝓝[<] T)
      (𝓝 (Real.sqrt (h3PathCanonicalTerminalKineticEnergyAt u a T) • N)) := by
  let L : ℝ := h3PathCanonicalTerminalKineticEnergyAt u a T
  have hELimit : Tendsto (velocityH3Energy0At u) (𝓝[<] T) (𝓝 L) :=
    h3PathCanonical_terminalKineticEnergy_tendsto_noCanonicalData hH3 hClass
  have hRootLimit : Tendsto
      (fun r : ℝ => Real.sqrt (velocityH3Energy0At u r))
      (𝓝[<] T) (𝓝 (Real.sqrt L)) := by
    simpa only [Function.comp_def] using
      ((Real.continuous_sqrt.tendsto L).comp hELimit)
  have hSmul : Tendsto
      (fun r : ℝ => Real.sqrt (velocityH3Energy0At u r) •
        h3PathPhysicalUnitVelocity244 hH3 r)
      (𝓝[<] T) (𝓝 (Real.sqrt L • N)) :=
    hRootLimit.smul hN
  have hNear : ∀ᶠ t : ℝ in 𝓝[<] T, t ∈ Set.Ioo a T := by
    have hAfter : ∀ᶠ t : ℝ in 𝓝 T, a < t :=
      Ioi_mem_nhds hClass.terminal_start.2
    filter_upwards [hAfter.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t hpos hlt
    exact ⟨hpos, hlt⟩
  apply hSmul.congr'
  filter_upwards [hNear] with t ht
  have hPos : 0 < velocityH3Energy0At u t :=
    h3Path_physicalKinetic_positive_of_positiveTerminal244 hH3 hClass hL t ht
  have hRoot : 0 < Real.sqrt (velocityH3Energy0At u t) :=
    Real.sqrt_pos.2 hPos
  change Real.sqrt (velocityH3Energy0At u t) •
      ((Real.sqrt (velocityH3Energy0At u t))⁻¹ •
        h3AuditInitialOldPhysicalHilbertTotal hH3 t) =
        h3AuditInitialOldPhysicalHilbertTotal hH3 t
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hRoot), one_smul]

/-- An entirely scalar angular Gram tail assumption suffices to produce
both a unit terminal direction and the exact-mass physical L2 trace. -/
theorem h3Path_physicalAngularGramTerminalTrace_and_exactMass244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hGram : H3PhysicalAngularGramTerminalTailVanishing244 (a := a) hH3) :
    ∃ N U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3PathPhysicalUnitVelocity244 hH3) (𝓝[<] T) (𝓝 N) ∧
        ‖N‖ = 1 ∧
        U = Real.sqrt (h3PathCanonicalTerminalKineticEnergyAt u a T) • N ∧
        Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U) ∧
        ‖U‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T := by
  obtain ⟨N, hN⟩ :=
    h3Path_physicalUnitVelocity_existsTerminalTrace_of_angularGram244
      hH3 hClass hL hGram
  have hNorm : ‖N‖ = 1 :=
    h3Path_physicalUnitVelocity_terminalTrace_norm_eq_one244
      hH3 hClass hL N hN
  have hU := h3Path_physicalVelocity_terminalTrace_of_unitDirection244
    hH3 hClass hL N hN
  refine ⟨N, Real.sqrt (h3PathCanonicalTerminalKineticEnergyAt u a T) • N,
    hN, hNorm, rfl, hU, ?_⟩
  exact h3Path_physicalVelocity_terminalTrace_norm_sq_eq_kineticLimit244
    hH3 hClass _ hU

end
end PrimeTensor.FirstMonomialTriad
