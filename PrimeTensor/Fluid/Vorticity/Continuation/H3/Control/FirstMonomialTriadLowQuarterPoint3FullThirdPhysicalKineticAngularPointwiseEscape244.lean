import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticAngularPersistentObstruction244
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Terminal angular Gram bursts force unbounded instantaneous physical angular speed

A positive lower bound for the scalar angular action on arbitrarily short
terminal intervals forces cofinal unboundedness of its instantaneous rate.
The rate is continuous on every strict positive-kinetic interval because it
coincides with the norm of the actual normalized Hilbert derivative.

Thus failure of the strong physical L² terminal trace at positive kinetic mass
implies that, for every terminal cutoff and every finite threshold, some later
physical time has angular velocity norm above the threshold.

This is a consequence of failure of the terminal trace, NOT of H³ nonextension.
A path with an L² terminal trace can still have unbounded angular speed, so
none of the converse statements is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- On a positive-terminal-kinetic tail, the scalar angular Gram integrand
is continuous: it is the norm of the continuous normalized transverse source. -/
theorem h3Path_physicalAngularGramRate_continuousOn_positiveTerminal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T) :
    ContinuousOn
      (fun r : ℝ =>
        Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
          velocityH3Energy0At u r) (Set.Ioo a T) := by
  have hAbs : Set.Ioo a T ⊆ Set.Ioo (0 : ℝ) T := by
    intro r hr
    exact ⟨lt_trans hClass.terminal_start.1 hr.1, hr.2⟩
  have hECont : ContinuousOn (velocityH3Energy0At u) (Set.Ioo a T) :=
    (h3Audit_initialKineticEnergy_continuousOn_positiveInterval hH3).mono hAbs
  have hRootCont : ContinuousOn
      (fun r : ℝ => Real.sqrt (velocityH3Energy0At u r)) (Set.Ioo a T) :=
    Real.continuous_sqrt.comp_continuousOn hECont
  have hInvCont : ContinuousOn
      (fun r : ℝ => (Real.sqrt (velocityH3Energy0At u r))⁻¹)
      (Set.Ioo a T) := by
    exact hRootCont.inv₀ (fun r hr => ne_of_gt (Real.sqrt_pos.2
      (h3Path_physicalKinetic_positive_of_positiveTerminal244
        hH3 hClass hL r hr)))
  have hQCont : ContinuousOn
      (h3PathPhysicalTransverseSource244 hH3) (Set.Ioo a T) :=
    (h3Path_physicalSourceChannels_continuousOn_positiveTerminal244
      hH3 hClass hL).2
  have hRateCont : ContinuousOn
      (fun r : ℝ =>
        ‖(Real.sqrt (velocityH3Energy0At u r))⁻¹ •
          h3PathPhysicalTransverseSource244 hH3 r‖)
      (Set.Ioo a T) := (hInvCont.smul hQCont).norm
  apply hRateCont.congr
  intro r hr
  have hrAbs : r ∈ Set.Ioo (0 : ℝ) T := hAbs hr
  have hE : 0 < velocityH3Energy0At u r :=
    h3Path_physicalKinetic_positive_of_positiveTerminal244
      hH3 hClass hL r hr
  have hGram := h3Path_physicalSourceGram_sqrt_div_kinetic_eq_angularSpeed244
    hH3 r hrAbs hE
  rw [(h3Path_physicalUnitVelocity_hasDerivAt_angular244
    hH3 r hrAbs hE).deriv] at hGram
  exact hGram

/-- A uniform upper bound on the instantaneous angular Gram rate bounds
its integral by the threshold times the length of every ordered interval. -/
theorem h3Path_physicalAngularGramAction_le_of_localRateCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (C : ℝ)
    (hCeil : ∀ r : ℝ, r ∈ Set.Ioo b T →
      Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
        velocityH3Energy0At u r ≤ C)
    (s t : ℝ) (hs : s ∈ Set.Ioo b T) (ht : t ∈ Set.Ioo b T)
    (hst : s ≤ t) :
    (∫ r in s..t,
      Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
        velocityH3Energy0At u r) ≤ C * (t - s) := by
  have hSet : Set.Icc s t ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_trans hb.1 (lt_of_lt_of_le hs.1 hr.1),
      lt_of_le_of_lt hr.2 ht.2⟩
  have hBSet : Set.Icc s t ⊆ Set.Ioo b T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hFInt : IntervalIntegrable
      (fun r : ℝ =>
        Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
          velocityH3Energy0At u r) volume s t :=
    ((h3Path_physicalAngularGramRate_continuousOn_positiveTerminal244
      hH3 hClass hL).mono hSet).intervalIntegrable_of_Icc hst
  have hBound :
      (∫ r in s..t,
        Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
          velocityH3Energy0At u r) ≤
      (∫ _r in s..t, C) := by
    apply intervalIntegral.integral_mono_on hst hFInt intervalIntegrable_const
    intro r hr
    exact hCeil r (hBSet hr)
  calc
    (∫ r in s..t,
      Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
        velocityH3Energy0At u r) ≤ (∫ _r in s..t, C) := hBound
    _ = C * (t - s) := by simp [mul_comm]

/-- Cofinal fixed positive angular Gram bursts are incompatible with any
pointwise ceiling on a terminal subtail: the rate is cofinally unbounded. -/
theorem h3Path_physicalAngularGramRate_cofinally_unbounded_of_bursts244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hBursts : H3PhysicalAngularGramCofinalBursts244 (a := a) hH3) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
          velocityH3Energy0At u r := by
  obtain ⟨ε, hε, hIntervals⟩ := hBursts
  intro b hb M
  classical
  by_contra hNo
  let B : ℝ := max M 0
  let C : ℝ := B + 1
  have hBNonneg : 0 ≤ B := le_max_right M 0
  have hCPos : 0 < C := by dsimp [C]; linarith only [hBNonneg]
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hCeil : ∀ r : ℝ, r ∈ Set.Ioo b T →
      Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
        velocityH3Energy0At u r ≤ B := by
    intro r hr
    have hBound :
        Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
          velocityH3Energy0At u r ≤ M := by
      apply le_of_not_gt
      intro hGreater
      exact hNo ⟨r, hr, hGreater⟩
    exact hBound.trans (le_max_left M 0)
  let δ : ℝ := ε / C
  have hδ : 0 < δ := div_pos hε hCPos
  have hUpper : max b (T - δ) < T := by
    apply max_lt hb.2
    linarith only [hδ]
  let b' : ℝ := (max b (T - δ) + T) / 2
  have hb'Range : max b (T - δ) < b' ∧ b' < T := by
    dsimp [b']
    constructor <;> linarith only [hUpper]
  have hb' : b' ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 (lt_of_le_of_lt (le_max_left b (T - δ)) hb'Range.1),
      hb'Range.2⟩
  obtain ⟨s, t, hs, ht, hst, hBurst⟩ := hIntervals b' hb'
  have hsB : s ∈ Set.Ioo b T :=
    ⟨lt_trans (lt_of_le_of_lt (le_max_left b (T - δ)) hb'Range.1) hs.1,
      hs.2⟩
  have htB : t ∈ Set.Ioo b T :=
    ⟨lt_trans (lt_of_le_of_lt (le_max_left b (T - δ)) hb'Range.1) ht.1,
      ht.2⟩
  have hLength : t - s < δ := by
    have hLower : T - δ ≤ max b (T - δ) := le_max_right b (T - δ)
    linarith only [hLower, hb'Range.1, hs.1, ht.2]
  have hBound := h3Path_physicalAngularGramAction_le_of_localRateCeiling244
    hH3 hClass hL b hb B hCeil s t hsB htB hst
  have hNonnegLength : 0 ≤ t - s := sub_nonneg.mpr hst
  have hBUpper : B * (t - s) ≤ C * (t - s) :=
    mul_le_mul_of_nonneg_right hBC hNonnegLength
  have hCUpper : C * (t - s) < C * δ :=
    mul_lt_mul_of_pos_left hLength hCPos
  have hCancel : C * δ = ε := by
    change C * (ε / C) = ε
    calc
      C * (ε / C) = (ε / C) * C := mul_comm _ _
      _ = ε := div_mul_cancel₀ _ (ne_of_gt hCPos)
  linarith only [hBurst, hBound, hBUpper, hCUpper, hCancel]

/-- Failure of the strong physical L² terminal trace at positive terminal
kinetic mass forces arbitrarily large instantaneous angular Gram rate on
*every* strict terminal subtail. -/
theorem h3Path_physicalAngularGramRate_cofinally_unbounded_of_noTrace244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < Real.sqrt (h3PathPhysicalSourceGramDefect244 hH3 r) /
          velocityH3Energy0At u r := by
  exact h3Path_physicalAngularGramRate_cofinally_unbounded_of_bursts244
    hH3 hClass hL
      (h3Path_physicalAngularGram_cofinalBursts_of_noVelocityTrace244
        hH3 hClass hL hNoTrace)

/-- This is precisely the cofinal unboundedness of physical normalized
Hilbert angular speed, not just of a newly defined scalar quantity. -/
theorem h3Path_physicalUnitVelocity_angularSpeed_cofinally_unbounded_of_noTrace244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖deriv (h3PathPhysicalUnitVelocity244 hH3) r‖ := by
  intro b hb M
  obtain ⟨r, hr, hHigh⟩ :=
    h3Path_physicalAngularGramRate_cofinally_unbounded_of_noTrace244
      hH3 hClass hL hNoTrace b hb M
  have hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hr.1), hr.2⟩
  have hE : 0 < velocityH3Energy0At u r :=
    h3Path_physicalKinetic_positive_of_positiveTerminal244 hH3 hClass hL
      r ⟨lt_trans hb.1 hr.1, hr.2⟩
  rw [h3Path_physicalSourceGram_sqrt_div_kinetic_eq_angularSpeed244
    hH3 r hrAbs hE] at hHigh
  exact ⟨r, hr, hHigh⟩

/-- On every positive-kinetic terminal energy class either the actual
physical L² velocity has its exact-mass strong trace or the normalized
physical angular speed exceeds every finite bound on every terminal subtail. -/
theorem h3Path_physicalL2Trace_or_cofinalUnboundedAngularSpeed244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T) :
    (∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U) ∧
        ‖U‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T) ∨
      (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
        ∃ r : ℝ, r ∈ Set.Ioo b T ∧
          M < ‖deriv (h3PathPhysicalUnitVelocity244 hH3) r‖) := by
  by_cases hTrace : ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)
  · obtain ⟨U, hU⟩ := hTrace
    exact Or.inl ⟨U, hU,
      h3Path_physicalVelocity_terminalTrace_norm_sq_eq_kineticLimit244
        hH3 hClass U hU⟩
  · exact Or.inr
      (h3Path_physicalUnitVelocity_angularSpeed_cofinally_unbounded_of_noTrace244
        hH3 hClass hL hTrace)

end
end PrimeTensor.FirstMonomialTriad
