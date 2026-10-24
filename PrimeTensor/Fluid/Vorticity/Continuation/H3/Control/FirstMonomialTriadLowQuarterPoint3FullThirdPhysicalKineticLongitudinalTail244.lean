import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticTransverseSource244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Audit.OneComponentInitialDyadicKineticAverageRelativeEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Longitudinal physical source expenditure and transverse terminal obstruction

The exact kinetic/transverse orthogonal decomposition from the preceding
checkpoint separates the actual physical velocity derivative R into a scalar
kinetic-loss direction and a perpendicular forcing Q. On a tail with positive
terminal kinetic energy L, the longitudinal magnitude is bounded by D0/sqrt L.
The genuine kinetic energy budget then bounds its entire integral uniformly by
(E0(s)-L)/(2 sqrt L). No extra analytic bound on D0 or Q is assumed on
compact strictly positive intervals: both norm rates are continuous there.

Consequently the only remaining possible obstruction to a strong terminal L2
velocity trace within the positive-L case is nonvanishing transverse source
variation. This does NOT rule out transverse nonintegrability or H3 blowup.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Actual kinetic-loss component of the physical projected momentum source. -/
noncomputable def h3PathPhysicalLongitudinalSource244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) : H3PhysicalRealFinVectorL2Hilbert :=
  -((velocityH3Dissipation0At u t / velocityH3Energy0At u t) •
      h3AuditInitialOldPhysicalHilbertTotal hH3 t)

/-- Exact decomposition, as a Hilbert-space equality. The algebraic identity
is valid even at zero kinetic mass, though tangency requires positivity. -/
theorem h3Path_physicalSource_eq_longitudinal_add_transverse244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) :
    h3PathActualProjectedMomentumSource244 hH3 t =
      h3PathPhysicalLongitudinalSource244 hH3 t +
        h3PathPhysicalTransverseSource244 hH3 t := by
  unfold h3PathPhysicalLongitudinalSource244 h3PathPhysicalTransverseSource244
  abel

/-- Longitudinal source magnitude is exactly D0/sqrt(E0) when kinetic
energy is positive. -/
theorem h3Path_physicalLongitudinal_norm_eq_dissipation_div_sqrt244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u t) :
    ‖h3PathPhysicalLongitudinalSource244 hH3 t‖ =
      velocityH3Dissipation0At u t /
        Real.sqrt (velocityH3Energy0At u t) := by
  let E : ℝ := velocityH3Energy0At u t
  let D : ℝ := velocityH3Dissipation0At u t
  let U : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 t
  have hD : 0 ≤ D := velocityH3Dissipation0At_nonneg u t
  have hSqrt : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hNorm : ‖U‖ = Real.sqrt E :=
    h3Audit_initialOldPhysicalHilbert_norm_eq_sqrt_kineticEnergy hH3 t ht
  have hDivNonneg : 0 ≤ D / E := div_nonneg hD hE.le
  change ‖-((D / E) • U)‖ = D / Real.sqrt E
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hDivNonneg, hNorm]
  apply (eq_div_iff (ne_of_gt hSqrt)).2
  calc
    (D / E) * Real.sqrt E * Real.sqrt E = (D / E) * E := by
      rw [mul_assoc, Real.mul_self_sqrt hE.le]
    _ = D := div_mul_cancel₀ D (ne_of_gt hE)

/-- On a positive-terminal-kinetic tail, longitudinal physical source
magnitude is controlled pointwise by a constant times genuine D0. -/
theorem h3Path_physicalLongitudinal_norm_le_terminalDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) :
    ‖h3PathPhysicalLongitudinalSource244 hH3 t‖ ≤
      (1 / Real.sqrt (h3PathCanonicalTerminalKineticEnergyAt u a T)) *
        velocityH3Dissipation0At u t := by
  let L : ℝ := h3PathCanonicalTerminalKineticEnergyAt u a T
  let E : ℝ := velocityH3Energy0At u t
  let D : ℝ := velocityH3Dissipation0At u t
  have hE : 0 < E :=
    h3Path_physicalKinetic_positive_of_positiveTerminal244 hH3 hClass hL t ht
  have hLE : L ≤ E :=
    h3PathCanonical_terminalKineticEnergy_le_anchor (u := u) ht
  have hRootL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hRootE : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hRootLe : Real.sqrt L ≤ Real.sqrt E := Real.sqrt_le_sqrt hLE
  have hD : 0 ≤ D := velocityH3Dissipation0At_nonneg u t
  have hPoint : D / Real.sqrt E ≤ D / Real.sqrt L := by
    apply (div_le_div_iff₀ hRootE hRootL).2
    exact mul_le_mul_of_nonneg_left hRootLe hD
  calc
    ‖h3PathPhysicalLongitudinalSource244 hH3 t‖ =
        D / Real.sqrt E :=
      h3Path_physicalLongitudinal_norm_eq_dissipation_div_sqrt244
        hH3 t ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩ hE
    _ ≤ D / Real.sqrt L := hPoint
    _ = (1 / Real.sqrt L) * D := by ring

/-- Under L>0 both physical source channels are strongly continuous in time
on the whole strict H3 energy-class tail, not merely separately measurable. -/
theorem h3Path_physicalSourceChannels_continuousOn_positiveTerminal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T) :
    ContinuousOn (h3PathPhysicalLongitudinalSource244 hH3) (Set.Ioo a T) ∧
      ContinuousOn (h3PathPhysicalTransverseSource244 hH3) (Set.Ioo a T) := by
  have hSub : Set.Ioo a T ⊆ Set.Ioo (0 : ℝ) T := by
    intro r hr
    exact ⟨lt_trans hClass.terminal_start.1 hr.1, hr.2⟩
  have hECont : ContinuousOn (velocityH3Energy0At u) (Set.Ioo a T) :=
    (h3Audit_initialKineticEnergy_continuousOn_positiveInterval hH3).mono hSub
  have hDCont : ContinuousOn (velocityH3Dissipation0At u) (Set.Ioo a T) :=
    (h3Path_dissipation0_continuousOn_positiveTime244 hH3).mono hSub
  have hUCont : ContinuousOn (h3AuditInitialOldPhysicalHilbertTotal hH3)
      (Set.Ioo a T) :=
    (h3Audit_initialOldPhysicalHilbert_continuousOn hH3).mono hSub
  have hRCont : ContinuousOn (h3PathActualProjectedMomentumSource244 hH3)
      (Set.Ioo a T) := by
    have hR : ContinuousOn (h3PathActualProjectedMomentumSource244 hH3)
        (Set.Ioo (0 : ℝ) T) := by
      change ContinuousOn
        (fun r : ℝ =>
          h3AuditInitialActualSpectralLaplacianTotal hH3 r -
            h3AuditInitialActualSpectralLerayTotal hH3 r)
        (Set.Ioo (0 : ℝ) T)
      exact h3Audit_initialActualProjectedRHS_continuousOn_positiveTime hH3
    exact hR.mono hSub
  have hFraction : ContinuousOn
      (fun r : ℝ => velocityH3Dissipation0At u r / velocityH3Energy0At u r)
      (Set.Ioo a T) := by
    exact hDCont.div hECont (fun r hr =>
      ne_of_gt (h3Path_physicalKinetic_positive_of_positiveTerminal244
        hH3 hClass hL r hr))
  have hSmul : ContinuousOn
      (fun r : ℝ =>
        (velocityH3Dissipation0At u r / velocityH3Energy0At u r) •
          h3AuditInitialOldPhysicalHilbertTotal hH3 r)
      (Set.Ioo a T) := hFraction.smul hUCont
  constructor
  · change ContinuousOn
      (fun r : ℝ => -((velocityH3Dissipation0At u r / velocityH3Energy0At u r) •
        h3AuditInitialOldPhysicalHilbertTotal hH3 r)) (Set.Ioo a T)
    exact hSmul.neg
  · change ContinuousOn
      (fun r : ℝ => h3PathActualProjectedMomentumSource244 hH3 r +
        (velocityH3Dissipation0At u r / velocityH3Energy0At u r) •
          h3AuditInitialOldPhysicalHilbertTotal hH3 r) (Set.Ioo a T)
    exact hRCont.add hSmul

/-- Exact terminal source-norm domination. Only the transverse component is
not already paid for by the scalar kinetic-dissipation budget. -/
theorem h3Path_physicalSource_norm_le_transverse_add_dissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) :
    ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ≤
      ‖h3PathPhysicalTransverseSource244 hH3 t‖ +
        (1 / Real.sqrt (h3PathCanonicalTerminalKineticEnergyAt u a T)) *
          velocityH3Dissipation0At u t := by
  calc
    ‖h3PathActualProjectedMomentumSource244 hH3 t‖ =
        ‖h3PathPhysicalLongitudinalSource244 hH3 t +
          h3PathPhysicalTransverseSource244 hH3 t‖ := by
      rw [h3Path_physicalSource_eq_longitudinal_add_transverse244]
    _ ≤ ‖h3PathPhysicalLongitudinalSource244 hH3 t‖ +
          ‖h3PathPhysicalTransverseSource244 hH3 t‖ := norm_add_le _ _
    _ ≤ ‖h3PathPhysicalTransverseSource244 hH3 t‖ +
          (1 / Real.sqrt (h3PathCanonicalTerminalKineticEnergyAt u a T)) *
            velocityH3Dissipation0At u t := by
      have hBound := h3Path_physicalLongitudinal_norm_le_terminalDissipation244
        hH3 hClass hL t ht
      linarith only [hBound]

/-- No independent compact-time integrability assumption for Q is required.
The exact source decomposition and continuity deliver an integrated Hilbert
source-norm bound from the transverse action and terminal kinetic loss. -/
theorem h3Path_physicalSourceNorm_integral_le_transverse_and_remainingKinetic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (s t : ℝ) (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t) :
    (∫ r in s..t, ‖h3PathActualProjectedMomentumSource244 hH3 r‖) ≤
      (∫ r in s..t, ‖h3PathPhysicalTransverseSource244 hH3 r‖) +
        (velocityH3Energy0At u s -
          h3PathCanonicalTerminalKineticEnergyAt u a T) /
          (2 * Real.sqrt (h3PathCanonicalTerminalKineticEnergyAt u a T)) := by
  let L : ℝ := h3PathCanonicalTerminalKineticEnergyAt u a T
  let c : ℝ := 1 / Real.sqrt L
  have hSqrt : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hDen : 0 < 2 * Real.sqrt L := mul_pos (by norm_num) hSqrt
  have hSet : Set.Icc s t ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hChannels := h3Path_physicalSourceChannels_continuousOn_positiveTerminal244
    hH3 hClass hL
  have hRCont : ContinuousOn (h3PathActualProjectedMomentumSource244 hH3)
      (Set.Icc s t) := by
    have hFull : ContinuousOn (h3PathActualProjectedMomentumSource244 hH3)
        (Set.Ioo (0 : ℝ) T) := by
      change ContinuousOn
        (fun r : ℝ => h3AuditInitialActualSpectralLaplacianTotal hH3 r -
          h3AuditInitialActualSpectralLerayTotal hH3 r)
        (Set.Ioo (0 : ℝ) T)
      exact h3Audit_initialActualProjectedRHS_continuousOn_positiveTime hH3
    have hSub : Set.Icc s t ⊆ Set.Ioo (0 : ℝ) T := by
      intro r hr
      exact ⟨lt_trans hClass.terminal_start.1 (hSet hr).1, (hSet hr).2⟩
    exact hFull.mono hSub
  have hRInt : IntervalIntegrable
      (fun r : ℝ => ‖h3PathActualProjectedMomentumSource244 hH3 r‖) volume s t :=
    hRCont.norm.intervalIntegrable_of_Icc hst
  have hQInt : IntervalIntegrable
      (fun r : ℝ => ‖h3PathPhysicalTransverseSource244 hH3 r‖) volume s t :=
    (hChannels.2.mono hSet).norm.intervalIntegrable_of_Icc hst
  have hDInt : IntervalIntegrable (velocityH3Dissipation0At u) volume s t :=
    ((h3Path_dissipation0_continuousOn_positiveTime244 hH3).mono (by
      intro r hr
      have hr' := hSet hr
      exact ⟨lt_trans hClass.terminal_start.1 hr'.1, hr'.2⟩)).intervalIntegrable_of_Icc hst
  have hExtraInt : IntervalIntegrable (fun r : ℝ => c * velocityH3Dissipation0At u r)
      volume s t := hDInt.const_mul c
  have hComparison :
      (∫ r in s..t, ‖h3PathActualProjectedMomentumSource244 hH3 r‖) ≤
        (∫ r in s..t,
          ‖h3PathPhysicalTransverseSource244 hH3 r‖ +
            c * velocityH3Dissipation0At u r) := by
    apply intervalIntegral.integral_mono_on hst hRInt (hQInt.add hExtraInt)
    intro r hr
    change ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
      ‖h3PathPhysicalTransverseSource244 hH3 r‖ +
        (1 / Real.sqrt L) * velocityH3Dissipation0At u r
    exact h3Path_physicalSource_norm_le_transverse_add_dissipation244
      hH3 hClass hL r (hSet hr)
  have hSplit :
      (∫ r in s..t,
        ‖h3PathPhysicalTransverseSource244 hH3 r‖ +
          c * velocityH3Dissipation0At u r) =
        (∫ r in s..t, ‖h3PathPhysicalTransverseSource244 hH3 r‖) +
          c * (∫ r in s..t, velocityH3Dissipation0At u r) := by
    rw [intervalIntegral.integral_add hQInt hExtraInt,
      intervalIntegral.integral_const_mul]
  rw [hSplit] at hComparison
  have hBudget := h3Path_physicalDissipation0_tailBudget_le_remainingKinetic244
    hH3 hClass s t hs ht hst
  have hCost : c * (∫ r in s..t, velocityH3Dissipation0At u r) ≤
      (velocityH3Energy0At u s - L) / (2 * Real.sqrt L) := by
    change (1 / Real.sqrt L) * (∫ r in s..t, velocityH3Dissipation0At u r) ≤
      (velocityH3Energy0At u s - L) / (2 * Real.sqrt L)
    calc
      (1 / Real.sqrt L) * (∫ r in s..t, velocityH3Dissipation0At u r) =
          (1 / (2 * Real.sqrt L)) *
            (2 * (∫ r in s..t, velocityH3Dissipation0At u r)) := by
        field_simp [ne_of_gt hSqrt] <;> ring
      _ ≤ (1 / (2 * Real.sqrt L)) * (velocityH3Energy0At u s - L) :=
        mul_le_mul_of_nonneg_left hBudget (by positivity)
      _ = (velocityH3Energy0At u s - L) / (2 * Real.sqrt L) := by
        ring
  exact hComparison.trans (add_le_add_right hCost _)

/-- Bochner FTC converts the integrated transverse/kinetic source budget into
an actual physical Hilbert velocity displacement estimate. -/
theorem h3Path_physicalHilbert_increment_le_transverse_and_remainingKinetic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (s t : ℝ) (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T)
    (hst : s ≤ t) :
    ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
        h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ ≤
      (∫ r in s..t, ‖h3PathPhysicalTransverseSource244 hH3 r‖) +
        (velocityH3Energy0At u s -
          h3PathCanonicalTerminalKineticEnergyAt u a T) /
          (2 * Real.sqrt (h3PathCanonicalTerminalKineticEnergyAt u a T)) := by
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hs.1, hs.2⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hFTC := h3Path_physicalHilbertFTC_betweenPositiveTimes244 hH3 s t hsAbs htAbs
  have hNorm :
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 t -
          h3AuditInitialOldPhysicalHilbertTotal hH3 s‖ ≤
        (∫ r in s..t, ‖h3PathActualProjectedMomentumSource244 hH3 r‖) := by
    rw [hFTC]
    exact intervalIntegral.norm_integral_le_integral_norm hst
  exact hNorm.trans
    (h3Path_physicalSourceNorm_integral_le_transverse_and_remainingKinetic244
      hH3 hClass hL s t hs ht hst)

end
end PrimeTensor.FirstMonomialTriad
