import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticAngularPointwiseEscape244
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Terminal physical angular escape forces projected PDE source escape

Let U be the actual physical L² velocity, R the projected Hilbert momentum
source, Q its kinetic-orthogonal transverse component, E = ‖U‖², and
L > 0 the canonical terminal kinetic mass. The previously proved exact
orthogonal decomposition gives ‖Q‖ ≤ ‖R‖. The exact unit direction derivative
N' = Q / sqrt(E), together with E ≥ L, yields

  sqrt(L) * ‖N'‖ ≤ ‖Q‖ ≤ ‖R‖.

Consequently, if the physical L² velocity has no strong terminal trace,
the prior cofinal unboundedness of angular speed forces cofinal unboundedness
of both Q and the *actual* projected PDE Hilbert source

  R = (physical spectral Laplacian) - (physical spectral Leray term).

A bound for this physical source on even one terminal subtail is therefore
a sufficient condition for a strong physical L² terminal trace. This is
not a bound obtained from the Navier--Stokes H³ energy estimates, and
H³ nonextension alone does not imply the assumed failure of the L² trace.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Orthogonality makes the transverse projected source no larger than the
actual projected physical momentum source at each strictly positive time. -/
theorem h3Path_physicalTransverse_norm_le_projectedSource244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) T)
    (hE : 0 < velocityH3Energy0At u r) :
    ‖h3PathPhysicalTransverseSource244 hH3 r‖ ≤
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ := by
  let E : ℝ := velocityH3Energy0At u r
  let D : ℝ := velocityH3Dissipation0At u r
  let Q : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathPhysicalTransverseSource244 hH3 r
  let R : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathActualProjectedMomentumSource244 hH3 r
  have hIdentity : ‖R‖ ^ 2 = ‖Q‖ ^ 2 + D ^ 2 / E :=
    h3Path_physicalSource_norm_sq_eq_transverse_add_kineticCost244
      hH3 r hr hE
  have hCost : 0 ≤ D ^ 2 / E := div_nonneg (sq_nonneg D) hE.le
  have hSq : ‖Q‖ ^ 2 ≤ ‖R‖ ^ 2 := by
    linarith only [hIdentity, hCost]
  exact (sq_le_sq₀ (norm_nonneg Q) (norm_nonneg R)).1 hSq

/-- The canonical terminal kinetic floor turns angular speed into a
quantitative lower bound on transverse physical forcing. -/
theorem h3Path_physicalAngularSpeed_mul_terminalSqrt_le_transverse244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (r : ℝ) (hr : r ∈ Set.Ioo a T) :
    Real.sqrt (h3PathCanonicalTerminalKineticEnergyAt u a T) *
        ‖deriv (h3PathPhysicalUnitVelocity244 hH3) r‖ ≤
      ‖h3PathPhysicalTransverseSource244 hH3 r‖ := by
  let L : ℝ := h3PathCanonicalTerminalKineticEnergyAt u a T
  let E : ℝ := velocityH3Energy0At u r
  let Q : H3PhysicalRealFinVectorL2Hilbert :=
    h3PathPhysicalTransverseSource244 hH3 r
  have hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hr.1, hr.2⟩
  have hE : 0 < E :=
    h3Path_physicalKinetic_positive_of_positiveTerminal244 hH3 hClass hL r hr
  have hLE : L ≤ E := h3PathCanonical_terminalKineticEnergy_le_anchor (u := u) hr
  have hRootE : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hRootLe : Real.sqrt L ≤ Real.sqrt E := Real.sqrt_le_sqrt hLE
  have hAngular :
      ‖deriv (h3PathPhysicalUnitVelocity244 hH3) r‖ =
        ‖Q‖ / Real.sqrt E := by
    rw [(h3Path_physicalUnitVelocity_hasDerivAt_angular244
      hH3 r hrAbs hE).deriv]
    exact h3Path_physicalAngularRate_norm_eq_transverse_div_sqrt244 hH3 r hE
  calc
    Real.sqrt L * ‖deriv (h3PathPhysicalUnitVelocity244 hH3) r‖ =
        Real.sqrt L * (‖Q‖ / Real.sqrt E) := by rw [hAngular]
    _ ≤ Real.sqrt E * (‖Q‖ / Real.sqrt E) :=
      mul_le_mul_of_nonneg_right hRootLe
        (div_nonneg (norm_nonneg Q) hRootE.le)
    _ = ‖Q‖ := by
      calc
        Real.sqrt E * (‖Q‖ / Real.sqrt E) =
            (‖Q‖ / Real.sqrt E) * Real.sqrt E := mul_comm _ _
        _ = ‖Q‖ := div_mul_cancel₀ _ (ne_of_gt hRootE)

/-- The same kinetic floor and Pythagorean source decomposition control
the normalized angular speed by the genuine PDE source norm. -/
theorem h3Path_physicalAngularSpeed_mul_terminalSqrt_le_projectedSource244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (r : ℝ) (hr : r ∈ Set.Ioo a T) :
    Real.sqrt (h3PathCanonicalTerminalKineticEnergyAt u a T) *
        ‖deriv (h3PathPhysicalUnitVelocity244 hH3) r‖ ≤
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ := by
  have hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hr.1, hr.2⟩
  have hE : 0 < velocityH3Energy0At u r :=
    h3Path_physicalKinetic_positive_of_positiveTerminal244
      hH3 hClass hL r hr
  exact (h3Path_physicalAngularSpeed_mul_terminalSqrt_le_transverse244
    hH3 hClass hL r hr).trans
      (h3Path_physicalTransverse_norm_le_projectedSource244 hH3 r hrAbs hE)

/-- Failure of the strong physical terminal L² trace forces the *transverse*
physical momentum-source norm above every finite threshold on each subtail. -/
theorem h3Path_physicalTransverseSource_cofinally_unbounded_of_noTrace244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3PathPhysicalTransverseSource244 hH3 r‖ := by
  intro b hb M
  have hRoot : 0 < Real.sqrt (h3PathCanonicalTerminalKineticEnergyAt u a T) :=
    Real.sqrt_pos.2 hL
  obtain ⟨r, hr, hHigh⟩ :=
    h3Path_physicalUnitVelocity_angularSpeed_cofinally_unbounded_of_noTrace244
      hH3 hClass hL hNoTrace b hb
        (M / Real.sqrt (h3PathCanonicalTerminalKineticEnergyAt u a T))
  have hrTail : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hr.1, hr.2⟩
  have hScaled :
      M < Real.sqrt (h3PathCanonicalTerminalKineticEnergyAt u a T) *
        ‖deriv (h3PathPhysicalUnitVelocity244 hH3) r‖ := by
    calc
      M < ‖deriv (h3PathPhysicalUnitVelocity244 hH3) r‖ *
          Real.sqrt (h3PathCanonicalTerminalKineticEnergyAt u a T) :=
        (div_lt_iff₀ hRoot).mp hHigh
      _ = Real.sqrt (h3PathCanonicalTerminalKineticEnergyAt u a T) *
          ‖deriv (h3PathPhysicalUnitVelocity244 hH3) r‖ := mul_comm _ _
  exact ⟨r, hr, hScaled.trans_le
    (h3Path_physicalAngularSpeed_mul_terminalSqrt_le_transverse244
      hH3 hClass hL r hrTail)⟩

/-- The actual projected physical L² momentum-source norm must be cofinally
unbounded if the physical velocity has no terminal strong L² limit. -/
theorem h3Path_physicalProjectedSource_cofinally_unbounded_of_noTrace244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3PathActualProjectedMomentumSource244 hH3 r‖ := by
  intro b hb M
  obtain ⟨r, hr, hHigh⟩ :=
    h3Path_physicalTransverseSource_cofinally_unbounded_of_noTrace244
      hH3 hClass hL hNoTrace b hb M
  have hrTail : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hr.1, hr.2⟩
  have hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hrTail.1, hrTail.2⟩
  have hE : 0 < velocityH3Energy0At u r :=
    h3Path_physicalKinetic_positive_of_positiveTerminal244
      hH3 hClass hL r hrTail
  exact ⟨r, hr, hHigh.trans_le
    (h3Path_physicalTransverse_norm_le_projectedSource244 hH3 r hrAbs hE)⟩

/-- The abstract actual projected source is precisely the physical spectral
Laplacian minus the physical spectral Leray forcing. Its Hilbert L² norm
therefore escapes cofinally if the physical terminal L² trace fails. -/
theorem h3Path_physicalLaplacianMinusLeray_cofinally_unbounded_of_noTrace244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r -
          h3AuditInitialActualSpectralLerayTotal hH3 r‖ := by
  intro b hb M
  obtain ⟨r, hr, hHigh⟩ :=
    h3Path_physicalProjectedSource_cofinally_unbounded_of_noTrace244
      hH3 hClass hL hNoTrace b hb M
  refine ⟨r, hr, ?_⟩
  change M < ‖h3PathActualProjectedMomentumSource244 hH3 r‖
  exact hHigh

/-- A pointwise bound on the genuine projected PDE source on any one
terminal subtail is sufficient for a strong physical L² endpoint trace. -/
theorem h3Path_physicalL2Trace_of_projectedSource_ceiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (C : ℝ)
    (hCeil : ∀ r : ℝ, r ∈ Set.Ioo b T →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C) :
    ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U) := by
  classical
  by_contra hNoTrace
  obtain ⟨r, hr, hHigh⟩ :=
    h3Path_physicalProjectedSource_cofinally_unbounded_of_noTrace244
      hH3 hClass hL hNoTrace b hb C
  exact (not_lt_of_ge (hCeil r hr)) hHigh

/-- Either the physical velocity has an exact-mass strong terminal L² trace
or its actual projected Laplacian-minus-Leray source is cofinally unbounded. -/
theorem h3Path_physicalL2Trace_or_cofinalProjectedPDEsourceEscape244
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
          M < ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r -
            h3AuditInitialActualSpectralLerayTotal hH3 r‖) := by
  by_cases hTrace : ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)
  · obtain ⟨U, hU⟩ := hTrace
    exact Or.inl ⟨U, hU,
      h3Path_physicalVelocity_terminalTrace_norm_sq_eq_kineticLimit244
        hH3 hClass U hU⟩
  · exact Or.inr
      (h3Path_physicalLaplacianMinusLeray_cofinally_unbounded_of_noTrace244
        hH3 hClass hL hTrace)

end
end PrimeTensor.FirstMonomialTriad
