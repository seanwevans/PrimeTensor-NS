import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceEscape244
import Mathlib.Tactic

/-!
# Fixed physical Laplacian or Leray escape from missing terminal L² trace

The physical projected momentum source R is the difference of the actual
physical spectral Laplacian A and the physical spectral Leray term B. The
previous checkpoint proved that missing physical L² terminal convergence,
with positive terminal kinetic mass, forces ‖R‖ to exceed every threshold
on every terminal subtail.

Triangle inequality and a finite two-channel cofinal pigeonhole now yield
a single fixed component (A or B) that is cofinally unbounded. In contrast,
an escape witness by itself only identifies one large component at that
time, without fixing which one it is.

Separate eventual bounds for both components imply an eventual bound for
R and hence the earlier conditional L² terminal trace. These are necessary
obstructions to failure of the physical L² trace, not unconditional H³
continuation estimates. No source component is asserted to be bounded.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The projected physical source is bounded by the sum of its actual
physical Laplacian and Leray component norms, at every time. -/
theorem h3Path_physicalProjectedSource_norm_le_Laplacian_add_Leray244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (r : ℝ) :
    ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
      ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r‖ +
        ‖h3AuditInitialActualSpectralLerayTotal hH3 r‖ := by
  change ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r -
    h3AuditInitialActualSpectralLerayTotal hH3 r‖ ≤ _
  exact norm_sub_le _ _

/-- Every large projected-source witness has a large physical Laplacian
or Leray component. This local dichotomy need not choose a fixed side. -/
theorem h3Path_physicalProjectedSource_large_component_at_time244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (r M : ℝ)
    (hLarge : M < ‖h3PathActualProjectedMomentumSource244 hH3 r‖) :
    M / 2 < ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r‖ ∨
      M / 2 < ‖h3AuditInitialActualSpectralLerayTotal hH3 r‖ := by
  have hTriangle :=
    h3Path_physicalProjectedSource_norm_le_Laplacian_add_Leray244 hH3 r
  by_contra hNeither
  push_neg at hNeither
  linarith only [hLarge, hTriangle, hNeither.1, hNeither.2]

/-- Abstract two-channel cofinal pigeonhole: an unbounded difference on
all terminal subtails requires a *fixed* component with the same property.
If neither component escapes, their individual tail ceilings intersect on
the later of their two cutoffs, contradicting the source escape. -/
theorem h3Path_physicalDifference_cofinalEscape_fixedComponent244
    {a T : ℝ}
    (A B : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (hEscape : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < ‖A r - B r‖) :
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < ‖A r‖) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < ‖B r‖) := by
  classical
  by_contra hNeither
  have hNoA : ¬ (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < ‖A r‖) := by
    intro hA
    exact hNeither (Or.inl hA)
  have hNoB : ¬ (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < ‖B r‖) := by
    intro hB
    exact hNeither (Or.inr hB)
  push_neg at hNoA hNoB
  obtain ⟨bA, hbA, CA, hBoundA⟩ := hNoA
  obtain ⟨bB, hbB, CB, hBoundB⟩ := hNoB
  let b : ℝ := max bA bB
  have hb : b ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hbA.1 (le_max_left bA bB), max_lt hbA.2 hbB.2⟩
  obtain ⟨r, hr, hHigh⟩ := hEscape b hb (CA + CB)
  have hrA : r ∈ Set.Ioo bA T :=
    ⟨lt_of_le_of_lt (le_max_left bA bB) hr.1, hr.2⟩
  have hrB : r ∈ Set.Ioo bB T :=
    ⟨lt_of_le_of_lt (le_max_right bA bB) hr.1, hr.2⟩
  have hTriangle : ‖A r - B r‖ ≤ ‖A r‖ + ‖B r‖ := norm_sub_le _ _
  have hCeil : ‖A r - B r‖ ≤ CA + CB :=
    hTriangle.trans (add_le_add (hBoundA r hrA) (hBoundB r hrB))
  exact (not_lt_of_ge hCeil) hHigh

/-- Under positive terminal kinetic mass, failure of a strong physical L²
velocity trace singles out a fixed PDE component: either actual physical
spectral Laplacian or actual physical spectral Leray source is cofinally
unbounded in the physical Hilbert norm. -/
theorem h3Path_physicalLaplacian_or_Leray_fixedCofinalEscape_of_noTrace244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)) :
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r‖) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3AuditInitialActualSpectralLerayTotal hH3 r‖) := by
  apply h3Path_physicalDifference_cofinalEscape_fixedComponent244
    (h3AuditInitialActualSpectralLaplacianTotal hH3)
    (h3AuditInitialActualSpectralLerayTotal hH3)
  exact h3Path_physicalLaplacianMinusLeray_cofinally_unbounded_of_noTrace244
    hH3 hClass hL hNoTrace

/-- Separate finite tail ceilings for the physical Laplacian and Leray
components, even with distinct cutoff times, yield a single eventual
projected-source ceiling and hence a physical terminal L² trace. -/
theorem h3Path_physicalL2Trace_of_Laplacian_and_Leray_tailCeilings244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (bA bB : ℝ) (hbA : bA ∈ Set.Ioo a T) (hbB : bB ∈ Set.Ioo a T)
    (CA CB : ℝ)
    (hBoundA : ∀ r : ℝ, r ∈ Set.Ioo bA T →
      ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r‖ ≤ CA)
    (hBoundB : ∀ r : ℝ, r ∈ Set.Ioo bB T →
      ‖h3AuditInitialActualSpectralLerayTotal hH3 r‖ ≤ CB) :
    ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U) ∧
        ‖U‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T := by
  let b : ℝ := max bA bB
  have hb : b ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hbA.1 (le_max_left bA bB), max_lt hbA.2 hbB.2⟩
  have hCeil : ∀ r : ℝ, r ∈ Set.Ioo b T →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ CA + CB := by
    intro r hr
    have hrA : r ∈ Set.Ioo bA T :=
      ⟨lt_of_le_of_lt (le_max_left bA bB) hr.1, hr.2⟩
    have hrB : r ∈ Set.Ioo bB T :=
      ⟨lt_of_le_of_lt (le_max_right bA bB) hr.1, hr.2⟩
    exact (h3Path_physicalProjectedSource_norm_le_Laplacian_add_Leray244
      hH3 r).trans (add_le_add (hBoundA r hrA) (hBoundB r hrB))
  obtain ⟨U, hU⟩ := h3Path_physicalL2Trace_of_projectedSource_ceiling244
    hH3 hClass hL b hb (CA + CB) hCeil
  exact ⟨U, hU,
    h3Path_physicalVelocity_terminalTrace_norm_sq_eq_kineticLimit244
      hH3 hClass U hU⟩

/-- A fixed Laplacian ceiling forces the physical Leray term to carry all
remaining cofinal source escape if no terminal physical L² trace exists. -/
theorem h3Path_physicalLeray_fixedEscape_of_Laplacian_ceiling_noTrace244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U))
    (bA : ℝ) (hbA : bA ∈ Set.Ioo a T) (CA : ℝ)
    (hBoundA : ∀ r : ℝ, r ∈ Set.Ioo bA T →
      ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r‖ ≤ CA) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3AuditInitialActualSpectralLerayTotal hH3 r‖ := by
  intro b hb M
  let c : ℝ := max b bA
  have hc : c ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hb.1 (le_max_left b bA), max_lt hb.2 hbA.2⟩
  obtain ⟨r, hr, hHigh⟩ :=
    h3Path_physicalLaplacianMinusLeray_cofinally_unbounded_of_noTrace244
      hH3 hClass hL hNoTrace c hc (M + CA)
  have hrB : r ∈ Set.Ioo b T :=
    ⟨lt_of_le_of_lt (le_max_left b bA) hr.1, hr.2⟩
  have hrA : r ∈ Set.Ioo bA T :=
    ⟨lt_of_le_of_lt (le_max_right b bA) hr.1, hr.2⟩
  have hTriangle :
      ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r -
        h3AuditInitialActualSpectralLerayTotal hH3 r‖ ≤
      ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r‖ +
        ‖h3AuditInitialActualSpectralLerayTotal hH3 r‖ := norm_sub_le _ _
  refine ⟨r, hrB, ?_⟩
  linarith only [hHigh, hTriangle, hBoundA r hrA]

/-- A fixed Leray ceiling instead forces the physical Laplacian term to
carry cofinal escape if the physical terminal L² trace fails. -/
theorem h3Path_physicalLaplacian_fixedEscape_of_Leray_ceiling_noTrace244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U))
    (bB : ℝ) (hbB : bB ∈ Set.Ioo a T) (CB : ℝ)
    (hBoundB : ∀ r : ℝ, r ∈ Set.Ioo bB T →
      ‖h3AuditInitialActualSpectralLerayTotal hH3 r‖ ≤ CB) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r‖ := by
  intro b hb M
  let c : ℝ := max b bB
  have hc : c ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hb.1 (le_max_left b bB), max_lt hb.2 hbB.2⟩
  obtain ⟨r, hr, hHigh⟩ :=
    h3Path_physicalLaplacianMinusLeray_cofinally_unbounded_of_noTrace244
      hH3 hClass hL hNoTrace c hc (M + CB)
  have hrA : r ∈ Set.Ioo b T :=
    ⟨lt_of_le_of_lt (le_max_left b bB) hr.1, hr.2⟩
  have hrB : r ∈ Set.Ioo bB T :=
    ⟨lt_of_le_of_lt (le_max_right b bB) hr.1, hr.2⟩
  have hTriangle :
      ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r -
        h3AuditInitialActualSpectralLerayTotal hH3 r‖ ≤
      ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r‖ +
        ‖h3AuditInitialActualSpectralLerayTotal hH3 r‖ := norm_sub_le _ _
  refine ⟨r, hrA, ?_⟩
  linarith only [hHigh, hTriangle, hBoundB r hrB]

/-- Positive kinetic mass yields an exact-mass terminal physical L² trace,
or one fixed physical spectral PDE source component is cofinally unbounded.
The alternative does not assert either escape branch unconditionally. -/
theorem h3Path_physicalL2Trace_or_fixedLaplacianLerayEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T) :
    (∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U) ∧
        ‖U‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T) ∨
    ((∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r‖) ∨
     (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3AuditInitialActualSpectralLerayTotal hH3 r‖)) := by
  by_cases hTrace : ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)
  · obtain ⟨U, hU⟩ := hTrace
    exact Or.inl ⟨U, hU,
      h3Path_physicalVelocity_terminalTrace_norm_sq_eq_kineticLimit244
        hH3 hClass U hU⟩
  · exact Or.inr
      (h3Path_physicalLaplacian_or_Leray_fixedCofinalEscape_of_noTrace244
        hH3 hClass hL hTrace)

end
end PrimeTensor.FirstMonomialTriad
