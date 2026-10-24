import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedComponentEscape244
import Mathlib.Tactic

/-!
# Physical projected-source escape transfers to actual H³ energy escape

The previous checkpoint proves that missing a strong terminal physical L²
trace (on a positive-kinetic-mass energy class) forces a fixed physical source
component, diffusion or Leray, to be unbounded on every terminal subtail.

Here we use the previously proven *actual inverse-Fourier* source bounds:

  ‖physical Laplacian‖ <= 3 E₃,
  ‖physical Leray‖ <= C_L E₃,
  ‖projected momentum source‖ <= (3+C_L) E₃.

The bounds are applied at genuinely positive times and need no extra
physical-source identification assumptions. An abstract nonnegative-majorant
lemma transfers cofinal norm escape into cofinal energy escape without
requiring strictly positive coefficients. We preserve the fixed-component
obstruction while recording the scalar consequence:

  no strong physical L² endpoint trace and L>0 ->
    ∀ b in (a,T), ∀ M, ∃ t in (b,T), M < E₃(t).

Conversely a bounded H³ energy on any terminal subtail gives a strong
physical L² trace (not smooth H³ continuation). No implication from H³
nonextension to failure of L² trace is asserted here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Cofinal norm escape propagates backward through any nonnegative
pointwise scalar majorant, even when the coefficient is zero. -/
theorem h3Path_cofinalNormEscape_forces_scalarMajorantEscape244
    {a T : ℝ}
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (E : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ r : ℝ, r ∈ Set.Ioo a T → ‖F r‖ ≤ K * E r)
    (hEscape : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < ‖F r‖) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < E r := by
  intro b hb M
  obtain ⟨r, hr, hHigh⟩ := hEscape b hb (K * M)
  have hrTail : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hr.1, hr.2⟩
  refine ⟨r, hr, ?_⟩
  by_contra hNot
  have hE : E r ≤ M := le_of_not_gt hNot
  have hCeil : ‖F r‖ ≤ K * M :=
    (hBound r hrTail).trans (mul_le_mul_of_nonneg_left hE hK)
  exact (not_lt_of_ge hCeil) hHigh

/-- On each strictly positive physical time, the reconstructed actual
Laplacian is dominated by three times the normalized H³ energy. -/
theorem h3Path_physicalLaplacian_norm_le_H3Energy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r‖ ≤
      3 * velocityH3EnergyAt u r := by
  let b : ℝ := (r + T) / 2
  have hb : r < b ∧ b < T := by
    dsimp only [b]
    constructor <;> linarith only [hr.2]
  have hrIcc : r ∈ Set.Icc (0 : ℝ) b := ⟨hr.1.le, hb.1.le⟩
  exact h3Audit_initialActualSpectralLaplacian_norm_le_energy
    hH3 b hb.2 r hrIcc

/-- The actual physical Leray source is dominated by its explicitly
calibrated quadratic Fourier coefficient times normalized H³ energy. -/
theorem h3Path_physicalLeray_norm_le_H3Energy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3AuditInitialActualSpectralLerayTotal hH3 r‖ ≤
      h3AuditInitialLerayEnergyCoefficient * velocityH3EnergyAt u r := by
  let b : ℝ := (r + T) / 2
  have hb : r < b ∧ b < T := by
    dsimp only [b]
    constructor <;> linarith only [hr.2]
  have hrIcc : r ∈ Set.Icc (0 : ℝ) b := ⟨hr.1.le, hb.1.le⟩
  exact h3Audit_initialActualSpectralLeray_norm_le_energy
    hH3 b hb.2 r hrIcc

/-- The exact physical projected source is pointwise bounded by the
previously verified sum of its two inverse-Fourier H³ majorants. -/
theorem h3Path_physicalProjectedSource_norm_le_H3Energy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
      (3 + h3AuditInitialLerayEnergyCoefficient) *
        velocityH3EnergyAt u r := by
  have hD := h3Path_physicalLaplacian_norm_le_H3Energy244 hH3 r hr
  have hN := h3Path_physicalLeray_norm_le_H3Energy244 hH3 r hr
  calc
    ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
        ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r‖ +
          ‖h3AuditInitialActualSpectralLerayTotal hH3 r‖ :=
      h3Path_physicalProjectedSource_norm_le_Laplacian_add_Leray244 hH3 r
    _ ≤ 3 * velocityH3EnergyAt u r +
        h3AuditInitialLerayEnergyCoefficient * velocityH3EnergyAt u r :=
      add_le_add hD hN
    _ = (3 + h3AuditInitialLerayEnergyCoefficient) *
        velocityH3EnergyAt u r := by ring

/-- A fixed cofinally escaping physical Laplacian component forces
normalized actual H³ energy to escape cofinally on the same class. -/
theorem h3Path_physicalLaplacian_cofinalEscape_forces_H3Energy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEscape : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r‖) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < velocityH3EnergyAt u r := by
  apply h3Path_cofinalNormEscape_forces_scalarMajorantEscape244
    (h3AuditInitialActualSpectralLaplacianTotal hH3)
    (velocityH3EnergyAt u) 3 (by norm_num)
  · intro r hr
    exact h3Path_physicalLaplacian_norm_le_H3Energy244 hH3 r
      ⟨lt_trans hClass.terminal_start.1 hr.1, hr.2⟩
  · exact hEscape

/-- Cofinal physical Leray-source norm escape likewise forces the actual
H³ energy to escape; only nonnegativity of the Leray coefficient is used. -/
theorem h3Path_physicalLeray_cofinalEscape_forces_H3Energy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEscape : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3AuditInitialActualSpectralLerayTotal hH3 r‖) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < velocityH3EnergyAt u r := by
  apply h3Path_cofinalNormEscape_forces_scalarMajorantEscape244
    (h3AuditInitialActualSpectralLerayTotal hH3)
    (velocityH3EnergyAt u) h3AuditInitialLerayEnergyCoefficient
    h3AuditInitialLerayEnergyCoefficient_nonneg
  · intro r hr
    exact h3Path_physicalLeray_norm_le_H3Energy244 hH3 r
      ⟨lt_trans hClass.terminal_start.1 hr.1, hr.2⟩
  · exact hEscape

/-- The already-proved full projected PDE source escape also implies
cofinal H³ energy escape without first selecting a fixed PDE component. -/
theorem h3Path_physicalProjectedSource_cofinalEscape_forces_H3Energy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEscape : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3PathActualProjectedMomentumSource244 hH3 r‖) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < velocityH3EnergyAt u r := by
  apply h3Path_cofinalNormEscape_forces_scalarMajorantEscape244
    (h3PathActualProjectedMomentumSource244 hH3)
    (velocityH3EnergyAt u) (3 + h3AuditInitialLerayEnergyCoefficient)
    (by have h := h3AuditInitialLerayEnergyCoefficient_nonneg; linarith)
  · intro r hr
    exact h3Path_physicalProjectedSource_norm_le_H3Energy244 hH3 r
      ⟨lt_trans hClass.terminal_start.1 hr.1, hr.2⟩
  · exact hEscape

/-- Failure of a strong terminal physical L² trace and positive terminal
kinetic mass forces the actual physical normalized H³ energy above every
finite threshold on every terminal subtail. Both fixed source branches from
the previous checkpoint transfer to the same scalar conclusion. -/
theorem h3Path_physicalH3Energy_cofinally_unbounded_of_noL2Trace244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < velocityH3EnergyAt u r := by
  rcases h3Path_physicalLaplacian_or_Leray_fixedCofinalEscape_of_noTrace244
      hH3 hClass hL hNoTrace with hLap | hLeray
  · exact h3Path_physicalLaplacian_cofinalEscape_forces_H3Energy244
      hH3 hClass hLap
  · exact h3Path_physicalLeray_cofinalEscape_forces_H3Energy244
      hH3 hClass hLeray

/-- A single terminal normalized-H³-energy ceiling gives a bounded
physical projected source, and hence a strong exact-mass physical L² trace. -/
theorem h3Path_physicalL2Trace_of_terminalH3EnergyCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (C : ℝ)
    (hCeil : ∀ r : ℝ, r ∈ Set.Ioo b T →
      velocityH3EnergyAt u r ≤ C) :
    ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U) ∧
        ‖U‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T := by
  have hCoeff : 0 ≤ 3 + h3AuditInitialLerayEnergyCoefficient := by
    have hNonneg := h3AuditInitialLerayEnergyCoefficient_nonneg
    linarith only [hNonneg]
  have hSourceCeil : ∀ r : ℝ, r ∈ Set.Ioo b T →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
        (3 + h3AuditInitialLerayEnergyCoefficient) * C := by
    intro r hr
    have hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hr.1), hr.2⟩
    exact (h3Path_physicalProjectedSource_norm_le_H3Energy244
      hH3 r hrAbs).trans
        (mul_le_mul_of_nonneg_left (hCeil r hr) hCoeff)
  obtain ⟨U, hU⟩ := h3Path_physicalL2Trace_of_projectedSource_ceiling244
    hH3 hClass hL b hb
      ((3 + h3AuditInitialLerayEnergyCoefficient) * C) hSourceCeil
  exact ⟨U, hU,
    h3Path_physicalVelocity_terminalTrace_norm_sq_eq_kineticLimit244
      hH3 hClass U hU⟩

/-- A positive-kinetic energy-class endpoint either has an exact-mass
physical strong L² trace, or its actual normalized H³ energy is cofinally
unbounded. The second alternative is not asserted from H³ nonextension. -/
theorem h3Path_physicalL2Trace_or_H3EnergyCofinalEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T) :
    (∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U) ∧
        ‖U‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T) ∨
      (∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
        ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < velocityH3EnergyAt u r) := by
  by_cases hTrace : ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)
  · obtain ⟨U, hU⟩ := hTrace
    exact Or.inl ⟨U, hU,
      h3Path_physicalVelocity_terminalTrace_norm_sq_eq_kineticLimit244
        hH3 hClass U hU⟩
  · exact Or.inr
      (h3Path_physicalH3Energy_cofinally_unbounded_of_noL2Trace244
        hH3 hClass hL hTrace)

/-- The same exact-mass terminal L² trace versus cofinal H³-energy escape
alternative holds for all nonnegative terminal kinetic limits. If L=0, the
strong physical L² trace exists without any angular-source hypothesis. -/
theorem h3Path_physicalL2Trace_or_H3EnergyCofinalEscape_allKinetic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U) ∧
        ‖U‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T) ∨
      (0 < h3PathCanonicalTerminalKineticEnergyAt u a T ∧
        ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
          ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < velocityH3EnergyAt u r) := by
  let L : ℝ := h3PathCanonicalTerminalKineticEnergyAt u a T
  by_cases hZero : L = 0
  · left
    refine ⟨0, h3Path_physicalVelocity_tendsto_zero_of_zeroTerminalKinetic244
      hH3 hClass hZero, ?_⟩
    simpa using hZero.symm
  · have hNonneg : 0 ≤ L :=
      h3PathCanonical_terminalKineticEnergy_nonneg hClass
    have hL : 0 < L := lt_of_le_of_ne hNonneg (Ne.symm hZero)
    rcases h3Path_physicalL2Trace_or_H3EnergyCofinalEscape244
        hH3 hClass hL with hTrace | hEscape
    · exact Or.inl hTrace
    · exact Or.inr ⟨hL, hEscape⟩

end
end PrimeTensor.FirstMonomialTriad
