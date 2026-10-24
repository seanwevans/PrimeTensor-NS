import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceH3EnergyEscape244
import Mathlib.Tactic

/-!
# Terminal projected-source escape in the actual weighted H³ spectral state

The committed physical momentum-source alternative identifies cofinal escape
of the physical spectral Laplacian or Leray forcing whenever the physical
velocity has no strong L² terminal trace and the terminal kinetic mass is
positive. The source constructors are inverse-Fourier transforms of the
*actual* weighted H³ spectral velocity state, rather than abstract PDE data.

This module retains the linear/quadratic distinction from the raw Fourier
estimates:
  ‖A(t)‖ ≤ 3 ‖S(t)‖,
  ‖B(t)‖ ≤ C_L ‖S(t)‖²,
  ‖A(t)-B(t)‖ ≤ 3 ‖S(t)‖ + C_L ‖S(t)‖².

Therefore either fixed physical source escape branch, and in fact escape of
the projected source alone, forces cofinal unboundedness of ‖S(t)‖.
Conversely any finite tail ceiling for ‖S(t)‖ yields a finite tail ceiling
for the projected momentum source and hence an exact-mass strong L² trace.

No equivalence between H³ energy and weighted spectral norm is assumed;
only the actual spectral reconstruction and established Fourier bounds are
used. No implication from H³ nonextension to failure of L² trace is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Physical inverse-Fourier Laplacian is linear in the actual weighted
spectral velocity norm on strictly positive times. -/
theorem h3Path_physicalLaplacian_norm_le_actualSpectralState244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r‖ ≤
      3 * ‖h3AuditActualSpectralVelocityTotal hH3 r‖ := by
  simpa only [h3AuditInitialActualSpectralLaplacianTotal, dite_eq_left hr]
    using h3AuditSpectralPhysicalLaplacian_norm_le
      (h3AuditActualSpectralVelocityTotal hH3 r)

/-- The physical inverse-Fourier Leray forcing retains its *quadratic*
weighted-spectral-state norm bound, with the previously proved constant. -/
theorem h3Path_physicalLeray_norm_le_actualSpectralState_sq244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3AuditInitialActualSpectralLerayTotal hH3 r‖ ≤
      h3AuditInitialLerayEnergyCoefficient *
        ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2 := by
  have hRaw := h3AuditSpectralPhysicalLerayForcing_norm_le
    (h3AuditActualSpectralVelocityTotal hH3 r)
  simpa only [h3AuditInitialActualSpectralLerayTotal, dite_eq_left hr,
    pow_two] using hRaw

/-- The projected source grows at most linearly plus quadratically in
actual weighted H³ spectral velocity, before replacing that norm by E₃. -/
theorem h3Path_physicalProjectedSource_norm_le_actualSpectralGrowth244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) T) :
    ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
      3 * ‖h3AuditActualSpectralVelocityTotal hH3 r‖ +
        h3AuditInitialLerayEnergyCoefficient *
          ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2 := by
  calc
    ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
        ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r‖ +
          ‖h3AuditInitialActualSpectralLerayTotal hH3 r‖ :=
      h3Path_physicalProjectedSource_norm_le_Laplacian_add_Leray244 hH3 r
    _ ≤ 3 * ‖h3AuditActualSpectralVelocityTotal hH3 r‖ +
        h3AuditInitialLerayEnergyCoefficient *
          ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2 :=
      add_le_add
        (h3Path_physicalLaplacian_norm_le_actualSpectralState244 hH3 r hr)
        (h3Path_physicalLeray_norm_le_actualSpectralState_sq244 hH3 r hr)

/-- Generic linear majorant principle: cofinal unbounded physical source
norm cannot be carried by a bounded weighted spectral velocity norm. -/
theorem h3Path_cofinalNormEscape_forces_spectralNorm_linear244
    {a T : ℝ}
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (S : ℝ → H3SpectralVelocityState)
    (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ r : ℝ, r ∈ Set.Ioo a T → ‖F r‖ ≤ K * ‖S r‖)
    (hEscape : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < ‖F r‖) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < ‖S r‖ := by
  intro b hb M
  obtain ⟨r, hr, hHigh⟩ := hEscape b hb (K * M)
  have hrTail : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hr.1, hr.2⟩
  refine ⟨r, hr, ?_⟩
  by_contra hNot
  have hS : ‖S r‖ ≤ M := le_of_not_gt hNot
  have hCeil : ‖F r‖ ≤ K * M :=
    (hBound r hrTail).trans (mul_le_mul_of_nonneg_left hS hK)
  exact (not_lt_of_ge hCeil) hHigh

/-- Quadratic analogue of the cofinal majorant principle. The threshold
max(M,0) handles arbitrary real M without imposing positivity hypotheses. -/
theorem h3Path_cofinalNormEscape_forces_spectralNorm_quadratic244
    {a T : ℝ}
    (F : ℝ → H3PhysicalRealFinVectorL2Hilbert)
    (S : ℝ → H3SpectralVelocityState)
    (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ r : ℝ, r ∈ Set.Ioo a T → ‖F r‖ ≤ K * ‖S r‖ ^ 2)
    (hEscape : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < ‖F r‖) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < ‖S r‖ := by
  intro b hb M
  let C : ℝ := max M 0
  have hC : 0 ≤ C := le_max_right M 0
  obtain ⟨r, hr, hHigh⟩ := hEscape b hb (K * C ^ 2)
  have hrTail : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hr.1, hr.2⟩
  refine ⟨r, hr, ?_⟩
  by_contra hNot
  have hS : ‖S r‖ ≤ C :=
    (le_of_not_gt hNot).trans (le_max_left M 0)
  have hSq : ‖S r‖ ^ 2 ≤ C ^ 2 :=
    (sq_le_sq₀ (norm_nonneg (S r)) hC).2 hS
  have hCeil : ‖F r‖ ≤ K * C ^ 2 :=
    (hBound r hrTail).trans (mul_le_mul_of_nonneg_left hSq hK)
  exact (not_lt_of_ge hCeil) hHigh

/-- Fixed physical Laplacian escape transfers to cofinal unboundedness of
the *actual* weighted H³ spectral-state norm. -/
theorem h3Path_physicalLaplacian_cofinalEscape_forces_spectralState244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEscape : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3AuditInitialActualSpectralLaplacianTotal hH3 r‖) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3AuditActualSpectralVelocityTotal hH3 r‖ := by
  apply h3Path_cofinalNormEscape_forces_spectralNorm_linear244
    (h3AuditInitialActualSpectralLaplacianTotal hH3)
    (h3AuditActualSpectralVelocityTotal hH3) 3 (by norm_num)
  · intro r hr
    exact h3Path_physicalLaplacian_norm_le_actualSpectralState244 hH3 r
      ⟨lt_trans hClass.terminal_start.1 hr.1, hr.2⟩
  · exact hEscape

/-- Fixed physical nonlinear Leray escape transfers to cofinal actual
spectral-state norm escape through the quadratic Fourier estimate. -/
theorem h3Path_physicalLeray_cofinalEscape_forces_spectralState244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEscape : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3AuditInitialActualSpectralLerayTotal hH3 r‖) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3AuditActualSpectralVelocityTotal hH3 r‖ := by
  apply h3Path_cofinalNormEscape_forces_spectralNorm_quadratic244
    (h3AuditInitialActualSpectralLerayTotal hH3)
    (h3AuditActualSpectralVelocityTotal hH3)
    h3AuditInitialLerayEnergyCoefficient
    h3AuditInitialLerayEnergyCoefficient_nonneg
  · intro r hr
    exact h3Path_physicalLeray_norm_le_actualSpectralState_sq244 hH3 r
      ⟨lt_trans hClass.terminal_start.1 hr.1, hr.2⟩
  · exact hEscape

/-- Even without selecting a fixed source component, cofinal escape of the
full projected momentum source forces actual weighted spectral-state escape. -/
theorem h3Path_physicalProjectedSource_cofinalEscape_forces_spectralState244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hEscape : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3PathActualProjectedMomentumSource244 hH3 r‖) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3AuditActualSpectralVelocityTotal hH3 r‖ := by
  intro b hb M
  let C : ℝ := max M 0
  have hC : 0 ≤ C := le_max_right M 0
  let K : ℝ := h3AuditInitialLerayEnergyCoefficient
  have hK : 0 ≤ K := h3AuditInitialLerayEnergyCoefficient_nonneg
  obtain ⟨r, hr, hHigh⟩ := hEscape b hb (3 * C + K * C ^ 2)
  have hrTail : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hr.1, hr.2⟩
  refine ⟨r, hr, ?_⟩
  by_contra hNot
  have hS : ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ≤ C :=
    (le_of_not_gt hNot).trans (le_max_left M 0)
  have hSq : ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2 ≤ C ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hC).2 hS
  have hCeil : ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
      3 * C + K * C ^ 2 := by
    calc
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
          3 * ‖h3AuditActualSpectralVelocityTotal hH3 r‖ +
            K * ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2 :=
        h3Path_physicalProjectedSource_norm_le_actualSpectralGrowth244
          hH3 r ⟨lt_trans hClass.terminal_start.1 hrTail.1, hrTail.2⟩
      _ ≤ 3 * C + K * C ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hS (by norm_num))
          (mul_le_mul_of_nonneg_left hSq hK)
  exact (not_lt_of_ge hCeil) hHigh

/-- Failure of a strong terminal physical L² trace forces the actual
weighted H³ spectral velocity norm above every threshold on each subtail.
Both fixed-component branches are retained in the proof. -/
theorem h3Path_physicalSpectralState_cofinally_unbounded_of_noL2Trace244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3AuditActualSpectralVelocityTotal hH3 r‖ := by
  rcases h3Path_physicalLaplacian_or_Leray_fixedCofinalEscape_of_noTrace244
      hH3 hClass hL hNoTrace with hLap | hLeray
  · exact h3Path_physicalLaplacian_cofinalEscape_forces_spectralState244
      hH3 hClass hLap
  · exact h3Path_physicalLeray_cofinalEscape_forces_spectralState244
      hH3 hClass hLeray

/-- A finite bound for the actual weighted spectral state on a terminal
subtail bounds the actual physical projected source and produces a strong
physical L² terminal trace carrying the canonical terminal kinetic mass. -/
theorem h3Path_physicalL2Trace_of_actualSpectralState_ceiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (C : ℝ)
    (hCeil : ∀ r : ℝ, r ∈ Set.Ioo b T →
      ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ≤ C) :
    ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U) ∧
        ‖U‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T := by
  let D : ℝ := max C 0
  have hD : 0 ≤ D := le_max_right C 0
  let K : ℝ := h3AuditInitialLerayEnergyCoefficient
  have hK : 0 ≤ K := h3AuditInitialLerayEnergyCoefficient_nonneg
  have hSourceCeil : ∀ r : ℝ, r ∈ Set.Ioo b T →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
        3 * D + K * D ^ 2 := by
    intro r hr
    have hS : ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ≤ D :=
      (hCeil r hr).trans (le_max_left C 0)
    have hSq : ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2 ≤ D ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hD).2 hS
    calc
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤
          3 * ‖h3AuditActualSpectralVelocityTotal hH3 r‖ +
            K * ‖h3AuditActualSpectralVelocityTotal hH3 r‖ ^ 2 :=
        h3Path_physicalProjectedSource_norm_le_actualSpectralGrowth244
          hH3 r ⟨lt_trans hClass.terminal_start.1 (lt_trans hb.1 hr.1), hr.2⟩
      _ ≤ 3 * D + K * D ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hS (by norm_num))
          (mul_le_mul_of_nonneg_left hSq hK)
  obtain ⟨U, hU⟩ := h3Path_physicalL2Trace_of_projectedSource_ceiling244
    hH3 hClass hL b hb (3 * D + K * D ^ 2) hSourceCeil
  exact ⟨U, hU,
    h3Path_physicalVelocity_terminalTrace_norm_sq_eq_kineticLimit244
      hH3 hClass U hU⟩

/-- Either the positive-kinetic-mass endpoint has an exact-mass physical
L² terminal trace or the actual weighted H³ spectral velocity norm escapes
cofinally. The second branch is NOT asserted from H³ nonextension. -/
theorem h3Path_physicalL2Trace_or_actualSpectralStateCofinalEscape244
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
        ∃ r : ℝ, r ∈ Set.Ioo b T ∧
          M < ‖h3AuditActualSpectralVelocityTotal hH3 r‖) := by
  by_cases hTrace : ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3) (𝓝[<] T) (𝓝 U)
  · obtain ⟨U, hU⟩ := hTrace
    exact Or.inl ⟨U, hU,
      h3Path_physicalVelocity_terminalTrace_norm_sq_eq_kineticLimit244
        hH3 hClass U hU⟩
  · exact Or.inr
      (h3Path_physicalSpectralState_cofinally_unbounded_of_noL2Trace244
        hH3 hClass hL hTrace)

end
end PrimeTensor.FirstMonomialTriad
