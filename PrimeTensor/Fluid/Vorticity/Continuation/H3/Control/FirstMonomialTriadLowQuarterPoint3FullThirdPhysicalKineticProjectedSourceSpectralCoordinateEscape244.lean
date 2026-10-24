import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralStateEscape244
import Mathlib.Tactic

/-!
# A fixed actual H³ spectral velocity coordinate carries terminal escape

The preceding module obtains cofinal unboundedness of the three-component
weighted Fourier velocity state from failure of a strong physical L² terminal
trace (for positive terminal kinetic mass). This module makes the finite
component selection *fixed*: one of the three weighted Fourier velocity
coordinates has arbitrarily large norm on every strict terminal subtail.

This is a finite-product argument, not a frequency-localization result.
A second lemma shows that subtracting a uniformly bounded spectral carrier
cannot remove this cofinal escape. In a subsequent module that carrier can
be instantiated by a proved uniformly bounded low-frequency cutoff.

For zero terminal kinetic mass there is already a strong physical L² trace;
thus the exact-mass-trace versus fixed-coordinate-escape alternative needs
no positivity assumption on the terminal kinetic mass.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Cofinal norm escape of a `Fin 3` product has a *fixed* cofinally
unbounded coordinate. The selected coordinate is independent of the
terminal subtail and of the requested threshold. -/
theorem h3Path_cofinalSpectralNormEscape_has_fixedCoordinate244
    {a T : ℝ}
    (S : ℝ → H3SpectralVelocityState)
    (hEscape : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < ‖S r‖) :
    ∃ j : Fin 3, ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < ‖S r j‖ := by
  classical
  by_contra hNone
  have hEach (j : Fin 3) :
      ∃ b : ℝ, b ∈ Set.Ioo a T ∧
        ∃ C : ℝ, ∀ r : ℝ, r ∈ Set.Ioo b T → ‖S r j‖ ≤ C := by
    by_contra hNoBound
    apply hNone
    refine ⟨j, ?_⟩
    intro b hb M
    by_contra hNoLarge
    apply hNoBound
    refine ⟨b, hb, M, ?_⟩
    intro r hr
    by_contra hNotLE
    apply hNoLarge
    exact ⟨r, hr, lt_of_not_ge hNotLE⟩
  obtain ⟨b0, hb0, C0, h0⟩ := hEach 0
  obtain ⟨b1, hb1, C1, h1⟩ := hEach 1
  obtain ⟨b2, hb2, C2, h2⟩ := hEach 2
  let b : ℝ := max b0 (max b1 b2)
  let C : ℝ := max 0 (max C0 (max C1 C2))
  have hb0b : b0 ≤ b := le_max_left _ _
  have hb1b : b1 ≤ b :=
    (le_max_left b1 b2).trans (le_max_right b0 (max b1 b2))
  have hb2b : b2 ≤ b :=
    (le_max_right b1 b2).trans (le_max_right b0 (max b1 b2))
  have hb : b ∈ Set.Ioo a T := by
    constructor
    · exact lt_of_lt_of_le hb0.1 hb0b
    · exact (max_lt_iff).2
        ⟨hb0.2, (max_lt_iff).2 ⟨hb1.2, hb2.2⟩⟩
  have hCnonneg : 0 ≤ C := le_max_left _ _
  have hC0 : C0 ≤ C :=
    (le_max_left C0 (max C1 C2)).trans
      (le_max_right 0 (max C0 (max C1 C2)))
  have hC1 : C1 ≤ C :=
    ((le_max_left C1 C2).trans
      (le_max_right C0 (max C1 C2))).trans
        (le_max_right 0 (max C0 (max C1 C2)))
  have hC2 : C2 ≤ C :=
    ((le_max_right C1 C2).trans
      (le_max_right C0 (max C1 C2))).trans
        (le_max_right 0 (max C0 (max C1 C2)))
  have hAll : ∀ r : ℝ, r ∈ Set.Ioo b T →
      ∀ j : Fin 3, ‖S r j‖ ≤ C := by
    intro r hr j
    fin_cases j
    · exact (h0 r ⟨lt_of_le_of_lt hb0b hr.1, hr.2⟩).trans hC0
    · exact (h1 r ⟨lt_of_le_of_lt hb1b hr.1, hr.2⟩).trans hC1
    · exact (h2 r ⟨lt_of_le_of_lt hb2b hr.1, hr.2⟩).trans hC2
  obtain ⟨r, hr, hHigh⟩ := hEscape b hb C
  have hBound : ‖S r‖ ≤ C := by
    apply (pi_norm_le_iff_of_nonneg hCnonneg).2
    exact hAll r hr
  exact (not_lt_of_ge hBound) hHigh

/-- With positive terminal kinetic mass, failure of the physical L² trace
forces a single actual weighted H³ spectral coordinate to be unbounded
cofinally. Neither the coordinate nor its selection may depend on b or M. -/
theorem h3Path_physicalNoL2Trace_forces_fixedSpectralCoordinateEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ j : Fin 3, ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖(h3AuditActualSpectralVelocityTotal hH3 r) j‖ := by
  exact h3Path_cofinalSpectralNormEscape_has_fixedCoordinate244
    (h3AuditActualSpectralVelocityTotal hH3)
    (h3Path_physicalSpectralState_cofinally_unbounded_of_noL2Trace244
      hH3 hClass hL hNoTrace)

/-- Subtracting any *uniformly bounded* spectral carrier leaves the
cofinal escape in the residual. This theorem requires no projection, cutoff,
or commutation hypothesis; those belong to a later concrete application. -/
theorem h3Path_cofinalSpectralNormEscape_forces_residualEscape244
    {a T : ℝ}
    (S Low : ℝ → H3SpectralVelocityState)
    (C : ℝ)
    (hLow : ∀ r : ℝ, r ∈ Set.Ioo a T → ‖Low r‖ ≤ C)
    (hEscape : ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < ‖S r‖) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧ M < ‖S r - Low r‖ := by
  intro b hb M
  obtain ⟨r, hr, hHigh⟩ := hEscape b hb (C + M)
  have hrTail : r ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 hr.1, hr.2⟩
  refine ⟨r, hr, ?_⟩
  have hSplit : S r = Low r + (S r - Low r) := by
    abel
  have hTriangle : ‖S r‖ ≤ ‖Low r‖ + ‖S r - Low r‖ := by
    calc
      ‖S r‖ = ‖Low r + (S r - Low r)‖ := congrArg norm hSplit
      _ ≤ ‖Low r‖ + ‖S r - Low r‖ := norm_add_le _ _
  have hLowBound := hLow r hrTail
  linarith

/-- For a physical path without strong L² terminal trace, the actual H³
spectral velocity still escapes after subtracting any carrier whose
spectral norm has a fixed ceiling on the energy-class interval. -/
theorem h3Path_physicalNoL2Trace_forces_spectralResidualEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (Low : ℝ → H3SpectralVelocityState)
    (C : ℝ)
    (hLow : ∀ r : ℝ, r ∈ Set.Ioo a T → ‖Low r‖ ≤ C) :
    ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
      ∃ r : ℝ, r ∈ Set.Ioo b T ∧
        M < ‖h3AuditActualSpectralVelocityTotal hH3 r - Low r‖ := by
  exact h3Path_cofinalSpectralNormEscape_forces_residualEscape244
    (h3AuditActualSpectralVelocityTotal hH3) Low C hLow
    (h3Path_physicalSpectralState_cofinally_unbounded_of_noL2Trace244
      hH3 hClass hL hNoTrace)

/-- The exact-mass L² trace versus *fixed spectral coordinate* escape
dichotomy holds without requiring positive terminal kinetic mass. In the
zero-mass case the velocity tends strongly to zero. -/
theorem h3Path_physicalL2Trace_or_fixedSpectralCoordinateEscape_allKinetic244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U) ∧
        ‖U‖ ^ 2 = h3PathCanonicalTerminalKineticEnergyAt u a T) ∨
      (0 < h3PathCanonicalTerminalKineticEnergyAt u a T ∧
        ∃ j : Fin 3, ∀ b : ℝ, b ∈ Set.Ioo a T → ∀ M : ℝ,
          ∃ r : ℝ, r ∈ Set.Ioo b T ∧
            M < ‖(h3AuditActualSpectralVelocityTotal hH3 r) j‖) := by
  let L : ℝ := h3PathCanonicalTerminalKineticEnergyAt u a T
  by_cases hZero : L = 0
  · left
    refine ⟨0, h3Path_physicalVelocity_tendsto_zero_of_zeroTerminalKinetic244
      hH3 hClass hZero, ?_⟩
    simpa using hZero.symm
  · have hNonneg : 0 ≤ L :=
      h3PathCanonical_terminalKineticEnergy_nonneg hClass
    have hPos : 0 < L := lt_of_le_of_ne hNonneg (Ne.symm hZero)
    rcases h3Path_physicalL2Trace_or_actualSpectralStateCofinalEscape244
        hH3 hClass hPos with hTrace | hEscape
    · exact Or.inl hTrace
    · exact Or.inr ⟨hPos,
        h3Path_cofinalSpectralNormEscape_has_fixedCoordinate244
          (h3AuditActualSpectralVelocityTotal hH3) hEscape⟩

end
end PrimeTensor.FirstMonomialTriad
