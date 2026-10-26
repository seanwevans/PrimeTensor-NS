import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPhysicalPDEModulus244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Bounded.Radial.Weighted.Cauchy
import Mathlib.Tactic

/-!
# Physical projected-PDE modulus transferred through exact radial Plancherel

The preceding checkpoint proves a temporal modulus for physical L² momentum,
not for untruncated weighted H³ spectral velocity. Existing terminal Fourier
analysis already proves an exact bounded-radial weighted-square defect bound
in terms of the unweighted raw Fourier square defect. Existing Plancherel
identifies that raw defect with the actual physical zero-order velocity jets.

Here we connect that result to the actual old physical Hilbert momentum and
its genuine PDE derivative. At positive strict times, for radial cutoff ρ,

   RadialWeightedDefect_ρ(S(s), S(t))
     ≤ 3 K(ρ) ‖U(t)-U(s)‖²,

where K(ρ) = 1+ρ²+ρ⁴+ρ⁶ is the exact Sobolev weight-square ceiling.
A projected-source ceiling C therefore gives the *quadratic time bound*

   RadialWeightedDefect_ρ(S(s), S(t)) ≤ 3 K(ρ) C² (t-s)².

An H³ energy ceiling supplies C=(3+C_Leray) E. On any compact strict-time
interval, such a C exists without extra hypotheses.

This is a finite-frequency squared-state increment, NOT a global H³
increment or an absolute bound on the fourth-order dissipation. The finite-
annulus gradient multiplier adds a factor of the outer cutoff, and its
quadratic energy variation requires an additional polarization step.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The genuine physical three-component kinetic square defect is bounded
by three times the squared norm of the actual old physical L² Hilbert
momentum increment. This deliberately uses the preexisting jet definitions,
not a new identification or an assumed encoder. -/
theorem h3Path_physicalVelocitySquareDefect_le_threeMomentumSquare244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3TerminalPhysicalVelocityTotalSquareDefect hH3 s t hs ht ≤
      3 * ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
        h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2 := by
  let V : H3PhysicalRealFinVectorL2Hilbert :=
    h3AuditInitialOldPhysicalHilbertTotal hH3 s -
      h3AuditInitialOldPhysicalHilbertTotal hH3 t
  have hJet (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) T) (j : Fin 3) :
      h3TerminalPhysicalVelocityComponentAt hH3 r hr j =
        (h3AuditInitialOldPhysicalHilbertTotal hH3 r) j := by
    change h3TerminalPhysicalVelocityComponentAt hH3 r hr j =
      h3AuditActualPhysicalZeroJetL2Total hH3 j r
    rw [h3AuditActualPhysicalZeroJetL2Total_eq_at hH3 j r hr]
    rfl
  have hComp (j : Fin 3) :
      ‖h3TerminalPhysicalVelocityComponentAt hH3 s hs j -
        h3TerminalPhysicalVelocityComponentAt hH3 t ht j‖ ≤ ‖V‖ := by
    rw [hJet s hs j, hJet t ht j]
    simpa only [V, PiLp.sub_apply] using (PiLp.norm_apply_le V j)
  have hSq (j : Fin 3) :
      ‖h3TerminalPhysicalVelocityComponentAt hH3 s hs j -
        h3TerminalPhysicalVelocityComponentAt hH3 t ht j‖ ^ 2 ≤ ‖V‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hComp j) 2
  change
    ‖h3TerminalPhysicalVelocityComponentAt hH3 s hs 0 -
      h3TerminalPhysicalVelocityComponentAt hH3 t ht 0‖ ^ 2 +
    ‖h3TerminalPhysicalVelocityComponentAt hH3 s hs 1 -
      h3TerminalPhysicalVelocityComponentAt hH3 t ht 1‖ ^ 2 +
    ‖h3TerminalPhysicalVelocityComponentAt hH3 s hs 2 -
      h3TerminalPhysicalVelocityComponentAt hH3 t ht 2‖ ^ 2 ≤
    3 * ‖V‖ ^ 2
  nlinarith only [hSq 0, hSq 1, hSq 2]

/-- Genuine bounded-radial weighted H³ spectral increments are controlled
by physical kinetic L² increments, using the already-closed exact radial
weight ceiling and actual physical Plancherel. No Fourier cutoff lemma is
postulated. -/
theorem h3Path_actualRadialWeightedSquareDefect_le_physicalMomentumSquare244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ
      (h3AuditActualSpectralVelocityTotal hH3 s)
      (h3AuditActualSpectralVelocityTotal hH3 t) ≤
    (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
        h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2 := by
  rw [h3Path_actualSpectralVelocity_eq_terminalState244 hH3 s hs,
    h3Path_actualSpectralVelocity_eq_terminalState244 hH3 t ht]
  have hBound :=
    weightedSpectralVelocityRadialSquareDefect_le_ceiling_mul_rawVelocityFourierTotalSquareDefect
      hρ
      (h3TerminalVelocitySpectralStateAt hH3 s hs)
      (h3TerminalVelocitySpectralStateAt hH3 t ht)
  have hPhysical :=
    h3Path_physicalVelocitySquareDefect_le_threeMomentumSquare244
      hH3 s t hs ht
  have hK : 0 ≤ h3TerminalRadialSobolevWeightSquareCeiling ρ :=
    (h3TerminalRadialSobolevWeightSquareCeiling_pos ρ).le
  calc
    _ ≤ h3TerminalRadialSobolevWeightSquareCeiling ρ *
      h3TerminalRawVelocityFourierTotalSquareDefect
        (h3TerminalVelocitySpectralStateAt hH3 s hs)
        (h3TerminalVelocitySpectralStateAt hH3 t ht) := hBound
    _ = h3TerminalRadialSobolevWeightSquareCeiling ρ *
      h3TerminalPhysicalVelocityTotalSquareDefect hH3 s t hs ht := by
        rw [h3TerminalRawVelocityFourierTotalSquareDefect_velocitySpectralStateAt_eq_physical
          hH3 s t hs ht]
    _ ≤ h3TerminalRadialSobolevWeightSquareCeiling ρ *
      (3 * ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
        h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hPhysical hK
    _ = (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
        h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2 := by ring

/-- A strict-window projected-PDE L² source ceiling yields an explicit
quadratic time modulus for the finite-radius weighted H³ spectral defect. -/
theorem h3Path_actualRadialWeightedSquareDefect_le_projectedPDECeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (s t C : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t)
    (hCeil : ∀ r : ℝ, r ∈ Set.Icc s t →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C) :
    h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ
      (h3AuditActualSpectralVelocityTotal hH3 s)
      (h3AuditActualSpectralVelocityTotal hH3 t) ≤
    (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
      (C * (t - s)) ^ 2 := by
  have hMom := h3Path_physicalMomentum_increment_le_projectedPDECeiling244
    hH3 s t C hs ht hst hCeil
  have hMomRev :
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
        h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ≤ C * (t - s) := by
    simpa only [norm_sub_rev] using hMom
  have hSq :
      ‖h3AuditInitialOldPhysicalHilbertTotal hH3 s -
        h3AuditInitialOldPhysicalHilbertTotal hH3 t‖ ^ 2 ≤
      (C * (t - s)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hMomRev 2
  have hCoeff : 0 ≤ 3 * h3TerminalRadialSobolevWeightSquareCeiling ρ :=
    mul_nonneg (by norm_num)
      (h3TerminalRadialSobolevWeightSquareCeiling_pos ρ).le
  exact (h3Path_actualRadialWeightedSquareDefect_le_physicalMomentumSquare244
    hH3 ρ hρ s t hs ht).trans
      (mul_le_mul_of_nonneg_left hSq hCoeff)

/-- Actual H³-energy control is a sufficient projected-PDE ceiling, with the
existing calibrated physical Laplacian/Leray coefficient. -/
theorem h3Path_actualRadialWeightedSquareDefect_le_H3EnergyCeiling244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (s t E : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hst : s ≤ t)
    (hE : ∀ r : ℝ, r ∈ Set.Icc s t →
      velocityH3EnergyAt u r ≤ E) :
    h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ
      (h3AuditActualSpectralVelocityTotal hH3 s)
      (h3AuditActualSpectralVelocityTotal hH3 t) ≤
    (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
      (((3 + h3AuditInitialLerayEnergyCoefficient) * E) * (t - s)) ^ 2 := by
  have hCoeff : 0 ≤ 3 + h3AuditInitialLerayEnergyCoefficient := by
    have hNonneg := h3AuditInitialLerayEnergyCoefficient_nonneg
    linarith only [hNonneg]
  apply h3Path_actualRadialWeightedSquareDefect_le_projectedPDECeiling244
    hH3 ρ hρ s t ((3 + h3AuditInitialLerayEnergyCoefficient) * E)
    hs ht hst
  intro r hr
  have hrAbs : r ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  exact (h3Path_physicalProjectedSource_norm_le_H3Energy244 hH3 r hrAbs).trans
    (mul_le_mul_of_nonneg_left (hE r hr) hCoeff)

/-- Compact strict-time physical projected PDE continuity provides an
unconditional local quadratic modulus at every fixed Fourier radius. The
constant depends on the interval and may diverge toward the terminal time. -/
theorem h3Path_actualRadialWeightedSquareDefect_compactPDEModulus244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (ha : 0 < a) (hab : a < b) (hb : b < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s t : ℝ, s ∈ Set.Icc a b → t ∈ Set.Icc a b → s ≤ t →
      h3TerminalWeightedSpectralVelocityRadialSquareDefect ρ
        (h3AuditActualSpectralVelocityTotal hH3 s)
        (h3AuditActualSpectralVelocityTotal hH3 t) ≤
      (3 * h3TerminalRadialSobolevWeightSquareCeiling ρ) *
        (C * (t - s)) ^ 2 := by
  obtain ⟨C, hC, hSource⟩ :=
    h3Path_actualProjectedMomentumSource_uniformL2OnStrict244 hH3 ha hab hb
  refine ⟨C, hC, ?_⟩
  intro s t hs ht hst
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hb⟩
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  apply h3Path_actualRadialWeightedSquareDefect_le_projectedPDECeiling244
    hH3 ρ hρ s t C hsAbs htAbs hst
  intro r hr
  exact hSource r ⟨le_trans hs.1 hr.1, le_trans hr.2 ht.2⟩

end
end PrimeTensor.FirstMonomialTriad
