import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralCubicDissipationIntegratedWindows244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFixedFrequencyDissipationEvacuation244
import Mathlib.Tactic

/-!
# Absolute terminal high-radial H³ dissipation escape below arbitrary subcutoffs

The previously proved four-channel/no-strong-kinetic-trace terminal witness
has genuine high-radial physical H³ dissipation larger than `(n+1)^3` at
radial cutoff `n+1`.  In this module we prove that the actual high-radial
spectral integral is antitone in its radial cutoff, by the exact low/high
physical partition and nonnegativity of the dissipation density.

As a consequence, ONE AND THE SAME terminal sequence exhibits divergence of
absolute physical high-radial dissipation for every cutoff profile `rho n`
that is eventually bounded above by `n+1`.  No continuity of full H³
physical dissipation, temporal integral growth, or uniform persistence width
is asserted.  The result holds under the actual positive terminal kinetic
mass and failure of a strong physical kinetic L² terminal trace.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The genuine physical high-radial H³ dissipation is antitone in radius.
We use the already-verified low-radial monotonicity and exact partition;
this does not require pointwise Fourier representatives or time continuity. -/
theorem h3Path_actualHighRadialDissipation_antitone_radius244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T)
    {ρ σ : ℝ} (hρσ : ρ ≤ σ) :
    h3PathActualHighRadialDissipation244 σ
        (h3AuditActualSpectralVelocityTotal hH3 t) ≤
      h3PathActualHighRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  have hLow := h3Path_actualLowRadialDissipation_mono_radius244
    hH3 hClass t ht hρσ
  have hPartρ := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ht ρ
  have hPartσ := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ht σ
  linarith only [hLow, hPartρ, hPartσ]

/-- Every eventually smaller moving cutoff inherits ABSOLUTE high-radial
physical H³ dissipation divergence along the same cubic witness.  The
profile may grow, oscillate, or remain fixed; no new times are selected. -/
theorem h3Path_cubicHighRadialSequence_allSubcutoffHigh_tendsto_atTop244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ)
    (hτ : ∀ n : ℕ, τ n ∈ Set.Ioo a T)
    (hCubic : ∀ n : ℕ,
      ((n : ℝ) + 1) ^ 3 <
        h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n))) :
    ∀ ρ : ℕ → ℝ,
      (∀ᶠ n : ℕ in atTop, ρ n ≤ (n : ℝ) + 1) →
      Tendsto (fun n : ℕ =>
        h3PathActualHighRadialDissipation244 (ρ n)
          (h3AuditActualSpectralVelocityTotal hH3 (τ n))) atTop atTop := by
  intro ρ hCutoff
  apply tendsto_atTop.2
  intro M
  obtain ⟨N, hN⟩ := exists_nat_gt M
  filter_upwards [hCutoff, eventually_ge_atTop N] with n hρ hNn
  have hNReal : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hNn
  have hM : M < (n : ℝ) := lt_of_lt_of_le hN hNReal
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hR : 0 ≤ (n : ℝ) + 1 := by positivity
  have hR2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ)]
  have hCubeLower : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by
    calc
      (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
      _ = ((n : ℝ) + 1) * 1 := by ring
      _ ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left hR2 hR
      _ = ((n : ℝ) + 1) ^ 3 := by ring
  have hMono := h3Path_actualHighRadialDissipation_antitone_radius244
    hH3 hClass (τ n) (hτ n) hρ
  have hLarge : M < h3PathActualHighRadialDissipation244 (ρ n)
      (h3AuditActualSpectralVelocityTotal hH3 (τ n)) :=
    lt_of_lt_of_le
      (lt_trans (lt_of_lt_of_le hM hCubeLower) (hCubic n))
      hMono
  exact hLarge.le

/-- In the physical no-kinetic-L²-terminal-trace branch, one terminal
sequence supports divergent high-radial dissipation at EVERY eventually
sublinear cutoff profile.  This is stronger than the normalized evacuation
and keeps the same selected sequence across all profiles. -/
theorem h3Path_physicalNoL2Trace_forces_allSubcutoffHighDivergence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ ρ : ℕ → ℝ,
        (∀ᶠ n : ℕ in atTop, ρ n ≤ (n : ℝ) + 1) →
        Tendsto (fun n : ℕ =>
          h3PathActualHighRadialDissipation244 (ρ n)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) atTop atTop) := by
  obtain ⟨τ, hτ, hNear, hLimit, hCubic⟩ :=
    h3Path_physicalNoL2Trace_forces_highRadialCubicDissipationSequence244
      hH3 hClass hMass hNoTrace
  exact ⟨τ, hτ, hNear, hLimit,
    h3Path_cubicHighRadialSequence_allSubcutoffHigh_tendsto_atTop244
      hH3 hClass τ hτ hCubic⟩


/-- Explicit fixed-radius formulation: EVERY fixed physical Fourier radius
shares one terminal sequence of divergent high-radial H³ dissipation. -/
theorem h3Path_physicalNoL2Trace_forces_allFixedHighDivergence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ ρ : ℝ, Tendsto (fun n : ℕ =>
        h3PathActualHighRadialDissipation244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 (τ n))) atTop atTop) := by
  obtain ⟨τ, hτ, _hNear, hLimit, hProfiles⟩ :=
    h3Path_physicalNoL2Trace_forces_allSubcutoffHighDivergence244
      hH3 hClass hMass hNoTrace
  refine ⟨τ, hτ, hLimit, ?_⟩
  intro ρ
  obtain ⟨N, hN⟩ := exists_nat_gt ρ
  have hEvent : ∀ᶠ n : ℕ in atTop, ρ ≤ (n : ℝ) + 1 := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith only [hN, hCast]
  exact hProfiles (fun _ : ℕ => ρ) hEvent

end
end PrimeTensor.FirstMonomialTriad
