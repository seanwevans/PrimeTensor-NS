import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellRiccatiPhysicalCarrierOrSourcePeak
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellOvershootEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalSourceLaplacianLerayTemporalSplit244
import Mathlib.Tactic

/-!
# Minimal-shell Riccati carrier: exact kinetic overshoot or physical PDE excursions

The actual minimal first crossing has a strictly positive overshoot omega and
last-shell raw kinetic mass mu, with omega <= 4*(N+2)^8*mu. Rather than
assuming a fixed fraction of cubic overshoot, we divide by the positive
weight to preserve its exact (potentially tiny) mass cost.

An attained canonical projected source peak need not occur in the smaller
physical dissipation window. On its actual half-terminal source interval,
P(s) = D(s)-L(s), so a source peak above 3 L forces either the projected
source at the original anchor above L, a physical Fourier Laplacian temporal
excursion above L, or a physical Leray temporal excursion above L.

Combining these with the established every-(D,L) kinetic carrier/source
alternative supplies a four-channel obstruction on precisely the same
minimal first-crossing witnesses. No terminal full-H3 dissipation estimate,
source-time modulus, uniform normalized shell mass or overshoot is assumed.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeMinimalPDEExcursion
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMinimalPDEExcursion :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The actual projected physical source decomposes at two fixed times:
three times the component threshold at the peak demands at least one
strict threshold at the anchor, the physical diffusion increment, or the
physical Leray increment. No temporal differentiability is required. -/
theorem h3Critical_minimalShell_physicalSourcePeak_forces_PDEComponentExcursion
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t s L : ℝ)
    (hPeak : 3 * L < ‖h3PathActualProjectedMomentumSource244 hH3 s‖) :
    L < ‖h3PathActualProjectedMomentumSource244 hH3 t‖ ∨
    L < ‖h3AuditInitialActualSpectralLaplacianTotal hH3 s -
      h3AuditInitialActualSpectralLaplacianTotal hH3 t‖ ∨
    L < ‖h3AuditInitialActualSpectralLerayTotal hH3 s -
      h3AuditInitialActualSpectralLerayTotal hH3 t‖ := by
  have hTriangle :=
    h3Path_physicalSourcePeak_le_anchor_diffusionJump_lerayJump244
      (h3AuditInitialActualSpectralLaplacianTotal hH3 s)
      (h3AuditInitialActualSpectralLaplacianTotal hH3 t)
      (h3AuditInitialActualSpectralLerayTotal hH3 s)
      (h3AuditInitialActualSpectralLerayTotal hH3 t)
  change ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤
      ‖h3PathActualProjectedMomentumSource244 hH3 t‖ +
      ‖h3AuditInitialActualSpectralLaplacianTotal hH3 s -
        h3AuditInitialActualSpectralLaplacianTotal hH3 t‖ +
      ‖h3AuditInitialActualSpectralLerayTotal hH3 s -
        h3AuditInitialActualSpectralLerayTotal hH3 t‖ at hTriangle
  by_cases hAnchor : L < ‖h3PathActualProjectedMomentumSource244 hH3 t‖
  · exact Or.inl hAnchor
  by_cases hDiff : L < ‖h3AuditInitialActualSpectralLaplacianTotal hH3 s -
      h3AuditInitialActualSpectralLaplacianTotal hH3 t‖
  · exact Or.inr (Or.inl hDiff)
  · right
    right
    have hAnchorLe := le_of_not_gt hAnchor
    have hDiffLe := le_of_not_gt hDiff
    linarith only [hPeak, hTriangle, hAnchorLe, hDiffLe]

/-- The exact last-shell overshoot gives an actual positive raw kinetic
mass lower bound divided by the real physical outer eighth-power weight.
The overshoot is NOT claimed to be a fixed fraction of the cubic crossing. -/
theorem h3Critical_minimalShell_lastCarrier_pays_exactOvershootMass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (n N m : ℕ) (C δ : ℝ)
    (hWindow : h3CriticalMinimalShellEnergyWindow hH3 t n N m C δ) :
    0 < h3CriticalMinimalShellOvershoot hH3 t n N ∧
    0 < h3CriticalMinimalLastShellMass hH3 t m N ∧
    h3CriticalMinimalShellOvershoot hH3 t n N /
        (4 * (((N : ℝ) + 2) ^ 8)) ≤
      h3CriticalMinimalLastShellMass hH3 t m N := by
  rcases hWindow with ⟨_, _, _, _, _, _, _, _, hQuarter,
    _, _, _, _, hMass, hOver⟩
  have hOmega : 0 < h3CriticalMinimalShellOvershoot hH3 t n N := by
    dsimp only [h3CriticalMinimalShellOvershoot]
    linarith only [hQuarter]
  have hMu : 0 < h3CriticalMinimalLastShellMass hH3 t m N := by
    simpa only [h3CriticalMinimalLastShellMass] using hMass
  have hDen : 0 < 4 * (((N : ℝ) + 2) ^ 8) := by positivity
  have hOmegaLe : h3CriticalMinimalShellOvershoot hH3 t n N ≤
      (4 * (((N : ℝ) + 2) ^ 8)) *
        h3CriticalMinimalLastShellMass hH3 t m N := by
    simpa only [h3CriticalMinimalShellOvershoot,
      h3CriticalMinimalLastShellMass] using hOver
  have hOmegaLe' : h3CriticalMinimalShellOvershoot hH3 t n N ≤
      h3CriticalMinimalLastShellMass hH3 t m N *
        (4 * (((N : ℝ) + 2) ^ 8)) := by
    calc
      _ ≤ (4 * (((N : ℝ) + 2) ^ 8)) *
            h3CriticalMinimalLastShellMass hH3 t m N := hOmegaLe
      _ = h3CriticalMinimalLastShellMass hH3 t m N *
            (4 * (((N : ℝ) + 2) ^ 8)) := by ring
  exact ⟨hOmega, hMu, (div_le_iff₀ hDen).2 hOmegaLe'⟩

/-- The exact same minimal shell, anchor, and canonical half-terminal source
interval support one of four real physical charges. The source-peak arm is
resolved into its original anchor, Laplacian increment or Leray increment;
the carrier retains the actual, possibly tiny, kinetic mass lower bound. -/
def h3CriticalMinimalShellRiccatiCarrierOrPDEExcursionAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℕ → ℝ) (N m : ℕ → ℕ) (v : ℕ → ℕ)
    (k : ℕ) (D L : ℝ) : Prop :=
  ((v k : ℝ) + 1) ^ 2 <
      4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
        velocityH3EnergyAt u (t (v k)) ∨
  (D * ((v k : ℝ) + 1) < (m (v k) : ℝ) + 2 ∧
    0 < h3CriticalMinimalShellOvershoot hH3 (t (v k)) (v k) (N (v k)) ∧
    0 < h3CriticalMinimalLastShellMass hH3 (t (v k)) (m (v k)) (N (v k)) ∧
    h3CriticalMinimalShellOvershoot hH3 (t (v k)) (v k) (N (v k)) /
        (4 * (((N (v k) : ℝ) + 2) ^ 8)) ≤
      h3CriticalMinimalLastShellMass hH3 (t (v k)) (m (v k)) (N (v k))) ∨
  (∃ s : ℝ,
    s ∈ Set.Icc (t (v k)) (t (v k) + (T - t (v k)) / 2) ∧
    (L < ‖h3PathActualProjectedMomentumSource244 hH3 (t (v k))‖ ∨
     L < ‖h3AuditInitialActualSpectralLaplacianTotal hH3 s -
       h3AuditInitialActualSpectralLaplacianTotal hH3 (t (v k))‖ ∨
     L < ‖h3AuditInitialActualSpectralLerayTotal hH3 s -
       h3AuditInitialActualSpectralLerayTotal hH3 (t (v k))‖))

/-- Upgrade the accepted actual-carrier/source-peak theorem without changing
any first-crossing witnesses. Every threshold L is tested at 3L before the
actual physical source is split across anchor, diffusion and Leray. -/
theorem h3Critical_minimalShell_actualCarrierSource_refine_PDEExcursion
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℕ → ℝ) (N m : ℕ → ℕ) (C δ : ℕ → ℝ)
    (v : ℕ → ℕ)
    (hWindows : ∀ k : ℕ,
      h3CriticalMinimalShellEnergyWindow hH3
        (t (v k)) (v k) (N (v k)) (m (v k))
        (C (v k)) (δ (v k)))
    (hActual : ∀ D L : ℝ, 0 ≤ D → 0 ≤ L →
      ∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          (((v k : ℝ) + 1) ^ 2 <
            4 * (4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1) *
              velocityH3EnergyAt u (t (v k))) ∨
          ((D * ((v k : ℝ) + 1) < (m (v k) : ℝ) + 2) ∧
            0 < h3PathActualBandRawKineticMass244
              ((m (v k) : ℝ) + 1) ((m (v k) : ℝ) + 2)
              (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) ∨
          (∃ s : ℝ,
            s ∈ Set.Icc (t (v k))
              (t (v k) + (T - t (v k)) / 2) ∧
            L < ‖h3PathActualProjectedMomentumSource244 hH3 s‖)) :
    ∀ D L : ℝ, 0 ≤ D → 0 ≤ L →
      ∀ᶠ k : ℕ in atTop,
        h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
          h3CriticalMinimalShellRiccatiCarrierOrPDEExcursionAt
            hH3 t N m v k D L := by
  intro D L hD hL
  have hThreeL : 0 ≤ 3 * L := by positivity
  have hAt := hActual D (3 * L) hD hThreeL
  filter_upwards [hAt] with k hk
  intro hRic
  rcases hk hRic with hEnergy | hCarrier | hSource
  · exact Or.inl hEnergy
  · right
    left
    have hMass := h3Critical_minimalShell_lastCarrier_pays_exactOvershootMass
      hH3 (t (v k)) (v k) (N (v k)) (m (v k))
      (C (v k)) (δ (v k)) (hWindows k)
    exact ⟨hCarrier.1, hMass.1, hMass.2.1, hMass.2.2⟩
  · right
    right
    obtain ⟨s, hs, hPeak⟩ := hSource
    refine ⟨s, hs, ?_⟩
    exact h3Critical_minimalShell_physicalSourcePeak_forces_PDEComponentExcursion
      hH3 (t (v k)) s L hPeak

/-- Preserve the genuinely selected minimal first-crossing, signed-gap,
positive last-shell and original sixth/ninth source-rate witnesses. In the
bounded-charge pressure branch, each late Riccati-heavy window pays either
quadratic H3 anchor energy, an explicitly overshoot-charged occupied last
Fourier shell beyond D times the inner frequency, or a large actual source
anchor/diffusion/Leray excursion on the original canonical time interval. -/
theorem h3Critical_noL2Trace_minimalShell_kineticCarrierOrPhysicalPDEExcursion
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N m : ℕ → ℕ, ∃ C δ : ℕ → ℝ,
    ∃ v j : ℕ → ℕ, ∃ k₁ : ℕ,
      StrictMono v ∧
      Tendsto (fun k => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ, h3CriticalMinimalShellEnergyWindow
        hH3 (t (v k)) (v k) (N (v k)) (m (v k))
        (C (v k)) (δ (v k))) ∧
      h3CriticalMinimalShellPhysicalSixthNinthAlternative (u := u)
        T t N C δ v ∧
      (∀ᶠ k : ℕ in atTop,
        v k ≤ j k ∧ j k < N (v k) ∧
        0 < h3PathActualBandRawKineticMass244
          ((j k : ℝ) + 1) ((j k : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) ∧
      h3CriticalMinimalShellEveryTailSignedAccounting u t δ v k₁ ∧
      ((∀ M : ℝ, ∃ q : ℕ,
          M < ∑ k ∈ Finset.range q,
            h3CriticalMinimalShellCubicWindowCost δ v k) ∨
        (∀ D L : ℝ, 0 ≤ D → 0 ≤ L →
          ∀ᶠ k : ℕ in atTop,
            h3CriticalMinimalShellRiccatiWindowAt u t δ v k →
              h3CriticalMinimalShellRiccatiCarrierOrPDEExcursionAt
                hH3 t N m v k D L)) := by
  obtain ⟨t, N, m, C, δ, v, j, k₁,
      hv, hLimit, hSeparate, hWindows, hRates, hShell, hAccounting,
      hAlt⟩ :=
    h3Critical_noL2Trace_minimalShell_actualCarrierOrPhysicalSourcePeak
      hH3 hClass hNoTrace
  refine ⟨t, N, m, C, δ, v, j, k₁,
    hv, hLimit, hSeparate, hWindows, hRates, hShell, hAccounting, ?_⟩
  rcases hAlt with hDivergent | hActual
  · exact Or.inl hDivergent
  · exact Or.inr
      (h3Critical_minimalShell_actualCarrierSource_refine_PDEExcursion
        hH3 t N m C δ v hWindows hActual)

end
end PrimeTensor.Bridge.Euclidean
