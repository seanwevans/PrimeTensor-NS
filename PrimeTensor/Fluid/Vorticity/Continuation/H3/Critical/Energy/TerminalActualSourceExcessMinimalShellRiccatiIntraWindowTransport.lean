import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellRiccatiQuadraticEnergy
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessAutomaticIntegratedGapTransport
import Mathlib.Tactic

/-!
# Minimal-shell Riccati energy: anchor burden or actual intra-window replenishment

A Riccati-heavy instant on a minimal physical PDE window already costs quadratic
H3 energy at its OWN time s. This module accounts for the rise from the
original first-crossing anchor time t to that SAME physical s. The exact H3
energy balance, plus automatic integrability on compact strict-time intervals,
forces one of two *actual* charges:

  R^2 < 2 B E3(t)  or
  R^2 < 2 B ∫_[t,s] max(0, -Transport3 - 2 Dissipation3),

where B = 4 K_Riccati^2 + 1. No assumed H3 time-Lipschitz constant, no
terminal full-H3 dissipation budget, and no replacement PDE/kinetic witnesses.

The cofinal consequence still needs the two EXPLICIT hypotheses of the
accepted every-tail theorem: unbounded window charges and bounded positive
inter-window replenishment. It does not silently assert these PDE estimates.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeMinimalIntraWindow
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMinimalIntraWindow :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- If quadratic amplitude occurs later, then either the original anchor
already pays half its amplitude or the actual positive energy gain does.
No sign condition on E1-E0 or on G is needed. -/
theorem h3Critical_scalar_quadraticPeak_anchorOrActualGain
    (R B E0 E1 G : ℝ) (hB : 0 ≤ B)
    (hPeak : R ^ 2 < B * E1)
    (hGain : E1 - E0 ≤ G) :
    R ^ 2 < 2 * B * E0 ∨ R ^ 2 < 2 * B * G := by
  by_cases hAnchor : R ^ 2 < 2 * B * E0
  · exact Or.inl hAnchor
  · right
    have hAnchorLe : 2 * B * E0 ≤ R ^ 2 := le_of_not_gt hAnchor
    have hScaled : B * (E1 - E0) ≤ B * G :=
      mul_le_mul_of_nonneg_left hGain hB
    nlinarith only [hPeak, hAnchorLe, hScaled]

/-- An actual physical Riccati-heavy window contains an instant s at which
quadratic energy is paid either at the initial anchor or by the positive
signed transport-minus-viscosity integral from the anchor to s. -/
def h3CriticalMinimalShellQuadraticAnchorOrSignedWindowAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t δ : ℕ → ℝ) (v : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ s : ℝ,
    s ∈ Set.Icc (t (v k)) (t (v k) + δ (v k)) ∧
    let R : ℝ := (v k : ℝ) + 1
    let B : ℝ := 4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1
    R ^ 2 < 2 * B * velocityH3EnergyAt u (t (v k)) ∨
      R ^ 2 < 2 * B *
        (∫ z in t (v k)..s,
          max 0 (-velocityH3TransportDerivativeAt u z -
            2 * velocityH3DissipationAt u z))

/-- The physical intra-window charge follows from the exact signed H3
balance, automatic compact-slice FTC and the previously proved quadratic
Riccati energy bound. The equal-anchor case is handled separately. -/
theorem h3Critical_minimalShellQuadraticWindow_anchorOrSignedTransport
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t δ : ℕ → ℝ) (v : ℕ → ℕ) (k : ℕ)
    (ht : t (v k) ∈ Set.Ioo a T)
    (hEnd : t (v k) + δ (v k) < T)
    (hQuadratic : h3CriticalMinimalShellQuadraticEnergyWindowAt u t δ v k) :
    h3CriticalMinimalShellQuadraticAnchorOrSignedWindowAt u t δ v k := by
  obtain ⟨s, hs, hPeak⟩ := hQuadratic
  refine ⟨s, hs, ?_⟩
  let R : ℝ := (v k : ℝ) + 1
  let B : ℝ := 4 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 + 1
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hGain :
      velocityH3EnergyAt u s - velocityH3EnergyAt u (t (v k)) ≤
        ∫ z in t (v k)..s,
          max 0 (-velocityH3TransportDerivativeAt u z -
            2 * velocityH3DissipationAt u z) := by
    by_cases hStrict : t (v k) < s
    · exact h3Critical_physicalGap_integratedSignedTransport_pays_energyGain_automatic
        hH3 hClass (t (v k)) s ht hsClass hStrict
    · have heq : s = t (v k) :=
        le_antisymm (le_of_not_gt hStrict) hs.1
      rw [heq]
      simp
  have hPeak' : R ^ 2 < B * velocityH3EnergyAt u s := by
    simpa only [R, B] using hPeak
  have hEither := h3Critical_scalar_quadraticPeak_anchorOrActualGain
    R B (velocityH3EnergyAt u (t (v k))) (velocityH3EnergyAt u s)
    (∫ z in t (v k)..s,
      max 0 (-velocityH3TransportDerivativeAt u z -
        2 * velocityH3DissipationAt u z)) hB hPeak' hGain
  simpa only [R, B] using hEither

/-- No-terminal-L2-trace minimal first crossings keep their original actual
kinetic, spectral-width, sixth/ninth PDE and signed-gap certificates. Under
the EXISTING two conditional finite-tail hypotheses, arbitrarily late
Riccati-heavy windows pay a *quadratic* cost either already at the original
energy anchor or through actual integrated positive signed transport INSIDE
that particular PDE window. -/
theorem h3Critical_noL2Trace_minimalShell_cofinalQuadraticAnchorOrIntraWindowTransport
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
      (∀ k : ℕ,
        1 < 4 * (velocityH3EnergyAt u (t (v k)) / ((v k : ℝ) + 1)) *
          (((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) ^ 2) ∧
      (∀ᶠ k : ℕ in atTop,
        v k ≤ j k ∧ j k < N (v k) ∧
        0 < h3PathActualBandRawKineticMass244
          ((j k : ℝ) + 1) ((j k : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) ∧
      (∀ k : ℕ, k₁ ≤ k →
        h3CriticalMinimalShellSignedTransportBudgetAt
          hH3 (t (v k)) (v k) (δ (v k))) ∧
      h3CriticalMinimalShellEveryTailSignedAccounting u t δ v k₁ ∧
      (h3CriticalMinimalShellEveryTailCubicChargeUnbounded δ v k₁ →
        h3CriticalMinimalShellEveryTailGapBudget u t δ v k₁ →
        ∀ b : ℕ, ∃ i : ℕ, b ≤ i ∧
          h3CriticalMinimalShellQuadraticAnchorOrSignedWindowAt
            u t δ v (i + k₁)) := by
  obtain ⟨t, N, m, C, δ, v, j, k₁, hv, hLimit, hSeparate,
      hWindow, hRates, hEnergyWidth, hShell, hSigned, hAccounting,
      hRecurring⟩ :=
    h3Critical_noL2Trace_minimalShell_cofinalQuadraticEnergyWindows
      hH3 hClass hNoTrace
  have hTailTime : ∀ᶠ k : ℕ in atTop, a < t (v k) := by
    have hOpen : Set.Ioi a ∈ 𝓝 T :=
      isOpen_Ioi.mem_nhds hClass.terminal_start.2
    exact hLimit.eventually hOpen
  obtain ⟨kTime, hkTime⟩ := Filter.eventually_atTop.1 hTailTime
  refine ⟨t, N, m, C, δ, v, j, k₁, hv, hLimit, hSeparate,
    hWindow, hRates, hEnergyWidth, hShell, hSigned, hAccounting, ?_⟩
  intro hCharge hBudget b
  obtain ⟨i, hi, hQuadratic⟩ := hRecurring hCharge hBudget (max b kTime)
  have hStartA : a < t (v (i + k₁)) := by
    apply hkTime
    omega
  have hWindowData := hWindow (i + k₁)
  have hEnd : t (v (i + k₁)) + δ (v (i + k₁)) < T := by
    rcases hWindowData with ⟨_, _, _, _, _, hEnd, _⟩
    exact hEnd
  have hPositive : 0 < δ (v (i + k₁)) := by
    rcases hWindowData with ⟨_, _, _, _, hδ, _⟩
    exact hδ
  have ht : t (v (i + k₁)) ∈ Set.Ioo a T := by
    exact ⟨hStartA, by linarith only [hEnd, hPositive]⟩
  exact ⟨i, le_trans (le_max_left _ _) hi,
    h3Critical_minimalShellQuadraticWindow_anchorOrSignedTransport
      hH3 hClass t δ v (i + k₁) ht hEnd hQuadratic⟩

end
end PrimeTensor.Bridge.Euclidean
