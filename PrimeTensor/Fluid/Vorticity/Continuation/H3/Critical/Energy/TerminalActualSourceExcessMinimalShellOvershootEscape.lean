import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellEnergyRates
import Mathlib.Tactic

/-!
# Minimal H3 last-shell overshoot: critical raw mass versus relative frequency

The SAME canonical first crossing, physical H3 anchor energy, actual source
maximum, exact quadratic-sharp PDE clock and positive annular cost support the
sixth/ninth rate alternative AND a last-shell spectral constraint.

The last shell pays only the *overshoot* above 3 R^3/4, not a fixed fraction
of R^3. We therefore state a quantitative pointwise alternative and its
conditional cofinal consequence without inventing a lower bound on overshoot.
No finite terminal full-H3 dissipation integral is assumed.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeMinimalShellOvershootEscape
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMinimalShellOvershootEscape :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Positive surplus above the strict first-crossing threshold. -/
noncomputable def h3CriticalMinimalShellOvershoot
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (n N : ℕ) : ℝ :=
  (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 t) -
    h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 t)) -
    3 * (((n : ℝ) + 1) ^ 3) / 4

/-- Raw kinetic mass of precisely the last integer shell, not a whole
annulus mass and not the width-averaged pigeonhole shell. -/
noncomputable def h3CriticalMinimalLastShellMass
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (m N : ℕ) : ℝ :=
  h3PathActualBandRawKineticMass244 ((m : ℝ) + 1) ((N : ℝ) + 1)
    (h3AuditActualSpectralVelocityTotal hH3 t)

/-- A last-shell kinetic bound is a two-way restriction: a shell lying
inside any proposed D-times-inner radius must pay its exact overshoot in
critical kinetic mass. No positive normalized overshoot is presumed. -/
theorem h3Critical_scalar_lastShellOvershoot_relativeOuter_or_massCost
    (R Q μ ω D : ℝ) (_hR : 0 < R) (hQ : 0 ≤ Q + 1)
    (hμ : 0 ≤ μ) (_hD : 0 ≤ D)
    (hOver : ω ≤ 4 * (Q + 1) ^ 8 * μ) :
    D * R < Q + 1 ∨ ω ≤ 4 * D ^ 8 * R ^ 8 * μ := by
  by_cases hFar : D * R < Q + 1
  · exact Or.inl hFar
  · right
    have hNear : Q + 1 ≤ D * R := le_of_not_gt hFar
    have hPower : (Q + 1) ^ 8 ≤ (D * R) ^ 8 :=
      pow_le_pow_left₀ hQ hNear 8
    have hScaled : (4 * μ) * (Q + 1) ^ 8 ≤
        (4 * μ) * (D * R) ^ 8 :=
      mul_le_mul_of_nonneg_left hPower (by positivity)
    calc
      ω ≤ 4 * (Q + 1) ^ 8 * μ := hOver
      _ = (4 * μ) * (Q + 1) ^ 8 := by ring
      _ ≤ (4 * μ) * (D * R) ^ 8 := hScaled
      _ = 4 * D ^ 8 * R ^ 8 * μ := by ring

/-- A genuinely nonnegligible last-shell *overshoot* (an explicit additional
hypothesis) cannot be carried at bounded relative radius with vanishing
critical raw kinetic mass R^5 μ. -/
theorem h3Critical_scalar_positiveLastShellOvershoot_forces_frequencyOrMass
    (R Q μ ω η D : ℝ)
    (hR : 0 < R) (hQ : 0 ≤ Q + 1) (hμ : 0 ≤ μ)
    (hD : 0 ≤ D)
    (hOvershoot : η * R ^ 3 ≤ ω)
    (hOver : ω ≤ 4 * (Q + 1) ^ 8 * μ) :
    D * R < Q + 1 ∨ η ≤ 4 * D ^ 8 * R ^ 5 * μ := by
  rcases h3Critical_scalar_lastShellOvershoot_relativeOuter_or_massCost
      R Q μ ω D hR hQ hμ hD hOver with hFar | hCost
  · exact Or.inl hFar
  · right
    have hBound : R ^ 3 * η ≤
        R ^ 3 * (4 * D ^ 8 * R ^ 5 * μ) := by
      calc
        R ^ 3 * η = η * R ^ 3 := by ring
        _ ≤ ω := hOvershoot
        _ ≤ 4 * D ^ 8 * R ^ 8 * μ := hCost
        _ = R ^ 3 * (4 * D ^ 8 * R ^ 5 * μ) := by ring
    by_contra hNot
    have hStrict : 4 * D ^ 8 * R ^ 5 * μ < η := lt_of_not_ge hNot
    have hMultiply := mul_lt_mul_of_pos_left hStrict (pow_pos hR 3)
    exact (not_lt_of_ge hBound) hMultiply

/-- For ANY positive inner radii, a positive normalized last-shell
overshoot that persists eventually and vanishing R^5 raw last-shell mass
force the relative outer cutoff to diverge. A lower overshoot fraction
is a premise, not a consequence of first-crossing minimality. -/
theorem h3Critical_scalar_lastShellCriticalMassVanishing_forces_relativeEscape
    (R Q μ ω : ℕ → ℝ)
    (hR : ∀ k, 0 < R k)
    (hQ : ∀ k, 0 ≤ Q k + 1)
    (hμ : ∀ k, 0 ≤ μ k)
    (hOver : ∀ k, ω k ≤ 4 * (Q k + 1) ^ 8 * μ k)
    (hCritical : Tendsto (fun k => (R k) ^ 5 * μ k) atTop (𝓝 0))
    (η : ℝ) (hη : 0 < η)
    (hOvershoot : ∀ᶠ k : ℕ in atTop, η * (R k) ^ 3 ≤ ω k) :
    Tendsto (fun k => (Q k + 1) / R k) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro A
  let D : ℝ := max A 1
  have hD : 0 ≤ D := le_trans (by norm_num) (le_max_right A 1)
  have hAD : A ≤ D := le_max_left A 1
  have hScaled : Tendsto
      (fun k => 4 * D ^ 8 * ((R k) ^ 5 * μ k))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hCritical.const_mul (4 * D ^ 8)
  have hSmall : ∀ᶠ k : ℕ in atTop,
      4 * D ^ 8 * ((R k) ^ 5 * μ k) < η :=
    hScaled.eventually (eventually_lt_nhds hη)
  filter_upwards [hOvershoot, hSmall] with k hk hkSmall
  have hAlternative := h3Critical_scalar_positiveLastShellOvershoot_forces_frequencyOrMass
    (R k) (Q k) (μ k) (ω k) η D
    (hR k) (hQ k) (hμ k) hD hk (hOver k)
  rcases hAlternative with hFar | hMassCost
  · have hScale : A * R k ≤ D * R k :=
      mul_le_mul_of_nonneg_right hAD (hR k).le
    exact (le_div_iff₀ (hR k)).2 (le_trans hScale hFar.le)
  · have hEq : 4 * D ^ 8 * ((R k) ^ 5 * μ k) =
        4 * D ^ 8 * (R k) ^ 5 * μ k := by ring
    rw [hEq] at hkSmall
    exact False.elim ((not_lt_of_ge hMassCost) hkSmall)

/-- The actual nontrace disjoint MINIMAL-shell and sixth/ninth PDE-rate
witnesses also carry the exact last-shell overshoot/critical-mass
alternative. Under separately stated nonvanishing normalized overshoot
and vanishing critical raw last-shell mass the true selected outer radius
must escape every relative cutoff. There is NO global H3 integrability,
source bound, or artificial re-selection of first-crossing windows. -/
theorem h3Critical_noL2Trace_disjointMinimalShell_criticalRawMassEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N m : ℕ → ℕ, ∃ C δ : ℕ → ℝ,
    ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ, h3CriticalMinimalShellEnergyWindow
        hH3 (t (v k)) (v k) (N (v k)) (m (v k))
        (C (v k)) (δ (v k))) ∧
      (∀ q : ℕ,
        (∑ k ∈ Finset.range q,
          δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤
        ∑ k ∈ Finset.range q,
          (∫ s in t (v k)..(t (v k) + δ (v k)),
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s))) ∧
      ((∀ M : ℝ, ∃ q : ℕ,
        M < ∑ k ∈ Finset.range q,
          δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∨
       (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
         ((v k : ℝ) + 1) ^ 3 * ((T - t (v k)) / 4) ≤ ε ∨
         ((v k : ℝ) + 1) ^ 12 ≤
           512 * ε ^ 2 *
             (2304 * velocityH3EnergyAt u (t (v k)) * (C (v k)) ^ 2 *
               ((N (v k) : ℝ) + 2) ^ 10 + 1) ∨
         ((v k : ℝ) + 1) ^ 9 ≤
           16 * ε ^ 2 *
             (36 * (C (v k)) ^ 2 *
               (((N (v k) : ℝ) + 2) ^ 8 +
                 ((v k : ℝ) + 2) ^ 8) + 1))) ∧
      (∀ k : ℕ,
        0 < h3CriticalMinimalShellOvershoot hH3 (t (v k)) (v k) (N (v k)) ∧
        0 < h3CriticalMinimalLastShellMass hH3 (t (v k)) (m (v k)) (N (v k))) ∧
      (∀ η D : ℝ, 0 < η → 0 ≤ D → ∀ k : ℕ,
        η * (((v k : ℝ) + 1) ^ 3) ≤
          h3CriticalMinimalShellOvershoot hH3 (t (v k)) (v k) (N (v k)) →
        D * ((v k : ℝ) + 1) < ((N (v k) : ℝ) + 2) ∨
        η ≤ 4 * D ^ 8 * (((v k : ℝ) + 1) ^ 5) *
          h3CriticalMinimalLastShellMass hH3 (t (v k)) (m (v k)) (N (v k))) ∧
      (∀ η : ℝ, 0 < η →
        (∀ᶠ k : ℕ in atTop,
          η * (((v k : ℝ) + 1) ^ 3) ≤
            h3CriticalMinimalShellOvershoot hH3 (t (v k)) (v k) (N (v k))) →
        Tendsto (fun k =>
          (((v k : ℝ) + 1) ^ 5) *
            h3CriticalMinimalLastShellMass hH3 (t (v k)) (m (v k)) (N (v k)))
          atTop (𝓝 0) →
        Tendsto (fun k =>
          ((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) atTop atTop) := by
  obtain ⟨t, N, m, C, δ, v, hv, hCofinal, hSeparated, hWindow,
      hSum, hRate⟩ :=
    h3Critical_noL2Trace_disjointMinimalShell_energySourceOuterRateBarrier
      hH3 hClass hNoTrace
  let R : ℕ → ℝ := fun k => (v k : ℝ) + 1
  let Q : ℕ → ℝ := fun k => (N (v k) : ℝ) + 1
  let μ : ℕ → ℝ := fun k =>
    h3CriticalMinimalLastShellMass hH3 (t (v k)) (m (v k)) (N (v k))
  let ω : ℕ → ℝ := fun k =>
    h3CriticalMinimalShellOvershoot hH3 (t (v k)) (v k) (N (v k))
  have hR (k : ℕ) : 0 < R k := by
    dsimp only [R]
    positivity
  have hQ (k : ℕ) : 0 ≤ Q k + 1 := by
    dsimp only [Q]
    positivity
  have hShell (k : ℕ) : 0 < ω k ∧ 0 < μ k ∧
      ω k ≤ 4 * (Q k + 1) ^ 8 * μ k := by
    rcases hWindow k with ⟨_, _, _, _, _, _, _, _, hQuarter,
      _, _, _, _, hMass, hOver⟩
    have hOmega : 0 < ω k := by
      dsimp only [ω, h3CriticalMinimalShellOvershoot]
      linarith only [hQuarter]
    have hMu : 0 < μ k := by
      simpa only [μ, h3CriticalMinimalLastShellMass] using hMass
    have hCost : ω k ≤ 4 * (Q k + 1) ^ 8 * μ k := by
      simpa only [ω, μ, Q, h3CriticalMinimalShellOvershoot,
        h3CriticalMinimalLastShellMass,
        show (N (v k) : ℝ) + 1 + 1 = (N (v k) : ℝ) + 2 by ring]
        using hOver
    exact ⟨hOmega, hMu, hCost⟩
  refine ⟨t, N, m, C, δ, v, hv, hCofinal, hSeparated,
    hWindow, hSum, hRate, ?_, ?_, ?_⟩
  · intro k
    have hs := hShell k
    exact ⟨by simpa only [ω] using hs.1,
      by simpa only [μ] using hs.2.1⟩
  · intro η D hη hD k hOmega
    have hs := hShell k
    have hω : η * (R k) ^ 3 ≤ ω k := by
      simpa only [R, ω] using hOmega
    have hAlt := h3Critical_scalar_positiveLastShellOvershoot_forces_frequencyOrMass
      (R k) (Q k) (μ k) (ω k) η D
      (hR k) (hQ k) hs.2.1.le hD hω hs.2.2
    simpa only [R, Q, μ,
      show (N (v k) : ℝ) + 1 + 1 = (N (v k) : ℝ) + 2 by ring]
      using hAlt
  · intro η hη hOvershoot hMassVanish
    have hOmegaEv : ∀ᶠ k : ℕ in atTop,
        η * (R k) ^ 3 ≤ ω k := by
      simpa only [R, ω] using hOvershoot
    have hMassEv : Tendsto (fun k => (R k) ^ 5 * μ k)
        atTop (𝓝 0) := by
      simpa only [R, μ] using hMassVanish
    have hEscape :=
      h3Critical_scalar_lastShellCriticalMassVanishing_forces_relativeEscape
        R Q μ ω hR hQ (fun k => (hShell k).2.1.le)
        (fun k => (hShell k).2.2) hMassEv η hη hOmegaEv
    have hRatioEq : (fun k : ℕ => (Q k + 1) / R k) =
        (fun k : ℕ => ((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) := by
      funext k
      dsimp only [Q, R]
      rw [show (N (v k) : ℝ) + 1 + 1 = (N (v k) : ℝ) + 2 by ring]
    rw [hRatioEq] at hEscape
    exact hEscape

end
end PrimeTensor.Bridge.Euclidean
