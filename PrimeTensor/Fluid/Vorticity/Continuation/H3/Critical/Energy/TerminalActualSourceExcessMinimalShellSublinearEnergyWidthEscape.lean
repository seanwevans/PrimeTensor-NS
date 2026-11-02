import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellAveragedKineticRates
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECriticalShellWidthEscape244
import Mathlib.Tactic

/-!
# Sublinear physical H3 anchor energy forces superlinear minimal annulus width

The strict quarter-cubic first-crossing gives R³ < 4 (Q+1)² E₃(t).
For ANY cofinal selected first-crossing sequence, E₃(t_k)/R_k -> 0
therefore implies (Q_k+1)/R_k -> +infinity. As N_k is the genuine
minimal first-crossing outer integer cutoff, its integer width
L_k=N_k-v_k also satisfies L_k/R_k -> +infinity.

This improves the earlier bounded-E₃ criterion: bounded anchor energy is
sufficient but NOT required. Sublinear relative energy is an explicit
conditional hypothesis; no universal energy, source, terminal-clock, or
full-terminal-dissipation bound is claimed.

We retain the SAME width-averaged positive-kinetic shell, exact PDE time
windows, minimal last-shell certificates, certified annular charges and
sixth/ninth source-rate alternative. No independent outer cutoff is chosen.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- An individual quarter-cubic crossing either escapes a proposed relative
outer cutoff D or forces physical H3 anchor energy at least R/(4 D²). -/
theorem h3Critical_scalar_quarterCubic_relativeRadius_or_linearEnergy
    (R Q E D : ℝ)
    (hR : 1 ≤ R) (hRQ : R ≤ Q) (hE : 0 ≤ E)
    (hCross : R ^ 3 < 4 * (Q + 1) ^ 2 * E) :
    D * R < Q + 1 ∨ R < 4 * D ^ 2 * E := by
  by_cases hFar : D * R < Q + 1
  · exact Or.inl hFar
  · right
    exact h3Critical_scalar_quarterCubic_relativeOuter_forces_energyGrowth
      R Q E D hR hRQ hE hCross (le_of_not_gt hFar)

/-- The sharp relative-energy threshold is E_k / R_k, not E_k itself.
Asymptotic sublinearity at a sequence of physical H3 first crossings
forces their outer-to-inner frequency ratio to diverge. -/
theorem h3Critical_scalar_sublinearAnchorEnergy_forces_relativeOuterEscape
    (R Q E : ℕ → ℝ)
    (hR : ∀ k, 1 ≤ R k) (hRQ : ∀ k, R k ≤ Q k)
    (hE : ∀ k, 0 ≤ E k)
    (hCross : ∀ k, (R k) ^ 3 < 4 * (Q k + 1) ^ 2 * E k)
    (hSublinear : Tendsto (fun k => E k / R k) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k => (Q k + 1) / R k) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro A
  let D : ℝ := max A 1
  have hAD : A ≤ D := le_max_left A 1
  have hScaled : Tendsto
      (fun k : ℕ => 4 * D ^ 2 * (E k / R k)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hSublinear.const_mul (4 * D ^ 2)
  have hSmall : ∀ᶠ k : ℕ in atTop,
      4 * D ^ 2 * (E k / R k) < 1 :=
    hScaled.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hSmall] with k hk
  have hPos : 0 < R k := lt_of_lt_of_le zero_lt_one (hR k)
  have hFar : D * R k < Q k + 1 := by
    rcases h3Critical_scalar_quarterCubic_relativeRadius_or_linearEnergy
        (R k) (Q k) (E k) D (hR k) (hRQ k) (hE k) (hCross k)
      with hFar | hGrowth
    · exact hFar
    · have hDiv : 1 < (4 * D ^ 2 * E k) / R k :=
        (lt_div_iff₀ hPos).2 (by simpa only [one_mul] using hGrowth)
      have hRewrite : (4 * D ^ 2 * E k) / R k =
          4 * D ^ 2 * (E k / R k) := by ring
      rw [hRewrite] at hDiv
      exact False.elim ((not_lt_of_ge hk.le) hDiv)
  have hScale : A * R k ≤ D * R k :=
    mul_le_mul_of_nonneg_right hAD hPos.le
  exact (le_div_iff₀ hPos).2 (hScale.trans hFar.le)

/-- The earlier exact physical sixth/ninth alternative, renamed as a
predicate so it can be kept with strengthened SAME-witness geometry. -/
def h3CriticalMinimalShellPhysicalSixthNinthAlternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    (T : ℝ) (t : ℕ → ℝ) (N : ℕ → ℕ) (C δ : ℕ → ℝ)
    (v : ℕ → ℕ) : Prop :=
  (∀ M : ℝ, ∃ q : ℕ,
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
            ((v k : ℝ) + 2) ^ 8) + 1))

/-- Physical disjoint minimal annuli retain the last-shell certificate,
energetic width-averaged Fourier shell, exact PDE windows and certified
sixth/ninth rate alternative. If their anchor energy is sublinear in R,
then BOTH outer frequency and annular integer width escape relative to R.
No finite terminal full-H3 dissipation integral is assumed. -/
theorem h3Critical_noL2Trace_disjointMinimalShell_sublinearEnergyWidthEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N m : ℕ → ℕ, ∃ C δ : ℕ → ℝ,
    ∃ v j : ℕ → ℕ,
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
      h3CriticalMinimalShellPhysicalSixthNinthAlternative (u := u)
        T t N C δ v ∧
      (∀ᶠ k : ℕ in atTop,
        v k ≤ j k ∧ j k < N (v k) ∧
        0 < h3PathActualBandRawKineticMass244
          ((j k : ℝ) + 1) ((j k : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) ∧
      (Tendsto (fun k =>
          velocityH3EnergyAt u (t (v k)) / ((v k : ℝ) + 1))
        atTop (𝓝 0) →
        Tendsto (fun k =>
          ((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) atTop atTop ∧
        Tendsto (fun k =>
          ((N (v k) - v k : ℕ) : ℝ) / ((v k : ℝ) + 1))
          atTop atTop) := by
  obtain ⟨t, N, m, C, δ, v, j, hv, hCofinal, hSeparated,
      hWindows, hSum, hRates, hSelected, _hMassAlt, _hCritical⟩ :=
    h3Critical_noL2Trace_disjointMinimalShell_widthAveragedKineticEnergyRates
      hH3 hClass hNoTrace
  have hRate : h3CriticalMinimalShellPhysicalSixthNinthAlternative (u := u)
      T t N C δ v := hRates
  have hShell : ∀ᶠ k : ℕ in atTop,
      v k ≤ j k ∧ j k < N (v k) ∧
      0 < h3PathActualBandRawKineticMass244
        ((j k : ℝ) + 1) ((j k : ℝ) + 2)
        (h3AuditActualSpectralVelocityTotal hH3 (t (v k))) := by
    filter_upwards [hSelected] with k hk
    exact ⟨hk.1, hk.2.1, hk.2.2.2.1⟩
  refine ⟨t, N, m, C, δ, v, j, hv, hCofinal,
    hSeparated, hWindows, hSum, hRate, hShell, ?_⟩
  intro hSublinear
  let R : ℕ → ℝ := fun k => (v k : ℝ) + 1
  let Q : ℕ → ℝ := fun k => (N (v k) : ℝ) + 1
  let E : ℕ → ℝ := fun k => velocityH3EnergyAt u (t (v k))
  let L : ℕ → ℝ := fun k => ((N (v k) - v k : ℕ) : ℝ)
  have hN (k : ℕ) : v k ≤ N (v k) := by
    have hW := hWindows k
    rcases hW with ⟨hNm, hvm, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
    omega
  have hR (k : ℕ) : 1 ≤ R k := by
    dsimp only [R]
    have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hn]
  have hRQ (k : ℕ) : R k ≤ Q k := by
    have hn : (v k : ℝ) ≤ (N (v k) : ℝ) := by
      exact_mod_cast hN k
    dsimp only [R, Q]
    linarith only [hn]
  have hE (k : ℕ) : 0 ≤ E k := by
    have hW := hWindows k
    rcases hW with ⟨_, _, _, _, _, _, _, hEnergy, _, _, _, _, _, _, _⟩
    dsimp only [E]
    exact (sq_nonneg _).trans hEnergy
  have hCross (k : ℕ) : (R k) ^ 3 < 4 * (Q k + 1) ^ 2 * E k := by
    have hW := hWindows k
    rcases hW with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hPhysical, _, _⟩
    simpa only [R, Q, E,
      show (N (v k) : ℝ) + 1 + 1 = (N (v k) : ℝ) + 2 by ring]
      using hPhysical
  have hSublinear' : Tendsto (fun k => E k / R k)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [E, R] using hSublinear
  have hOuter := h3Critical_scalar_sublinearAnchorEnergy_forces_relativeOuterEscape
    R Q E hR hRQ hE hCross hSublinear'
  have hGeom (k : ℕ) : Q k + 1 ≤ R k + L k + 1 := by
    have hEq : Q k + 1 = R k + L k + 1 := by
      dsimp only [Q, R, L]
      rw [Nat.cast_sub (hN k)]
      ring
    exact hEq.le
  have hWidth := h3Path_relativeShellEscape_forces_relativeWidthEscape244
    R (fun k => Q k + 1) L hR hGeom hOuter
  constructor
  · have hRatioEq : (fun k : ℕ => (Q k + 1) / R k) =
        (fun k : ℕ => ((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) := by
      funext k
      dsimp only [Q, R]
      rw [show (N (v k) : ℝ) + 1 + 1 = (N (v k) : ℝ) + 2 by ring]
    rw [hRatioEq] at hOuter
    exact hOuter
  · simpa only [R, L] using hWidth

end
end PrimeTensor.Bridge.Euclidean
