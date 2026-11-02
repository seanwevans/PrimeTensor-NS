import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellOvershootEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECriticalShellFrequency244
import Mathlib.Tactic

/-!
# Canonical first crossing: a width-averaged energetic shell and actual PDE rates

The final integer shell of a minimal crossing only pays its positive
overshoot, which may be arbitrarily small. An independent width-averaged
integer shell pays a definite share of the entire three-quarter cubic
first-crossing height. Here BOTH shells are synchronized with the exact
physical quadratic-sharp PDE window, actual H3 anchor energy, projected
source, disjoint integral charge and sixth/ninth PDE rate alternative.

No finite full-H3 dissipation integral, global energy ceiling, upper width
cap, or normalized *last*-shell overshoot is assumed. The conditional
critical-mass escape charges the width-averaged shell, not the last shell.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

-- Physical raw kinetic mass uses instances local to the original shell files.
noncomputable local instance axisFintypeMinimalAveragedKineticRates
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMinimalAveragedKineticRates :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Width-averaged cubic kinetic shell costs holding EVENTUALLY suffice for
cofinal relative-frequency escape when the normalized width-weighted shell
mass tends to zero. This avoids assuming an overshoot lower bound on the
last integer shell; exceptional early indices play no role in the limit. -/
theorem h3Critical_scalar_eventualWidthAveragedKineticMass_forces_shellEscape
    (R J L μ : ℕ → ℝ)
    (hR : ∀ k, 0 < R k)
    (hShell : ∀ᶠ k : ℕ in atTop,
      0 ≤ J k ∧ 0 ≤ L k ∧ 0 ≤ μ k ∧
        3 * (R k) ^ 3 / 4 < L k * (4 * (J k) ^ 8 * μ k))
    (hCritical : Tendsto (fun k => L k * (R k) ^ 5 * μ k)
      atTop (𝓝 0)) :
    Tendsto (fun k => J k / R k) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro A
  let D : ℝ := max A 0
  have hD : 0 ≤ D := le_max_right _ _
  have hAD : A ≤ D := le_max_left _ _
  have hScaled : Tendsto
      (fun k : ℕ => 16 * D ^ 8 * (L k * R k ^ 5 * μ k))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hCritical.const_mul (16 * D ^ 8)
  have hSmall : ∀ᶠ k : ℕ in atTop,
      16 * D ^ 8 * (L k * R k ^ 5 * μ k) < 3 :=
    hScaled.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 3))
  filter_upwards [hShell, hSmall] with k hCost hkSmall
  obtain ⟨hJ, hL, hμ, hBig⟩ := hCost
  have hAlt := h3Path_widthShell_nearInner_or_criticalMass244
    (R k) (J k) (L k) (μ k) D (hR k) hJ hL hμ hD hBig
  rcases hAlt with hFar | hMass
  · have hScale : A * R k ≤ D * R k :=
      mul_le_mul_of_nonneg_right hAD (hR k).le
    exact (le_div_iff₀ (hR k)).2 (le_trans hScale hFar.le)
  · have hEq : 16 * D ^ 8 * (L k * R k ^ 5 * μ k) =
        16 * D ^ 8 * L k * R k ^ 5 * μ k := by ring
    rw [hEq] at hkSmall
    exact False.elim (lt_asymm hMass hkSmall)

/-- The actual minimal first-crossing annuli carry TWO distinct physical
shell witnesses: the positive last-shell overshoot, and an energetic
width-averaged shell with a definite cubic charge. Both share the original
H3 anchor, exact source/PDE clock and sixth/ninth energy-source alternative.
The energetic shell has a conditional critical-kinetic-mass frequency escape
without assuming any lower bound on the last-shell overshoot. -/
theorem h3Critical_noL2Trace_disjointMinimalShell_widthAveragedKineticEnergyRates
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
      (∀ᶠ k : ℕ in atTop,
        v k ≤ j k ∧ j k < N (v k) ∧
        3 * (((v k : ℝ) + 1) ^ 3) / 4 <
          ((N (v k) - v k : ℕ) : ℝ) *
            (h3PathActualLowRadialDissipation244 ((j k : ℝ) + 2)
                (h3AuditActualSpectralVelocityTotal hH3 (t (v k))) -
              h3PathActualLowRadialDissipation244 ((j k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) ∧
        0 < h3PathActualBandRawKineticMass244
          ((j k : ℝ) + 1) ((j k : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (t (v k))) ∧
        3 * (((v k : ℝ) + 1) ^ 3) / 4 <
          ((N (v k) - v k : ℕ) : ℝ) *
            (4 * (((j k : ℝ) + 3) ^ 8) *
              h3PathActualBandRawKineticMass244
                ((j k : ℝ) + 1) ((j k : ℝ) + 2)
                (h3AuditActualSpectralVelocityTotal hH3 (t (v k))))) ∧
      (∀ D : ℝ, 0 ≤ D → ∀ᶠ k : ℕ in atTop,
        D * ((v k : ℝ) + 1) < (j k : ℝ) + 3 ∨
        3 < 16 * D ^ 8 * ((N (v k) - v k : ℕ) : ℝ) *
          ((v k : ℝ) + 1) ^ 5 *
          h3PathActualBandRawKineticMass244
            ((j k : ℝ) + 1) ((j k : ℝ) + 2)
            (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) ∧
      (Tendsto (fun k =>
          ((N (v k) - v k : ℕ) : ℝ) * ((v k : ℝ) + 1) ^ 5 *
          h3PathActualBandRawKineticMass244
            ((j k : ℝ) + 1) ((j k : ℝ) + 2)
            (h3AuditActualSpectralVelocityTotal hH3 (t (v k))))
          atTop (𝓝 0) →
        Tendsto (fun k => ((j k : ℝ) + 3) / ((v k : ℝ) + 1))
          atTop atTop) := by
  obtain ⟨t, N, m, C, δ, v, hv, hCofinal, hSeparated,
      hWindows, hSum, hRates⟩ :=
    h3Critical_noL2Trace_disjointMinimalShell_energySourceOuterRateBarrier
      hH3 hClass hNoTrace
  have hTailTime : ∀ᶠ k : ℕ in atTop, a < t (v k) := by
    have hNhds : Set.Ioi a ∈ 𝓝 T :=
      isOpen_Ioi.mem_nhds hClass.terminal_start.2
    exact hCofinal.eventually hNhds
  let P : ℕ → ℕ → Prop := fun k j =>
    v k ≤ j ∧ j < N (v k) ∧
    3 * (((v k : ℝ) + 1) ^ 3) / 4 <
      ((N (v k) - v k : ℕ) : ℝ) *
        (h3PathActualLowRadialDissipation244 ((j : ℝ) + 2)
            (h3AuditActualSpectralVelocityTotal hH3 (t (v k))) -
          h3PathActualLowRadialDissipation244 ((j : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) ∧
    0 < h3PathActualBandRawKineticMass244
      ((j : ℝ) + 1) ((j : ℝ) + 2)
      (h3AuditActualSpectralVelocityTotal hH3 (t (v k))) ∧
    3 * (((v k : ℝ) + 1) ^ 3) / 4 <
      ((N (v k) - v k : ℕ) : ℝ) *
        (4 * (((j : ℝ) + 3) ^ 8) *
          h3PathActualBandRawKineticMass244
            ((j : ℝ) + 1) ((j : ℝ) + 2)
            (h3AuditActualSpectralVelocityTotal hH3 (t (v k))))
  have hChoose (k : ℕ) : ∃ j : ℕ, (a < t (v k) → P k j) := by
    by_cases hta : a < t (v k)
    · obtain ⟨hNm, hnm, _, _, hδ, hEnd, _, _, hGap, hMinimal,
        _, _, _, _, _⟩ := hWindows k
      have hnN : v k ≤ N (v k) := by omega
      have ht : t (v k) ∈ Set.Ioo a T := by
        constructor
        · exact hta
        · linarith only [hδ, hEnd]
      have hCross : 3 * (((v k : ℝ) + 1) ^ 3) / 4 <
          h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (t (v k))) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (t (v k))) := by
        linarith only [hGap]
      obtain ⟨j, hjMin, hjMax, hAvg, hPositive, hKinetic⟩ :=
        h3Path_physicalFirstCrossing_exists_widthAveragedKineticShell244
          hH3 hClass (t (v k)) ht (v k) (N (v k))
          hnN hCross hMinimal
      refine ⟨j, ?_⟩
      intro _
      exact ⟨hjMin, hjMax, hAvg, hPositive, hKinetic⟩
    · exact ⟨0, fun hta' => False.elim (hta hta')⟩
  classical
  choose j hj using hChoose
  have hSelected : ∀ᶠ k : ℕ in atTop, P k (j k) := by
    filter_upwards [hTailTime] with k hk
    exact hj k hk
  let R : ℕ → ℝ := fun k => (v k : ℝ) + 1
  let J : ℕ → ℝ := fun k => (j k : ℝ) + 3
  let L : ℕ → ℝ := fun k => ((N (v k) - v k : ℕ) : ℝ)
  let μ : ℕ → ℝ := fun k =>
    h3PathActualBandRawKineticMass244
      ((j k : ℝ) + 1) ((j k : ℝ) + 2)
      (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))
  have hR (k : ℕ) : 0 < R k := by
    dsimp only [R]
    positivity
  have hShell : ∀ᶠ k : ℕ in atTop,
      0 ≤ J k ∧ 0 ≤ L k ∧ 0 ≤ μ k ∧
        3 * (R k) ^ 3 / 4 < L k * (4 * (J k) ^ 8 * μ k) := by
    filter_upwards [hSelected] with k hk
    obtain ⟨_, _, _, hMass, hBound⟩ := hk
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [J]; positivity
    · dsimp only [L]; exact Nat.cast_nonneg _
    · dsimp only [μ]; exact hMass.le
    · simpa only [R, J, L, μ] using hBound
  refine ⟨t, N, m, C, δ, v, j, hv, hCofinal, hSeparated,
    hWindows, hSum, hRates, ?_, ?_, ?_⟩
  · simpa only [P] using hSelected
  · intro D hD
    filter_upwards [hShell] with k hk
    obtain ⟨hJ, hL, hμ, hCost⟩ := hk
    have hAlt := h3Path_widthShell_nearInner_or_criticalMass244
      (R k) (J k) (L k) (μ k) D
      (hR k) hJ hL hμ hD hCost
    simpa only [R, J, L, μ] using hAlt
  · intro hCritical
    have hCritical' : Tendsto (fun k => L k * (R k) ^ 5 * μ k)
        atTop (𝓝 0) := by
      simpa only [R, L, μ] using hCritical
    have hEscape :=
      h3Critical_scalar_eventualWidthAveragedKineticMass_forces_shellEscape
        R J L μ hR hShell hCritical'
    simpa only [R, J] using hEscape

end
end PrimeTensor.Bridge.Euclidean
