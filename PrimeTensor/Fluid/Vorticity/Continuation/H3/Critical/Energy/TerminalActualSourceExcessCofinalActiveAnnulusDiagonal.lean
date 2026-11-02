import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEveryTailActiveAnnulus
import Mathlib.Tactic

/-!
# Cofinal diagonal of genuinely active physical H³ Fourier annuli

Every inner integer radius has an actual cubic high-radial snapshot on each
strict terminal subtail. The preceding theorem converts it to a FINITE outer
annulus with an EXACT physical projected-source PDE clock and a positive
local dissipation integral. Here a diagonal choice fixes ONE sequence whose
inner cutoff is n+1 and whose snapshots converge to T.

There is NO terminal full-H³ dissipation-integrability assumption. The selected
interval widths and outer frequencies may depend on n and need not be
uniform. The intervals are not yet asserted pairwise disjoint.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Elementary terminal diagonal selection: an every-subtail physical
witness for each n may be selected within 1/(n+1) of T, simultaneously
for all n, without assuming any uniform window size. -/
theorem h3Critical_scalar_everyTailWitness_cofinalDiagonal
    (a T : ℝ) (haT : a < T) (P : ℕ → ℝ → Prop)
    (hEvery : ∀ (n : ℕ) (b : ℝ), b ∈ Set.Ioo a T →
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧ P n t) :
    ∃ t : ℕ → ℝ,
      (∀ n : ℕ, t n ∈ Set.Ioo a T ∧ P n (t n)) ∧
      (∀ n : ℕ, dist (t n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto t atTop (𝓝 T) := by
  classical
  let ε : ℕ → ℝ := fun n => (1 : ℝ) / ((n : ℝ) + 1)
  let b : ℕ → ℝ := fun n => max ((a + T) / 2) (T - ε n)
  have hε (n : ℕ) : 0 < ε n := by
    dsimp only [ε]
    positivity
  have hb (n : ℕ) : b n ∈ Set.Ioo a T := by
    dsimp only [b]
    constructor
    · have hMid : a < (a + T) / 2 := by linarith only [haT]
      exact lt_of_lt_of_le hMid (le_max_left _ _)
    · apply max_lt
      · linarith only [haT]
      · linarith only [hε n]
  have hChoice (n : ℕ) :
      ∃ t : ℝ, t ∈ Set.Ioo (b n) T ∧ P n t :=
    hEvery n (b n) (hb n)
  choose t hSelected using hChoice
  have ht (n : ℕ) : t n ∈ Set.Ioo (b n) T := (hSelected n).1
  have hPt (n : ℕ) : P n (t n) := (hSelected n).2
  have hTail (n : ℕ) : t n ∈ Set.Ioo a T :=
    ⟨lt_trans (hb n).1 (ht n).1, (ht n).2⟩
  have hDist (n : ℕ) : dist (t n) T < ε n := by
    have hNear : T - ε n < t n :=
      lt_of_le_of_lt (le_max_right _ _) (ht n).1
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (ht n).2.le)]
    linarith only [hNear]
  have hInv : Tendsto (fun n : ℕ => ε n) atTop (𝓝 (0 : ℝ)) := by
    dsimp only [ε]
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hNormBound (n : ℕ) : ‖t n - T‖ ≤ ε n := by
    simpa only [Real.norm_eq_abs, Real.dist_eq] using
      (le_of_lt (hDist n))
  have hLimit : Tendsto t atTop (𝓝 T) :=
    (tendsto_iff_norm_sub_tendsto_zero).2
      (squeeze_zero'
        (Filter.Eventually.of_forall (fun n => norm_nonneg (t n - T)))
        (Filter.Eventually.of_forall hNormBound) hInv)
  refine ⟨t, ?_, ?_, hLimit⟩
  · exact fun n => ⟨hTail n, hPt n⟩
  · intro n
    simpa only [ε] using hDist n

/-- One cofinal sequence with INNER cutoff n+1, actual finite outer
cutoffs, selected physical source maxima, exact canonical quadratic-PDE
persistence widths, and positive local annular dissipation costs.
This is genuinely nonvacuous relative to the finite-dissipation branch:
no terminal full-H³ dissipation integral is assumed. -/
theorem h3Critical_noL2Trace_cofinalActiveCubicAnnulusDiagonal
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N : ℕ → ℕ, ∃ C δ : ℕ → ℝ,
      (∀ n : ℕ, t n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (t n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto t atTop (𝓝 T) ∧
      (∀ n : ℕ,
        n ≤ N n ∧ 0 ≤ C n ∧
        C n = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (t n) (t n + (T - t n) / 2) ∧
        0 < δ n ∧ t n + δ n < T ∧
        δ n = h3PathCubicAnnulusQuadraticSharpPDEWidth244
          ((T - t n) / 2)
          ((h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (t n)) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (t n))) -
            ((n : ℝ) + 1) ^ 3 / 2)
          (h3PathFiniteAnnulusPDEVariationCoefficient244
            ((n : ℝ) + 1) ((N n : ℝ) + 1)
            ‖h3AuditActualSpectralVelocityTotal hH3 (t n)‖ (C n))
          (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
            ((n : ℝ) + 1) ((N n : ℝ) + 1) (C n)) ∧
        ‖h3AuditActualSpectralVelocityTotal hH3 (t n)‖ ^ 2 ≤
          velocityH3EnergyAt u (t n) ∧
        (∀ r : ℝ, r ∈ Set.Icc (t n) (t n + δ n) →
          ((n : ℝ) + 1) ^ 3 / 2 <
            h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) ∧
          h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) ≤
            velocityH3DissipationAt u r) ∧
        δ n * (((n : ℝ) + 1) ^ 3 / 2) ≤
          ∫ r in t n..(t n + δ n),
            h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r)) := by
  let P : ℕ → ℝ → Prop := fun n t =>
    ∃ N : ℕ, ∃ C δ : ℝ,
      n ≤ N ∧ 0 ≤ C ∧
      C = h3PathActualProjectedSourceWindowEnvelope244 hH3
        t (t + (T - t) / 2) ∧
      0 < δ ∧ t + δ < T ∧
      δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 ((T - t) / 2)
        ((h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t)) -
          ((n : ℝ) + 1) ^ 3 / 2)
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1)
          ‖h3AuditActualSpectralVelocityTotal hH3 t‖ C)
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) C) ∧
      ‖h3AuditActualSpectralVelocityTotal hH3 t‖ ^ 2 ≤
        velocityH3EnergyAt u t ∧
      (∀ r : ℝ, r ∈ Set.Icc t (t + δ) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) ∧
        h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) ≤
          velocityH3DissipationAt u r) ∧
      δ * (((n : ℝ) + 1) ^ 3 / 2) ≤
        ∫ r in t..(t + δ),
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r)
  have hEvery (n : ℕ) (b : ℝ) (hb : b ∈ Set.Ioo a T) :
      ∃ t : ℝ, t ∈ Set.Ioo b T ∧ P n t := by
    obtain ⟨t, ht, N, C, δ, hnN, hC, hCEq, hδ, hEnd,
      hδEq, hEnergy, hFloor, hCost⟩ :=
      h3Critical_noL2Trace_everyTail_activeCubicPhysicalAnnulus
        hH3 hClass hNoTrace b hb n
    exact ⟨t, ht, N, C, δ, hnN, hC, hCEq, hδ, hEnd,
      hδEq, hEnergy, hFloor, hCost⟩
  obtain ⟨t, ht, hDist, hLimit⟩ :=
    h3Critical_scalar_everyTailWitness_cofinalDiagonal
      a T hClass.terminal_start.2 P hEvery
  have hWitness (n : ℕ) : P n (t n) := (ht n).2
  choose N C δ hData using hWitness
  refine ⟨t, N, C, δ, (fun n => (ht n).1), hDist, hLimit, ?_⟩
  intro n
  exact hData n

end
end PrimeTensor.Bridge.Euclidean
