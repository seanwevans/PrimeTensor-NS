import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessGradientTransportBudget
import Mathlib.Tactic

/-!
# Source-window costs force real gradient-energy gap spikes or Riccati energy

The accepted cofinal quintic-source windows carry a finite accounting
alternative: a large Riccati-energy observation on a window, or a cumulative
source-window drain paid by positive physical gradient-energy transport over
strictly separated gaps.

This module converts the latter INTEGRATED requirement into a pointwise
physical obstruction. At any finite stage, if the source charges exceed
initial energy plus a proposed uniform gradient-energy budget over the whole
span, then one of the actual gaps contains a gradient-energy value larger
than the proposed bound. The product spike can further be split into a
large physical H3 energy amplitude or a large canonical gradient coefficient.

No terminal dissipation integral, unproved uniform bound, or global NS
continuation conclusion is assumed.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Finite telescoping identity for adjacent start-time differences. -/
theorem h3Critical_scalar_adjacentGapWidth_telescope
    (start : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ Finset.range m, (start (k + 1) - start k)) =
      start m - start 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- A finite source-window drain that overdraws the initial energy and
an arbitrary constant gap-budget forces either an existing window exception
or a real pointwise spike on one of the very same intervening gaps.
The proof retains the actual finite-gap integral accounting, bounds each
integral by length times a hypothetical ceiling, and telescopes the lengths.
No endpoint or terminal-time integrability is needed. -/
theorem h3Critical_scalar_finiteGapOverdraft_forces_actualSpike
    (start finish cost : ℕ → ℝ) (f : ℝ → ℝ)
    (P : ℕ → Prop) (Einitial R : ℝ)
    (hWindow : ∀ k, start k ≤ finish k)
    (hGap : ∀ k, finish k ≤ start (k + 1))
    (hR : 0 ≤ R)
    (hGapInt : ∀ k,
      IntervalIntegrable f volume (finish k) (start (k + 1)))
    (hAccounting : ∀ m : ℕ,
      (∃ k : ℕ, k ≤ m ∧ P k) ∨
      (∑ k ∈ Finset.range (m + 1), cost k) + 1 ≤
        Einitial + ∑ k ∈ Finset.range m,
          ∫ s in finish k..start (k + 1), f s)
    (m : ℕ)
    (hOverdraft : Einitial + R * (start m - start 0) <
      (∑ k ∈ Finset.range (m + 1), cost k) + 1) :
    (∃ k : ℕ, k ≤ m ∧ P k) ∨
      ∃ k : ℕ, k < m ∧
        ∃ s : ℝ, s ∈ Set.Icc (finish k) (start (k + 1)) ∧ R < f s := by
  rcases hAccounting m with hLarge | hBudget
  · exact Or.inl hLarge
  · by_cases hSpike : ∃ k : ℕ, k < m ∧
        ∃ s : ℝ, s ∈ Set.Icc (finish k) (start (k + 1)) ∧ R < f s
    · exact Or.inr hSpike
    · exfalso
      have hGapCeil (k : ℕ) (hk : k ∈ Finset.range m) :
          (∫ s in finish k..start (k + 1), f s) ≤
            (start (k + 1) - finish k) * R := by
        have hBound : ∀ s : ℝ,
            s ∈ Set.Icc (finish k) (start (k + 1)) → f s ≤ R := by
          intro s hs
          apply le_of_not_gt
          intro hLargeValue
          exact hSpike ⟨k, Finset.mem_range.mp hk, s, hs, hLargeValue⟩
        calc
          (∫ s in finish k..start (k + 1), f s) ≤
              ∫ _s in finish k..start (k + 1), R :=
            intervalIntegral.integral_mono_on
              (hGap k) (hGapInt k) intervalIntegrable_const hBound
          _ = (start (k + 1) - finish k) * R := by simp
      have hWidth (k : ℕ) :
          (start (k + 1) - finish k) * R ≤
            (start (k + 1) - start k) * R := by
        have hLess : start (k + 1) - finish k ≤
            start (k + 1) - start k := by
          linarith only [hWindow k]
        exact mul_le_mul_of_nonneg_right hLess hR
      have hSum :
          (∑ k ∈ Finset.range m,
            ∫ s in finish k..start (k + 1), f s) ≤
          R * (start m - start 0) := by
        calc
          (∑ k ∈ Finset.range m,
              ∫ s in finish k..start (k + 1), f s) ≤
            ∑ k ∈ Finset.range m,
              (start (k + 1) - finish k) * R :=
              Finset.sum_le_sum (fun k hk => hGapCeil k hk)
          _ ≤ ∑ k ∈ Finset.range m,
              (start (k + 1) - start k) * R :=
              Finset.sum_le_sum (fun k _ => hWidth k)
          _ = R * (start m - start 0) := by
              rw [← Finset.sum_mul,
                h3Critical_scalar_adjacentGapWidth_telescope]
              ring
      have hTooBig :
          (∑ k ∈ Finset.range (m + 1), cost k) + 1 ≤
            Einitial + R * (start m - start 0) :=
        hBudget.trans (add_le_add_right hSum Einitial)
      exact (not_lt_of_ge hTooBig) hOverdraft

/-- A large nonnegative product forces its energy factor or its gradient
coefficient above a proposed separate ceiling. -/
theorem h3Critical_scalar_positiveProductSpike_split
    (C U c E : ℝ) (_hC : 0 ≤ C) (hU : 0 ≤ U)
    (hc : 0 ≤ c)
    (hSpike : C * U < c * E) : U < E ∨ C < c := by
  by_cases hEnergy : U < E
  · exact Or.inl hEnergy
  · right
    apply lt_of_not_ge
    intro hCoeff
    have hE : E ≤ U := le_of_not_gt hEnergy
    have hFirst : c * E ≤ c * U :=
      mul_le_mul_of_nonneg_left hE hc
    have hSecond : c * U ≤ C * U :=
      mul_le_mul_of_nonneg_right hCoeff hU
    exact (not_lt_of_ge (hFirst.trans hSecond)) hSpike

/-- The ORIGINAL cofinal quintic source windows obey a genuinely physical
finite-scale trichotomy. If their enhanced dissipation charges exceed the
initial energy plus the length times proposed coefficient/energy ceilings,
then either a Riccati-energy witness already exists on a source window,
or an intervening physical gap has energy above U, or its CANONICAL
H3 gradient transport coefficient above C.

This theorem does not assert the overdraft occurs or bound the resulting
energy/gradient spike. No terminal-wide integrability hypothesis is added. -/
theorem h3Critical_noL2Trace_cofinalQuintic_gradientEnergyGapSpike
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ M q : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hM : ∀ n, 0 ≤ M n)
    (hq : ∀ n, 0 < q n) :
    ∃ t : ℕ → ℝ, ∃ v : ℕ → ℕ, ∃ δ : ℕ → ℝ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k : ℕ, 0 < δ k ∧ t (v k) + δ k < t (v (k + 1))) ∧
      (∀ m : ℕ, ∀ C U : ℝ, 0 ≤ C → 0 ≤ U →
        velocityH3EnergyAt u (t (v 0)) +
          (C * U) * (t (v m) - t (v 0)) <
          (∑ k ∈ Finset.range (m + 1),
            h3CriticalSourceExcessEnhancedFloor
              (M (v k)) (q (v k)) * δ k) + 1 →
        (∃ k : ℕ, k ≤ m ∧
          ∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
              h3PathSqrtEnergyRiccatiCoefficient *
                Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
        ∃ k : ℕ, k < m ∧
          ∃ s : ℝ, s ∈ Set.Icc (t (v k) + δ k) (t (v (k + 1))) ∧
            (U < velocityH3EnergyAt u s ∨
              C < 4422 * (1 +
                |h3PathCanonicalSqrtEnergyGradientEnvelope u s|))) := by
  obtain ⟨t, v, δ, hv, hLimit, hGaps, hInt, hWindowAlt, hAccounting⟩ :=
    h3Critical_noL2Trace_cofinalQuintic_gradientTransportBudget
      hH3 hClass b hb hNoTrace c ρ σ M q hc hcLimit hρ hσ hM hq
  let start : ℕ → ℝ := fun k => t (v k)
  let finish : ℕ → ℝ := fun k => t (v k) + δ k
  let cost : ℕ → ℝ := fun k =>
    h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) * δ k
  let P : ℕ → Prop := fun k =>
    ∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
      h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
        h3PathSqrtEnergyRiccatiCoefficient *
          Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s
  let f : ℝ → ℝ := fun s =>
    (4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|)) *
      velocityH3EnergyAt u s
  have hWindow (k : ℕ) : start k ≤ finish k := by
    dsimp only [start, finish]
    exact le_add_of_nonneg_right (hGaps k).1.le
  have hGap (k : ℕ) : finish k ≤ start (k + 1) := by
    dsimp only [start, finish]
    exact (hGaps k).2.le
  have hGapInt (k : ℕ) :
      IntervalIntegrable f volume (finish k) (start (k + 1)) := by
    dsimp only [f, finish, start]
    exact hInt k
  have hScalarAccounting (m : ℕ) :
      (∃ k : ℕ, k ≤ m ∧ P k) ∨
      (∑ k ∈ Finset.range (m + 1), cost k) + 1 ≤
        velocityH3EnergyAt u (start 0) +
          ∑ k ∈ Finset.range m,
            ∫ s in finish k..start (k + 1), f s := by
    dsimp only [start, finish, cost, f, P]
    exact hAccounting m
  refine ⟨t, v, δ, hv, hLimit, hGaps, ?_⟩
  intro m C U hC hU hOverdraft
  have hOverdraftScalar :
      velocityH3EnergyAt u (start 0) +
        (C * U) * (start m - start 0) <
          (∑ k ∈ Finset.range (m + 1), cost k) + 1 := by
    simpa only [start, cost] using hOverdraft
  have hResult :=
    h3Critical_scalar_finiteGapOverdraft_forces_actualSpike
      start finish cost f P (velocityH3EnergyAt u (start 0))
      (C * U) hWindow hGap (mul_nonneg hC hU)
      hGapInt hScalarAccounting m hOverdraftScalar
  rcases hResult with hLarge | ⟨k, hk, s, hs, hSpike⟩
  · exact Or.inl hLarge
  · right
    refine ⟨k, hk, s, hs, ?_⟩
    have hCoeff : 0 ≤ 4422 *
        (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|) := by
      positivity
    exact h3Critical_scalar_positiveProductSpike_split
      C U (4422 * (1 + |h3PathCanonicalSqrtEnergyGradientEnvelope u s|))
      (velocityH3EnergyAt u s) hC hU hCoeff hSpike

end
end PrimeTensor.Bridge.Euclidean
