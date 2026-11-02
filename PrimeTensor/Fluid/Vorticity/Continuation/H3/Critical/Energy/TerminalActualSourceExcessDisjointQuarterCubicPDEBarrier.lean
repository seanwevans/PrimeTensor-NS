import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessDisjointAnnularQuadraticRateBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEveryTailActiveAnnulus
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessCofinalActiveAnnulusDiagonal
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointWindows244
import Mathlib.Tactic

/-!
# Quarter-cubic physical annuli and sixth/ninth-order PDE barriers

This construction preserves the strict quarter-cubic annular surplus from the
actual first-crossing outer cutoff. The earlier every-tail constructor proved
this surplus internally but omitted it from its exported witness. We expose it,
diagonalize on all terminal subintervals, and extract pairwise disjoint exact
physical PDE intervals. The nonintegrable terminal-dissipation branch is kept:
no global full-H3 L1 bound is assumed. The charge divergence or sharp PDE
concentration alternatives apply to the SAME selected physical windows.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- On every terminal subtail, at every specified inner integer frequency,
there is a genuinely ACTIVE finite physical Fourier annulus. Its exact
PDE-controlled width is selected using the physical projected-source
maximum, and its annular cost is a real positive-time integral. Neither a
full terminal H3 dissipation budget nor a positive terminal kinetic limit
is assumed. -/
theorem h3Critical_noL2Trace_everyTail_activeQuarterCubicPhysicalAnnulus
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (b : ℝ) (hb : b ∈ Set.Ioo a T) (n : ℕ) :
    ∃ t : ℝ, t ∈ Set.Ioo b T ∧
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
        ((n : ℝ) + 1) ^ 3 / 4 <
          (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 t) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 t)) -
            ((n : ℝ) + 1) ^ 3 / 2 ∧
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
              (h3AuditActualSpectralVelocityTotal hH3 r) := by
  obtain ⟨t, ht, hSpike⟩ :=
    h3Critical_noL2Trace_highRadialDissipation_spikes_everyFixedRadius
      hH3 hClass hNoTrace b hb ((n : ℝ) + 1)
      (by positivity) (((n : ℝ) + 1) ^ 3)
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hb.1 ht.1, ht.2⟩
  obtain ⟨N, C, δ, hnN, hC, hCEq, _hAttained,
      hδ, hEnd, hδEq, hFloor, hKinetic, _hProduct,
      hQuarter, _hMinimal⟩ :=
    h3Path_cubicHighSnapshot_has_exactAnchorCanonicalClock244
      hH3 hClass t htClass n hSpike
  let B : ℝ → ℝ := fun r =>
    h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 r) -
    h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 r)
  have hR : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hQ : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  have hSub : Set.Icc t (t + δ) ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_of_lt_of_le htClass.1 hr.1, lt_of_le_of_lt hr.2 hEnd⟩
  have hContinuous : ContinuousOn B (Set.Ioo a T) := by
    exact h3Path_finiteAnnularDissipation_continuousOn244
      hH3 hClass ((n : ℝ) + 1) ((N : ℝ) + 1) hR hQ
  have hIntegrable : IntervalIntegrable B volume t (t + δ) :=
    (hContinuous.mono hSub).intervalIntegrable_of_Icc
      (le_add_of_nonneg_right hδ.le)
  have hCost : δ * (((n : ℝ) + 1) ^ 3 / 2) ≤
      ∫ r in t..(t + δ), B r := by
    have hFromFloor := h3Path_localPositiveHeight_forces_integratedCost244
      B t (t + δ) (((n : ℝ) + 1) ^ 3 / 2)
      (by linarith only [hδ]) hIntegrable
      (fun r hr => (hFloor r hr).le)
    calc
      δ * (((n : ℝ) + 1) ^ 3 / 2) =
          ((t + δ) - t) * (((n : ℝ) + 1) ^ 3 / 2) := by ring
      _ ≤ ∫ r in t..(t + δ), B r := hFromFloor
  have hFull (r : ℝ) (hr : r ∈ Set.Icc t (t + δ)) :
      B r ≤ velocityH3DissipationAt u r := by
    exact h3Path_actualFiniteAnnulusDissipation_le_fullAt244
      hH3 hClass r (hSub hr) ((n : ℝ) + 1) ((N : ℝ) + 1)
  refine ⟨t, ht, N, C, δ, hnN, hC, hCEq,
    hδ, hEnd, hδEq, hKinetic, hQuarter, ?_, ?_⟩
  · intro r hr
    exact ⟨hFloor r hr, hFull r hr⟩
  · exact hCost


/-- One cofinal sequence with INNER cutoff n+1, actual finite outer
cutoffs, selected physical source maxima, exact canonical quadratic-PDE
persistence widths, and positive local annular dissipation costs.
This is genuinely nonvacuous relative to the finite-dissipation branch:
no terminal full-H³ dissipation integral is assumed. -/
theorem h3Critical_noL2Trace_cofinalQuarterCubicAnnulusDiagonal
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
        ((n : ℝ) + 1) ^ 3 / 4 <
          (h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (t n)) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (t n))) -
            ((n : ℝ) + 1) ^ 3 / 2 ∧
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
      ((n : ℝ) + 1) ^ 3 / 4 <
        (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t)) -
          ((n : ℝ) + 1) ^ 3 / 2 ∧
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
      hδEq, hEnergy, hQuarter, hFloor, hCost⟩ :=
      h3Critical_noL2Trace_everyTail_activeQuarterCubicPhysicalAnnulus
        hH3 hClass hNoTrace b hb n
    exact ⟨t, ht, N, C, δ, hnN, hC, hCEq, hδ, hEnd,
      hδEq, hEnergy, hQuarter, hFloor, hCost⟩
  obtain ⟨t, ht, hDist, hLimit⟩ :=
    h3Critical_scalar_everyTailWitness_cofinalDiagonal
      a T hClass.terminal_start.2 P hEvery
  have hWitness (n : ℕ) : P n (t n) := (ht n).2
  choose N C δ hData using hWitness
  refine ⟨t, N, C, δ, (fun n => (ht n).1), hDist, hLimit, ?_⟩
  intro n
  exact hData n

/-- The same strictly separated physical annuli have an actual quarter-cubic
surplus. Their unbounded certified charges or, for every positive tolerance,
terminal clock compression / sixth-order linear PDE rate / ninth-order
quadratic PDE rate, is a nonintegrable-branch alternative. -/
theorem h3Critical_noL2Trace_disjointQuarterCubicAnnuli_unboundedCharge_or_sixthNinth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N : ℕ → ℕ, ∃ C δ : ℕ → ℝ, ∃ v : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ,
        k ≤ v k ∧ 0 ≤ C (v k) ∧ 0 < δ (v k) ∧
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 t N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (t (v k)) (t (v k) + (T - t (v k)) / 2) ∧
        δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
          ((T - t (v k)) / 2)
          (h3PathCubicAnnulusActualGap244 hH3 t N (v k))
          (h3PathFiniteAnnulusPDEVariationCoefficient244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
            ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ (C (v k)))
          (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))) ∧
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) ≤
          ∫ r in t (v k)..(t (v k) + δ (v k)),
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤
        ∑ k ∈ Finset.range m,
          (∫ r in t (v k)..(t (v k) + δ (v k)),
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 r))) ∧
      ((∀ M : ℝ, ∃ m : ℕ,
        M < ∑ k ∈ Finset.range m,
          δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∨
       (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
         ((v k : ℝ) + 1) ^ 3 * ((T - t (v k)) / 4) ≤ ε ∨
         ((v k : ℝ) + 1) ^ 6 ≤
           16 * ε *
             (h3PathFiniteAnnulusPDEVariationCoefficient244
               ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
               ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖
               (C (v k)) + 1) ∨
         ((v k : ℝ) + 1) ^ 9 ≤
           16 * ε ^ 2 *
             (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
               ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k)) + 1))) := by
  obtain ⟨t, N, C, δ, hTimes, _hDist, hLimit, hWindows⟩ :=
    h3Critical_noL2Trace_cofinalQuarterCubicAnnulusDiagonal
      hH3 hClass hNoTrace
  have hδ (n : ℕ) : 0 < δ n := by
    obtain ⟨_, _, _, hPositive, _, _, _, _, _, _⟩ := hWindows n
    exact hPositive
  have hEnd (n : ℕ) : t n + δ n < T := by
    obtain ⟨_, _, _, _, hBefore, _, _, _, _, _⟩ := hWindows n
    exact hBefore
  obtain ⟨v, hMono, hCofinal, hSeparated⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      t δ T hLimit hδ hEnd
  have hIndex (k : ℕ) : k ≤ v k := by
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
        exact Nat.succ_le_of_lt
          (lt_of_le_of_lt ih (hMono (Nat.lt_succ_self k)))
  let K : ℕ → ℝ := fun n =>
    ‖h3AuditActualSpectralVelocityTotal hH3 (t n)‖
  let b : ℕ → ℝ := fun n => (T - t n) / 2
  let gap : ℕ → ℝ := fun n => h3PathCubicAnnulusActualGap244 hH3 t N n
  let Λ : ℕ → ℝ := fun n => h3PathCubicAnnulusActualLinearRate244 N K C n
  let Ξ : ℕ → ℝ := fun n => h3PathCubicAnnulusActualQuadraticRate244 N C n
  have hSelected (k : ℕ) :
      k ≤ v k ∧ 0 ≤ C (v k) ∧ 0 < δ (v k) ∧
      ((v k : ℝ) + 1) ^ 3 / 4 <
        h3PathCubicAnnulusActualGap244 hH3 t N (v k) ∧
      C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
        (t (v k)) (t (v k) + (T - t (v k)) / 2) ∧
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        ((T - t (v k)) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 t N (v k))
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
          ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ (C (v k)))
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))) ∧
      δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) ≤
        ∫ r in t (v k)..(t (v k) + δ (v k)),
          h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 r) := by
    obtain ⟨_, hC, hCEq, hPositive, _, hExact, _, hQuarter, _, hCost⟩ :=
      hWindows (v k)
    refine ⟨hIndex k, hC, hPositive, ?_, hCEq, ?_, hCost⟩
    · simpa only [h3PathCubicAnnulusActualGap244] using hQuarter
    · simpa only [h3PathCubicAnnulusActualGap244] using hExact
  have hExact (k : ℕ) :
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k)) := by
    obtain ⟨_, _, _, _, _, hWidth, _⟩ := hSelected k
    simpa only [b, gap, Λ, Ξ, K,
      h3PathCubicAnnulusActualGap244,
      h3PathCubicAnnulusActualLinearRate244,
      h3PathCubicAnnulusActualQuadraticRate244] using hWidth
  have hQuarter (k : ℕ) :
      ((v k : ℝ) + 1) ^ 3 / 4 ≤ gap (v k) := by
    exact le_of_lt (by simpa only [gap] using (hSelected k).2.2.2.1)
  have hLinearNonneg (k : ℕ) : 0 ≤ Λ (v k) := by
    dsimp only [Λ, h3PathCubicAnnulusActualLinearRate244]
    exact h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
      (K (v k)) (C (v k)) (norm_nonneg _) (hSelected k).2.1
  have hQuadraticNonneg (k : ℕ) : 0 ≤ Ξ (v k) := by
    dsimp only [Ξ, h3PathCubicAnnulusActualQuadraticRate244]
    exact h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))
  have hAlt := h3Critical_scalar_disjointQuadraticSharpCharges_unbounded_or_sixthNinth
    v δ b gap Λ Ξ hMono (fun k => (hSelected k).2.2.1.le)
    hExact (Filter.Eventually.of_forall hQuarter)
    (Filter.Eventually.of_forall hLinearNonneg)
    (Filter.Eventually.of_forall hQuadraticNonneg)
  let I : ℕ → ℝ := fun k =>
    ∫ r in t (v k)..(t (v k) + δ (v k)),
      h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 r) -
      h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 r)
  have hCosts (k : ℕ) :
      δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) ≤ I k :=
    (hSelected k).2.2.2.2.2.2
  have hSum (m : ℕ) :
      (∑ k ∈ Finset.range m,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤
      ∑ k ∈ Finset.range m, I k :=
    h3Critical_scalar_finiteAnnularChargeSum_le_actualIntegralSum
      v δ I hCosts m
  refine ⟨t, N, C, δ, v,
    hMono, hCofinal, hSeparated, hSelected, ?_, ?_⟩
  · intro m
    simpa only [I] using hSum m
  · rcases hAlt with hUnbounded | hCaps
    · exact Or.inl hUnbounded
    · right
      intro ε hε
      filter_upwards [hCaps ε hε] with k hk
      rcases hk with hTime | hLinear | hQuadratic
      · left
        change ((v k : ℝ) + 1) ^ 3 * (((T - t (v k)) / 2) / 2) ≤ ε at hTime
        convert hTime using 1 <;> ring
      · exact Or.inr (Or.inl (by
          simpa only [Λ, K, h3PathCubicAnnulusActualLinearRate244]
            using hLinear))
      · exact Or.inr (Or.inr (by
          simpa only [Ξ, h3PathCubicAnnulusActualQuadraticRate244]
            using hQuadratic))

end
end PrimeTensor.Bridge.Euclidean
