import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDESuperlinearOuterCutoff244
import Mathlib.Tactic

/-!
# First-crossing outer annular radii for quadratic-sharp physical PDE clocks

A lower bound on an arbitrarily selected outer Fourier cutoff can be
artificially inflated by enlarging that cutoff. This module makes the
outer radius canonical: it is the least integer whose actual weighted
H³ annular dissipation first passes three quarters of the inner cubic
height. The same minimal radius is then used in the exact physical PDE
clock, before source ceilings and temporal widths are selected.

Minimality is a genuine restriction on the spectral distribution, not a
new upper bound or a regularity claim. Finite terminal H³ dissipation
remains an explicit hypothesis for the final disjoint-window statement.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A high-radial cubic snapshot admits a *least* outer cutoff crossing
three-quarter cubic annular dissipation. Every smaller admissible
outer cutoff fails the strict three-quarter threshold. -/
theorem h3Path_cubicHighSnapshot_has_minimalOuterAnnulus244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (n : ℕ)
    (hCube : ((n : ℝ) + 1) ^ 3 <
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) :
    ∃ N : ℕ,
      n ≤ N ∧
      3 * (((n : ℝ) + 1) ^ 3) / 4 <
        h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) -
        h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 t) ∧
      (∀ m : ℕ, n ≤ m → m < N →
        h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) ≤
            3 * (((n : ℝ) + 1) ^ 3) / 4) := by
  let P : ℕ → Prop := fun m =>
    n ≤ m ∧
    3 * (((n : ℝ) + 1) ^ 3) / 4 <
      h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)
  have hExists : ∃ m : ℕ, P m := by
    obtain ⟨m, hmn, hm⟩ :=
      h3Path_cubicHighSnapshot_has_finiteAnnularHeight244
        hH3 hClass t ht n hCube
    exact ⟨m, hmn, hm⟩
  let N : ℕ := Nat.find hExists
  have hSpec : P N := Nat.find_spec hExists
  refine ⟨N, hSpec.1, hSpec.2, ?_⟩
  intro m hnm hmN
  have hNot : ¬ P m := Nat.find_min hExists hmN
  exact le_of_not_gt (fun h => hNot ⟨hnm, h⟩)

/-- The quadratic-sharp PDE window is built from the least possible
finite-annulus cutoff, rather than an arbitrary enlargement. -/
theorem h3Path_cubicHighSnapshot_has_minimalQuadraticSharpClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (n : ℕ)
    (hCube : ((n : ℝ) + 1) ^ 3 <
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) :
    ∃ (N : ℕ) (K C δ : ℝ),
      n ≤ N ∧ 0 ≤ K ∧ 0 ≤ C ∧ 0 < δ ∧ t + δ < T ∧
      (δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 ((T - t) / 2)
        ((h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t)) -
          ((n : ℝ) + 1) ^ 3 / 2)
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) K C)
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) C)) ∧
      (∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      ((n : ℝ) + 1) ^ 3 / 4 <
        (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t)) -
          ((n : ℝ) + 1) ^ 3 / 2 ∧
      (∀ m : ℕ, n ≤ m → m < N →
        h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) ≤
            3 * (((n : ℝ) + 1) ^ 3) / 4) := by
  obtain ⟨N, hnN, hHeight, hMinimal⟩ :=
    h3Path_cubicHighSnapshot_has_minimalOuterAnnulus244
      hH3 hClass t ht n hCube
  let R : ℝ := (n : ℝ) + 1
  let Q : ℝ := (N : ℝ) + 1
  let A : ℝ := R ^ 3 / 2
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let K : ℝ := ‖G‖
  let B : ℝ :=
    h3PathActualLowRadialDissipation244 Q G -
      h3PathActualLowRadialDissipation244 R G
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hK : 0 ≤ K := norm_nonneg G
  have hBase : ∀ j : Fin 3, ‖G j‖ ≤ K := by
    intro j
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg G)).1 le_rfl j
  have hCubePos : 0 < R ^ 3 := by dsimp only [R]; positivity
  have hHeight' : 3 * R ^ 3 / 4 < B := by
    simpa only [R, Q, B, G] using hHeight
  have hQuarter : R ^ 3 / 4 < B - A := by
    dsimp only [A]
    linarith only [hHeight']
  have hGap : 0 < B - A := by
    linarith only [hQuarter, hCubePos]
  let b : ℝ := (T - t) / 2
  have hb : 0 < b := by dsimp only [b]; linarith only [ht.2]
  have ht0 : 0 < t := lt_trans hClass.terminal_start.1 ht.1
  have htb : t < t + b := by linarith only [hb]
  have hbT : t + b < T := by
    dsimp only [b]
    linarith only [ht.2]
  obtain ⟨C, hC, hSource⟩ :=
    h3Path_actualProjectedMomentumSource_uniformL2OnStrict244
      hH3 ht0 htb hbT
  let Λ : ℝ := h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C
  let Ξ : ℝ := h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C
  have hΛ : 0 ≤ Λ :=
    h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244 R Q K C hK hC
  have hΞ : 0 ≤ Ξ :=
    h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244 R Q C
  obtain ⟨δ, hExact, hδ, hδb, _hδone, hBudget⟩ :=
    h3Path_cubicAnnulusQuadraticSharpPDEWidth_valid244
      b (B - A) Λ Ξ hb hGap hΛ hΞ
  have hEnd : t + δ < T := by linarith only [hδb, hbT]
  have hSourceWindow : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C := by
    intro s hs
    apply hSource s
    constructor
    · exact hs.1
    · linarith only [hs.2, hδb]
  have hFinal :=
    h3Path_actualFiniteAnnulus_integratedCost_of_anchoredPDE244
      hH3 hClass R Q K C A t δ hR hQ hK hA ht hδ hEnd
      hBase hSourceWindow (show A < B from sub_pos.mp hGap) hBudget
  refine ⟨N, K, C, δ, hnN, hK, hC, hδ, hEnd, ?_, hFinal.1, ?_, hMinimal⟩
  · change δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 b (B - A) Λ Ξ
    exact hExact
  · change R ^ 3 / 4 < B - A
    exact hQuarter

/-- The physical no-terminal-trace snapshots inherit minimal
three-quarter cubic outer cutoffs on all natural indices. -/
theorem h3Path_noL2Trace_forces_minimalQuadraticSharpClocks244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ),
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        n ≤ N n ∧ 0 ≤ K n ∧ 0 ≤ C n ∧ 0 < δ n ∧
        τ n + δ n < T ∧
        δ n = h3PathCubicAnnulusQuadraticSharpPDEWidth244 ((T - τ n) / 2)
          (h3PathCubicAnnulusActualGap244 hH3 τ N n)
          (h3PathCubicAnnulusActualLinearRate244 N K C n)
          (h3PathCubicAnnulusActualQuadraticRate244 N C n) ∧
        (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ n) →
          ((n : ℝ) + 1) ^ 3 / 2 <
            h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        ((n : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N n ∧
        (∀ m : ℕ, n ≤ m → m < N n →
          h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ≤
              3 * (((n : ℝ) + 1) ^ 3) / 4)) := by
  obtain ⟨τ, hτ, _hNear, hLimit, hCube⟩ :=
    h3Path_physicalNoL2Trace_forces_highRadialCubicDissipationSequence244
      hH3 hClass hMass hNoTrace
  have hChoice (n : ℕ) : ∃ (N : ℕ) (K C δ : ℝ),
      n ≤ N ∧ 0 ≤ K ∧ 0 ≤ C ∧ 0 < δ ∧ τ n + δ < T ∧
      (δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 ((T - τ n) / 2)
        ((h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) -
          ((n : ℝ) + 1) ^ 3 / 2)
        (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) K C)
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) C)) ∧
      (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ) →
        ((n : ℝ) + 1) ^ 3 / 2 <
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
      ((n : ℝ) + 1) ^ 3 / 4 <
        (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) -
          ((n : ℝ) + 1) ^ 3 / 2 ∧
      (∀ m : ℕ, n ≤ m → m < N →
        h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) ≤
            3 * (((n : ℝ) + 1) ^ 3) / 4) :=
    h3Path_cubicHighSnapshot_has_minimalQuadraticSharpClock244
      hH3 hClass (τ n) (hτ n) n (hCube n)
  choose N K C δ hAll using hChoice
  refine ⟨τ, N, K, C, δ, hτ, hLimit, ?_⟩
  intro n
  rcases hAll n with ⟨hnN, hK, hC, hδ, hEnd, hExact, hFloor, hGap, hMinimal⟩
  exact ⟨hnN, hK, hC, hδ, hEnd,
    (by simpa only [h3PathCubicAnnulusActualGap244,
      h3PathCubicAnnulusActualLinearRate244,
      h3PathCubicAnnulusActualQuadraticRate244] using hExact),
    hFloor, (by simpa only [h3PathCubicAnnulusActualGap244] using hGap), hMinimal⟩

/-- The finite-dissipation three-scale alternative holds with
first-crossing cutoffs, so growth of these radii cannot be manufactured
by choosing an unnecessarily distant annulus. -/
theorem h3Path_noL2Trace_finiteDissipation_minimalQuadraticSharpThreeScale244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ,
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N (v k)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k m : ℕ, v k ≤ m → m < N (v k) →
        h3PathActualLowRadialDissipation244 ((m : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
          h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ≤
            3 * (((v k : ℝ) + 1) ^ 3) / 4) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ≤ ε ∨
        ((v k : ℝ) + 1) ^ 6 ≤
          16 * ε * (h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1) ∨
        ((v k : ℝ) + 1) ^ 9 ≤
          16 * ε ^ 2 *
            (h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1)) := by
  obtain ⟨τ, N, K, C, δ, hTime, hLimit, hAll⟩ :=
    h3Path_noL2Trace_forces_minimalQuadraticSharpClocks244
      hH3 hClass hMass hNoTrace
  have hδ (n : ℕ) : 0 < δ n := by
    rcases hAll n with ⟨_, _, _, hp, _, _, _, _, _⟩
    exact hp
  have hEnd (n : ℕ) : τ n + δ n < T := by
    rcases hAll n with ⟨_, _, _, _, he, _, _, _, _⟩
    exact he
  obtain ⟨v, hv, hCofinal, hSeparate⟩ :=
    h3Path_exists_strictMono_pairwiseSeparatedTerminalWindows244
      τ δ T hLimit hδ hEnd
  let M : ℝ := ∫ r in a..T, velocityH3DissipationAt u r
  have hBound : ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤ M := by
    have hFloor (k : ℕ) (r : ℝ)
        (hr : r ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k))) :
        ((v k : ℝ) + 1) ^ 3 / 2 ≤ velocityH3DissipationAt u r := by
      rcases hAll (v k) with ⟨_, _, _, _, hb, _, hAnnulus, _, _⟩
      have hrClass : r ∈ Set.Ioo a T :=
        ⟨lt_of_lt_of_le (hTime (v k)).1 hr.1,
          lt_of_le_of_lt hr.2 hb⟩
      exact (hAnnulus r hr).le.trans
        (h3Path_actualFiniteAnnulusDissipation_le_fullAt244
          hH3 hClass r hrClass ((v k : ℝ) + 1)
            ((N (v k) : ℝ) + 1))
    have hSum := h3Path_disjointNonnegativeWindows_finiteHeightCost_le244
      (velocityH3DissipationAt u) a T
      (fun k => τ (v k)) (fun k => δ (v k))
      (fun k => ((v k : ℝ) + 1) ^ 3 / 2)
      hClass.terminal_start.2.le
      (fun r => velocityH3DissipationAt_nonneg u r)
      hDInt
      (fun k => (hTime (v k)).1.le)
      (fun k => (hδ (v k)).le)
      (fun k => (hEnd (v k)).le)
      (fun k => (hSeparate k (k + 1) (Nat.lt_succ_self k)).le)
      hFloor
    simpa only [M] using hSum
  have hΛ (n : ℕ) :
      0 ≤ h3PathCubicAnnulusActualLinearRate244 N K C n := by
    unfold h3PathCubicAnnulusActualLinearRate244
    rcases hAll n with ⟨_, hK, hC, _, _, _, _, _, _⟩
    exact h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
      ((n : ℝ) + 1) ((N n : ℝ) + 1) (K n) (C n) hK hC
  have hΞ (n : ℕ) :
      0 ≤ h3PathCubicAnnulusActualQuadraticRate244 N C n := by
    unfold h3PathCubicAnnulusActualQuadraticRate244
    exact h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244
      ((n : ℝ) + 1) ((N n : ℝ) + 1) (C n)
  have hExact (k : ℕ) :
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        ((T - τ (v k)) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
        (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
        (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)) := by
    exact (hAll (v k)).2.2.2.2.2.1
  let f : ℕ → ℝ := fun k =>
    δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)
  have hf (k : ℕ) : 0 ≤ f k := by
    dsimp only [f]
    exact mul_nonneg (hδ (v k)).le (by positivity)
  have hSummable : Summable f :=
    h3Path_nonnegativeBoundedRangeSums_summable244 f M hf
      (by simpa only [f] using hBound)
  have hCollapse : Tendsto (fun k : ℕ =>
      δ (v k) * ((v k : ℝ) + 1) ^ 3) atTop (𝓝 0) := by
    have hTwice := hSummable.tendsto_atTop_zero.const_mul (2 : ℝ)
    have hEq : (fun k : ℕ =>
        δ (v k) * ((v k : ℝ) + 1) ^ 3) =
        (fun k : ℕ => 2 * f k) := by
      funext k
      dsimp only [f]
      ring
    rw [hEq]
    simpa only [mul_zero] using hTwice
  have hQuarter : ∀ᶠ k : ℕ in atTop,
      ((v k : ℝ) + 1) ^ 3 / 4 ≤
        h3PathCubicAnnulusActualGap244 hH3 τ N (v k) := by
    apply Filter.Eventually.of_forall
    intro k
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, hg, _⟩
    exact hg.le
  have hΛEv : ∀ᶠ k : ℕ in atTop,
      0 ≤ h3PathCubicAnnulusActualLinearRate244 N K C (v k) :=
    Filter.Eventually.of_forall (fun k => hΛ (v k))
  have hΞEv : ∀ᶠ k : ℕ in atTop,
      0 ≤ h3PathCubicAnnulusActualQuadraticRate244 N C (v k) :=
    Filter.Eventually.of_forall (fun k => hΞ (v k))
  have hBarrier := h3Path_exactQuadraticSharpClocks_threeScaleBarrier244
    v δ (fun n => (T - τ n) / 2)
    (h3PathCubicAnnulusActualGap244 hH3 τ N)
    (h3PathCubicAnnulusActualLinearRate244 N K C)
    (h3PathCubicAnnulusActualQuadraticRate244 N C)
    hv hExact hCollapse hQuarter hΛEv hΞEv
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparate, ?_, ?_, ?_, hBarrier⟩
  · intro k
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, hg, _⟩
    exact hg
  · simpa only [f] using hSummable
  · intro k m hnm hmN
    rcases hAll (v k) with ⟨_, _, _, _, _, _, _, _, hMin⟩
    exact hMin m hnm hmN

end
end PrimeTensor.FirstMonomialTriad
