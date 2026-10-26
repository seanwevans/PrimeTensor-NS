import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointCostCollapse244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECofinalWindows244
import Mathlib.Tactic

/-!
# Exact anchored cubic-window width and terminal cost alternative

The previous terminal cubic window theorem packages existence of a positive
PDE-budgeted width. We now retain the exact explicit width selector. This is
necessary before applying the algebraic coefficient-growth barrier: arbitrary
shrinkage of an existential window cannot prove source concentration.

The resulting local witness and cofinal sequence record a *literal* minimum
of the terminal-time cap, unit cap and annular-gap/polynomial-PDE cap. A separate
algebraic trichotomy identifies the only three ways its cost can be small.

No unconditional bound on the source coefficient, cutoff, or full terminal H3
dissipation is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Preserve the *exact* selector instead of an arbitrary shorter positive
interval. The parameter b is half of the remaining physical time at the
cubic witness. -/
noncomputable def h3PathCubicAnnulusExactPDEWidth244
    (b gap Λ Ξ : ℝ) : ℝ :=
  min (b / 2) (min (1 : ℝ) (gap / (2 * (Λ + Ξ + 1))))

/-- The literal minimum meets the anchored quadratic PDE variation budget;
there is no hidden selection or additional time shrinkage. -/
theorem h3Path_cubicAnnulusExactPDEWidth_valid244
    (b gap Λ Ξ : ℝ)
    (hb : 0 < b) (hgap : 0 < gap)
    (hΛ : 0 ≤ Λ) (hΞ : 0 ≤ Ξ) :
    ∃ δ : ℝ,
      δ = h3PathCubicAnnulusExactPDEWidth244 b gap Λ Ξ ∧
      0 < δ ∧ δ < b ∧ δ ≤ 1 ∧
      Λ * δ + Ξ * δ ^ 2 < gap := by
  let Z : ℝ := Λ + Ξ + 1
  have hZ : 0 < Z := by
    dsimp only [Z]
    linarith only [hΛ, hΞ]
  let δ : ℝ := min (b / 2) (min (1 : ℝ) (gap / (2 * Z)))
  have hδ : 0 < δ := by
    dsimp only [δ]
    apply lt_min
    · linarith only [hb]
    · apply lt_min
      · norm_num
      · positivity
  have hδb : δ ≤ b / 2 := by
    dsimp only [δ]
    exact min_le_left _ _
  have hδone : δ ≤ 1 := by
    dsimp only [δ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδgap : δ ≤ gap / (2 * Z) := by
    dsimp only [δ]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hSquare : δ ^ 2 ≤ δ := by
    have hMul : 0 ≤ δ * (1 - δ) :=
      mul_nonneg hδ.le (by linarith only [hδone])
    nlinarith only [hMul]
  have hScaled : Z * δ ≤ gap / 2 := by
    calc
      Z * δ ≤ Z * (gap / (2 * Z)) :=
        mul_le_mul_of_nonneg_left hδgap hZ.le
      _ = gap / 2 := by
        field_simp [ne_of_gt hZ]
  have hQ : Ξ * δ ^ 2 ≤ Ξ * δ :=
    mul_le_mul_of_nonneg_left hSquare hΞ
  have hBudget : Λ * δ + Ξ * δ ^ 2 < gap := by
    have hUpper : Λ * δ + Ξ * δ ^ 2 ≤ Z * δ := by
      dsimp only [Z]
      nlinarith only [hQ, hδ]
    linarith only [hUpper, hScaled, hgap]
  refine ⟨δ, ?_, hδ, ?_, hδone, hBudget⟩
  · rfl
  · linarith only [hb, hδb]

/-- With an exact width selector, small cost forces either geometric
terminal-time compression, a large mass budget relative to the cubic
height, or growth of the anchored-PDE variation coefficients. -/
theorem h3Path_cubicAnnulusExactPDEWidth_costTrichotomy244
    (A M b gap Λ Ξ δ : ℝ)
    (hA : 0 < A) (hΛ : 0 ≤ Λ) (hΞ : 0 ≤ Ξ)
    (hExact : δ = h3PathCubicAnnulusExactPDEWidth244 b gap Λ Ξ)
    (hCost : A * δ ≤ M) :
    2 * M ≥ A * b ∨ M ≥ A ∨
      A * gap ≤ 2 * M * (Λ + Ξ + 1) := by
  by_cases hClock : 2 * M < A * b
  · by_cases hUnit : M < A
    · right
      right
      apply h3Path_explicitBudgetWidth_forces_PDECoefficientGrowth244
        A M b gap Λ Ξ hA hΛ hΞ
      · simpa only [hExact, h3PathCubicAnnulusExactPDEWidth244] using hCost
      · exact hClock
      · exact hUnit
    · right
      left
      exact le_of_not_gt hUnit
  · left
    exact le_of_not_gt hClock

/-- Each physical cubic witness admits its *literal* PDE width, with local
source ceiling and starting spectral bound selected from the actual path.
The same exact width carries the integrated half-cubic annulus cost. -/
theorem h3Path_cubicHighSnapshot_has_exactPDEClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (n : ℕ)
    (hCube : ((n : ℝ) + 1) ^ 3 <
      h3PathActualHighRadialDissipation244 ((n : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 t)) :
    ∃ (N : ℕ) (K C δ : ℝ),
      n ≤ N ∧ 0 ≤ K ∧ 0 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ t + δ < T ∧
      (∀ j : Fin 3,
        ‖(h3AuditActualSpectralVelocityTotal hH3 t) j‖ ≤ K) ∧
      (∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C) ∧
      (δ = h3PathCubicAnnulusExactPDEWidth244 ((T - t) / 2)
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
      (δ * (((n : ℝ) + 1) ^ 3 / 2) ≤
        ∫ s in t..(t + δ),
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) := by
  obtain ⟨N, hnN, hHeight⟩ :=
    h3Path_cubicHighSnapshot_has_finiteAnnularHeight244
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
  have hGap : 0 < B - A := by
    dsimp only [A]
    linarith only [hHeight', hCubePos]
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
  obtain ⟨δ, hExact, hδ, hδb, hδone, hBudget⟩ :=
    h3Path_cubicAnnulusExactPDEWidth_valid244
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
  refine ⟨N, K, C, δ, hnN, hK, hC, hδ, hδone, hEnd,
    hBase, hSourceWindow, ?_, ?_, ?_⟩
  · change δ = h3PathCubicAnnulusExactPDEWidth244 b (B - A) Λ Ξ
    exact hExact
  · exact hFinal.1
  · exact hFinal.2

/-- The original no-terminal-L2-trace branch now carries *exact* polynomial
PDE windows along its full cofinal cubic witness sequence. The equality is
preserved before any disjoint subsequence extraction. -/
theorem h3Path_noL2Trace_forces_cubicExactPDEClocks244
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
        n ≤ N n ∧ 0 ≤ K n ∧ 0 ≤ C n ∧ 0 < δ n ∧ δ n ≤ 1 ∧
        τ n + δ n < T ∧
        (∀ j : Fin 3,
          ‖(h3AuditActualSpectralVelocityTotal hH3 (τ n)) j‖ ≤ K n) ∧
        (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ n) →
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C n) ∧
        (δ n = h3PathCubicAnnulusExactPDEWidth244 ((T - τ n) / 2)
          ((h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n))) -
            ((n : ℝ) + 1) ^ 3 / 2)
          (h3PathFiniteAnnulusPDEVariationCoefficient244
            ((n : ℝ) + 1) ((N n : ℝ) + 1) (K n) (C n))
          (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
            ((n : ℝ) + 1) ((N n : ℝ) + 1) (C n))) ∧
        (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ n) →
          ((n : ℝ) + 1) ^ 3 / 2 <
            h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        (δ n * (((n : ℝ) + 1) ^ 3 / 2) ≤
          ∫ s in τ n..(τ n + δ n),
            h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s))) := by
  obtain ⟨τ, hτ, _hNear, hLimit, hCube⟩ :=
    h3Path_physicalNoL2Trace_forces_highRadialCubicDissipationSequence244
      hH3 hClass hMass hNoTrace
  have hChoice (n : ℕ) : ∃ (N : ℕ) (K C δ : ℝ),
      n ≤ N ∧ 0 ≤ K ∧ 0 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ τ n + δ < T ∧
      (∀ j : Fin 3,
        ‖(h3AuditActualSpectralVelocityTotal hH3 (τ n)) j‖ ≤ K) ∧
      (∀ s : ℝ, s ∈ Set.Icc (τ n) (τ n + δ) →
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C) ∧
      (δ = h3PathCubicAnnulusExactPDEWidth244 ((T - τ n) / 2)
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
      (δ * (((n : ℝ) + 1) ^ 3 / 2) ≤
        ∫ s in τ n..(τ n + δ),
          h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s)) :=
    h3Path_cubicHighSnapshot_has_exactPDEClock244
      hH3 hClass (τ n) (hτ n) n (hCube n)
  choose N K C δ hAll using hChoice
  exact ⟨τ, N, K, C, δ, hτ, hLimit, hAll⟩

end
end PrimeTensor.FirstMonomialTriad
