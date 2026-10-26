import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEAnchoredPersistence244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusIntegratedWindows244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopUniformProjectedRHS244
import Mathlib.Tactic

/-!
# Cofinal cubic annuli with automatically selected anchored PDE windows

The positive-time physical projected momentum source is continuous on any
strictly interior closed interval. Thus each cubic high-radial witness has a
finite local source ceiling, without an independently prescribed temporal
PDE hypothesis. Its actual starting H³ spectral state supplies its own
finite coordinate ceiling.

At any such witness, the existing finite-annulus extraction gives a strict
three-quarter-cubic lower bound. The anchored PDE polarization estimate
then admits a positive, explicitly constructed window on which the annular
energy stays above half the cubic threshold. This file packages the resulting
source ceiling, spectral ceiling, polynomial width budget, and integrated
lower bound at the *same* cofinal witnesses.

No uniform lower bound for the selected widths is claimed. In particular,
this theorem does not by itself give terminal integrated divergence.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- A strictly positive polynomial budget admits an explicit short interval.
The extra `1` in the denominator makes the bound valid even when both rate
coefficients vanish. -/
theorem h3Path_exists_positiveQuadraticBudgetWidth244
    (b Λ Ξ gap : ℝ)
    (hb : 0 < b) (hΛ : 0 ≤ Λ) (hΞ : 0 ≤ Ξ) (hgap : 0 < gap) :
    ∃ δ : ℝ, 0 < δ ∧ δ < b ∧ δ ≤ 1 ∧
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
  exact ⟨δ, hδ, by linarith only [hb, hδb], hδone, hBudget⟩

/-- A single genuine cubic high-radial witness determines a finite annulus,
a local projected physical PDE source ceiling, its own initial H³ coordinate
ceiling, and a strictly positive interval satisfying the *anchored* polynomial
PDE budget. The exact same interval retains half the cubic height and incurs
a finite-band integrated dissipation cost. -/
theorem h3Path_cubicHighSnapshot_has_anchoredPDEWindow244
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
      (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) K C * δ +
        h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) C * δ ^ 2 <
        (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 t)) -
            ((n : ℝ) + 1) ^ 3 / 2) ∧
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
  let b : ℝ := (t + T) / 2
  have ht0 : 0 < t := lt_trans hClass.terminal_start.1 ht.1
  have htb : t < b := by
    dsimp only [b]
    linarith only [ht.2]
  have hbT : b < T := by
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
  obtain ⟨δ, hδ, hδb, hδone, hBudget⟩ :=
    h3Path_exists_positiveQuadraticBudgetWidth244
      (b - t) Λ Ξ (B - A) (sub_pos.mpr htb) hΛ hΞ hGap
  have hEnd : t + δ < T := by
    linarith only [hδb, hbT]
  have hSourceWindow : ∀ s : ℝ, s ∈ Set.Icc t (t + δ) →
      ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C := by
    intro s hs
    apply hSource s
    constructor
    · exact hs.1
    · linarith only [hs.2, hδb]
  have hWidth : Λ * δ + Ξ * δ ^ 2 < B - A := hBudget
  have hFinal :=
    h3Path_actualFiniteAnnulus_integratedCost_of_anchoredPDE244
      hH3 hClass R Q K C A t δ hR hQ hK hA ht hδ hEnd
      hBase hSourceWindow (show A < B from sub_pos.mp hGap)
      hWidth
  refine ⟨N, K, C, δ, hnN, hK, hC, hδ, hδone, hEnd, hBase,
    hSourceWindow, ?_, ?_, ?_⟩
  · exact hWidth
  · exact hFinal.1
  · exact hFinal.2

/-- The existing cofinal cubic sequence admits the *same* explicitly
PDE-budgeted windows. Each window's source ceiling and initial H³ ceiling
are chosen from the actual physical path and need not be uniform in n. -/
theorem h3Path_noL2Trace_forces_cubicAnchoredPDEWindows244
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
        (h3PathFiniteAnnulusPDEVariationCoefficient244
            ((n : ℝ) + 1) ((N n : ℝ) + 1) (K n) (C n) * δ n +
          h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
            ((n : ℝ) + 1) ((N n : ℝ) + 1) (C n) * (δ n) ^ 2 <
          (h3PathActualLowRadialDissipation244 ((N n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
            h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ n))) -
              ((n : ℝ) + 1) ^ 3 / 2) ∧
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
      (h3PathFiniteAnnulusPDEVariationCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) K C * δ +
        h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
          ((n : ℝ) + 1) ((N : ℝ) + 1) C * δ ^ 2 <
        (h3PathActualLowRadialDissipation244 ((N : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n)) -
          h3PathActualLowRadialDissipation244 ((n : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ n))) -
            ((n : ℝ) + 1) ^ 3 / 2) ∧
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
            (h3AuditActualSpectralVelocityTotal hH3 s)) := by
    exact h3Path_cubicHighSnapshot_has_anchoredPDEWindow244
      hH3 hClass (τ n) (hτ n) n (hCube n)
  choose N K C δ hChoiceAll using hChoice
  exact ⟨τ, N, K, C, δ, hτ, hLimit, hChoiceAll⟩

end
end PrimeTensor.FirstMonomialTriad
