import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessQuinticPhysicalCharge
import Mathlib.Tactic

/-!
# Cofinal quintic source charges: geometric, cutoff, or actual PDE cost escape

A fivefold genuine highpass Fourier-source excess gives an enhanced physical
H³ dissipation floor and a calibrated quartic persistence window. We lift the
accepted single-window quintic charge gate to cofinal separated PDE windows.

The quintic cost inequality splits sharply into two necessary competing terms:
cutoff growth and local projected-PDE / spectral-state cost growth. Together
with compression of the original geometric window, this identifies the three
possible ways the actual physical dissipation cost may remain small.

No finite terminal H³ dissipation budget, uniform source ceiling, or uniform
window width is assumed or concluded.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeQuinticCofinal
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceQuinticCofinal :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- If the actual source-excess quintic estimate holds, at least one of
its two nonnegative square contributions must carry one quarter of the
original fifth-power requirement. This is the exact scalar obstruction,
without a hidden terminal-uniform constant. -/
theorem h3Critical_quinticMargin_cutoffOrPDECost
    (σ q A B J : ℝ) (hJ : 0 < J)
    (hQuintic :
      64 * q ^ 5 ≤
        (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
          (16 * (max 1 σ + 1) ^ 2 * q ^ 2 + A ^ 2 * B) ^ 2) :
    16 * q ^ 5 ≤
        (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
          (16 * (max 1 σ + 1) ^ 2 * q ^ 2) ^ 2 ∨
    16 * q ^ 5 ≤
        (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
          (A ^ 2 * B) ^ 2 := by
  let κ : ℝ := 3 * (3 + h3AuditInitialLerayEnergyCoefficient)
  let X : ℝ := 16 * (max 1 σ + 1) ^ 2 * q ^ 2
  let Y : ℝ := A ^ 2 * B
  have hκ : 0 < κ := by
    dsimp only [κ]
    have hCL := h3AuditInitialLerayEnergyCoefficient_nonneg
    positivity
  have hκJ : 0 ≤ κ * J := (mul_pos hκ hJ).le
  have hSquare : (X + Y) ^ 2 ≤ 2 * (X ^ 2 + Y ^ 2) := by
    nlinarith only [sq_nonneg (X - Y)]
  have hScaled := mul_le_mul_of_nonneg_left hSquare hκJ
  have hQuintic' : 64 * q ^ 5 ≤ κ * J * (X + Y) ^ 2 := hQuintic
  have hTotal :
      64 * q ^ 5 ≤ 2 * (κ * J * X ^ 2 + κ * J * Y ^ 2) := by
    calc
      64 * q ^ 5 ≤ κ * J * (X + Y) ^ 2 := hQuintic'
      _ ≤ κ * J * (2 * (X ^ 2 + Y ^ 2)) := hScaled
      _ = 2 * (κ * J * X ^ 2 + κ * J * Y ^ 2) := by ring
  change 16 * q ^ 5 ≤ κ * J * X ^ 2 ∨
    16 * q ^ 5 ≤ κ * J * Y ^ 2
  by_cases hCutoff : 16 * q ^ 5 ≤ κ * J * X ^ 2
  · exact Or.inl hCutoff
  · right
    have hCutoffSmall : κ * J * X ^ 2 < 16 * q ^ 5 :=
      lt_of_not_ge hCutoff
    nlinarith only [hTotal, hCutoffSmall]

/-- In the first branch the source excess is at most the actual budget
multiplied by the fourth power of the cutoff. There is no remaining q⁴
factor: it cancels using q>0. -/
theorem h3Critical_quinticCutoffBranch_normalizesToLinearSource
    (σ q J : ℝ) (hq : 0 < q)
    (hCutoff :
      16 * q ^ 5 ≤
        (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
          (16 * (max 1 σ + 1) ^ 2 * q ^ 2) ^ 2) :
    q ≤ 16 * (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
      (max 1 σ + 1) ^ 4 := by
  let κ : ℝ := 3 * (3 + h3AuditInitialLerayEnergyCoefficient)
  let S : ℝ := max 1 σ + 1
  have hFactor : 0 < 16 * q ^ 4 :=
    mul_pos (by norm_num) (pow_pos hq 4)
  have hRest :
      (16 * q ^ 4) * q ≤
        (16 * q ^ 4) * (16 * κ * J * S ^ 4) := by
    calc
      (16 * q ^ 4) * q = 16 * q ^ 5 := by ring
      _ ≤ κ * J * (16 * S ^ 2 * q ^ 2) ^ 2 := hCutoff
      _ = (16 * q ^ 4) * (16 * κ * J * S ^ 4) := by ring
  by_contra hNot
  have hOpp : 16 * κ * J * S ^ 4 < q := lt_of_not_ge hNot
  have hStrict :
      (16 * q ^ 4) * (16 * κ * J * S ^ 4) < (16 * q ^ 4) * q :=
    mul_lt_mul_of_pos_left hOpp hFactor
  exact (not_lt_of_ge hRest) hStrict

/-- Combining the scalar quintic split with positivity of q yields
an explicit *linear* cutoff growth gate or a genuine PDE-cost-square gate. -/
theorem h3Critical_quinticMargin_normalizedCutoffOrPDECost
    (σ q A B J : ℝ) (hq : 0 < q) (hJ : 0 < J)
    (hQuintic :
      64 * q ^ 5 ≤
        (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
          (16 * (max 1 σ + 1) ^ 2 * q ^ 2 + A ^ 2 * B) ^ 2) :
    q ≤ 16 * (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
      (max 1 σ + 1) ^ 4 ∨
    16 * q ^ 5 ≤
      (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
        (A ^ 2 * B) ^ 2 := by
  rcases h3Critical_quinticMargin_cutoffOrPDECost σ q A B J hJ hQuintic
    with hCutoff | hPDE
  · exact Or.inl
      (h3Critical_quinticCutoffBranch_normalizesToLinearSource
        σ q J hq hCutoff)
  · exact Or.inr hPDE

/-- A non-compressed, strongly source-excess-driven window cannot evade
its quintic H³ cost without a quantitative blowup in the actual local
source/spectral/viscous PDE coefficient A²B. -/
theorem h3Critical_quinticMargin_largeSource_forces_PDECost
    (σ q A B w M J : ℝ) (hq : 0 < q) (hJ : 0 < J)
    (hGeometric : J / h3CriticalSourceExcessEnhancedFloor M q < w)
    (hCutoffSmall :
      16 * (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
        (max 1 σ + 1) ^ 4 < q)
    (hGate :
      w ≤ J / h3CriticalSourceExcessEnhancedFloor M q ∨
      64 * q ^ 5 ≤
        (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
          (16 * (max 1 σ + 1) ^ 2 * q ^ 2 + A ^ 2 * B) ^ 2) :
    16 * q ^ 5 ≤
      (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
        (A ^ 2 * B) ^ 2 := by
  rcases hGate with hShort | hQuintic
  · exact False.elim ((not_le_of_gt hGeometric) hShort)
  · rcases h3Critical_quinticMargin_normalizedCutoffOrPDECost
      σ q A B J hq hJ hQuintic with hSmall | hPDE
    · exact False.elim ((not_le_of_gt hCutoffSmall) hSmall)
    · exact hPDE

/-- The source-excess witness and actual H³ PDE jointly give a cofinal
family of pairwise separated quintic-cost windows. At EVERY index and
for EVERY genuine finite local dissipation charge J>0, at least one of three
mechanisms remains: geometric window compression, cutoff growth,
or physical local PDE cost growth. There are no terminal-uniform ceilings.
-/
theorem h3Critical_noL2Trace_cofinalFivefoldSource_quinticThreeWayCostGate
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
    ∃ _i : Fin 3, ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ A B R δ : ℕ → ℝ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k : ℕ,
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < w (v k) ∧ t (v k) + w (v k) < T ∧
        1 ≤ R k ∧ 0 < δ k ∧ δ k ≤ w (v k) ∧
        min (w (v k))
          (1 / (h3CriticalSourcePeakSquareRootRadius
            (σ (v k)) (4 * q (v k)) (A k) (B k)) ^ 4) ≤ δ k ∧
        ∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) →
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            velocityH3DissipationAt u s) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ k < t (v l)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
            (M (v k)) (q (v k))) * ENNReal.ofReal (δ k)) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
            ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ∧
      (∀ k : ℕ, ∀ J : ℝ, 0 < J →
        (∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ≤
            ENNReal.ofReal J →
        w (v k) ≤ J / h3CriticalSourceExcessEnhancedFloor
          (M (v k)) (q (v k)) ∨
        (q (v k) ≤
            16 * (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
              (max 1 (σ (v k)) + 1) ^ 4 ∨
          16 * (q (v k)) ^ 5 ≤
            (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
              ((A k) ^ 2 * (B k)) ^ 2)) := by
  let fiveq : ℕ → ℝ := fun n => 5 * q n
  have hFive : ∀ n, 0 ≤ fiveq n := by
    intro n
    dsimp only [fiveq]
    exact mul_nonneg (by norm_num) (hq n).le
  obtain ⟨i, t, w, v, hv, hLimit, hSeparated, hWindows, _hOldCost⟩ :=
    h3Critical_noL2Trace_sourceExcess_disjointEnhancedFullDissipationCosts
      hH3 hClass b hb hNoTrace c ρ σ M fiveq hc hcLimit hρ hσ hM hFive
  have hSelected (k : ℕ) :
      ∃ A B R δ : ℝ,
        1 ≤ R ∧ 0 < δ ∧ δ ≤ w (v k) ∧
        min (w (v k))
          (1 / (h3CriticalSourcePeakSquareRootRadius
            (σ (v k)) (4 * q (v k)) A B) ^ 4) ≤ δ ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ) →
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            velocityH3DissipationAt u s) ∧
        (∀ J : ℝ, 0 < J →
          (∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ),
            ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ≤
              ENNReal.ofReal J →
          w (v k) ≤ J / h3CriticalSourceExcessEnhancedFloor
            (M (v k)) (q (v k)) ∨
          (q (v k) ≤
              16 * (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
                (max 1 (σ (v k)) + 1) ^ 4 ∨
            16 * (q (v k)) ^ 5 ≤
              (3 * (3 + h3AuditInitialLerayEnergyCoefficient)) * J *
                (A ^ 2 * B) ^ 2)) := by
    have ht : t (v k) ∈ Set.Ioo b T :=
      ⟨lt_trans (hc (v k)).1 (hWindows k).1.1, (hWindows k).1.2⟩
    have hAtStart : t (v k) ∈ Set.Icc
        (t (v k)) (t (v k) + w (v k)) :=
      ⟨le_rfl, le_add_of_nonneg_right ((hWindows k).2.1).le⟩
    have hFivePeak :
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) (σ (v k)) (M (v k)) +
          5 * q (v k) <
        ‖h3CriticalActualProjectedHighpassFourierSource hH3
          (ρ (v k)) i (t (v k))‖ := by
      exact ((hWindows k).2.2.2 (t (v k)) hAtStart).1
    have hPeak :
        h3CriticalSourceDrivenHighDissipationBarrier
          (velocityH3Energy0At u b) (σ (v k)) (M (v k)) <
        ‖h3CriticalActualProjectedHighpassFourierSource hH3
          (ρ (v k)) i (t (v k))‖ := by
      have hPositive : 0 ≤ 5 * q (v k) :=
        mul_nonneg (by norm_num) (hq (v k)).le
      linarith only [hFivePeak, hPositive]
    obtain ⟨C, E, _R0, _δ0, _hC0, _hE0, _hR0, _hσR0,
        _hδ0, _hδw0, _hClock0, hCeils, _hFloor0⟩ :=
      h3Critical_strictSourcePeak_automaticPersistence_withoutLocalCeilingAssumptions
        hH3 hClass b hb (ρ (v k)) (σ (v k)) (hσ (v k)) i
        (t (v k)) ht (M (v k)) (w (v k)) (hM (v k))
        (hWindows k).2.1 (hWindows k).2.2.1 hPeak
    obtain ⟨A, B, R, δ, _hA, _hB, hR, hδ, hδw, hWidth, hFull, hGate⟩ :=
      h3Critical_fivefoldActualSourcePeak_certifiesPhysicalQuinticGate
        hH3 hClass b hb (ρ (v k)) (σ (v k)) (hσ (v k)) i
        (t (v k)) ht (M (v k)) (q (v k)) C E (w (v k))
        (hM (v k)) (hq (v k)) (hWindows k).2.1 (hWindows k).2.2.1
        (fun s hs => (hCeils s hs).1)
        (fun s hs => (hCeils s hs).2) hFivePeak
    refine ⟨A, B, R, δ, hR, hδ, hδw, hWidth, hFull, ?_⟩
    intro J hJ hBudget
    rcases hGate J hJ hBudget with hShort | hQuintic
    · exact Or.inl hShort
    · exact Or.inr
        (h3Critical_quinticMargin_normalizedCutoffOrPDECost
          (σ (v k)) (q (v k)) A B J (hq (v k)) hJ hQuintic)
  choose A B R δ hR hδ hδw hWidth hFull hGate using hSelected
  refine ⟨i, t, w, v, A, B, R, δ, hv, hLimit, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(hWindows k).1, (hWindows k).2.1,
      (hWindows k).2.2.1, hR k, hδ k, hδw k, hWidth k, hFull k⟩
  · intro k l hkl
    have hShort : t (v k) + δ k ≤ t (v k) + w (v k) :=
      add_le_add_right (hδw k) (t (v k))
    exact lt_of_le_of_lt hShort (hSeparated k l hkl)
  · intro m
    apply Finset.sum_le_sum
    intro k _hk
    have hLower :
        (∫⁻ _s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
            (M (v k)) (q (v k))) ∂volume) ≤
        ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume := by
      apply h3Critical_extendedWindowCost_of_pointwiseFloor
      intro s hs
      exact (hFull k s hs).le
    calc
      ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
          (M (v k)) (q (v k))) * ENNReal.ofReal (δ k) =
          (∫⁻ _s in Set.Ioc (t (v k)) (t (v k) + δ k),
            ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
              (M (v k)) (q (v k))) ∂volume) :=
        (h3Critical_extendedConstantWindow_eq_heightWidth
          (t (v k)) (δ k)
          (h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)))
          (hδ k).le).symm
      _ ≤ ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
          ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume := hLower
  · intro k J hJ hBudget
    exact hGate k J hJ hBudget

end
end PrimeTensor.Bridge.Euclidean
