import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessQuarticPDEFactorEscape
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessQuinticCofinalCostSplit
import Mathlib.Tactic

/-!
# Exact physical factors for the fivefold source-clock obstruction

The cofinal quintic charge theorem constructs genuine physical coefficients
A=3+C_L*(norm of the spectral state at the peak + local spectral ceiling)
and B=12*(local projected-momentum-source ceiling)^2
     +2*(actual H3 dissipation at the peak + enhanced source floor).
Its public cofinal conclusion discarded these *defining equalities*.

We reconstruct the same fivefold source-peak selection, retaining the
local ceiling witnesses, A and B identities, separation, and the complete
endpoint Riccati/compression/cutoff/PDE-cost alternative. In the PDE branch
we expose which *physical* factor must grow, with a quantitative quadratic
source cost. No terminal uniform ceiling or noncompression is assumed.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Exact local physics of the original calibrated fivefold quintic source
window. The local upper bounds C and E are genuine compact-window source
and state ceilings. No separate global bound is assumed. -/
theorem h3Critical_fivefoldWindow_exactPhysicalPDEFactorGate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (x w δ σ M q C E A B : ℝ)
    (hx : x ∈ Set.Ioo a T)
    (hM : 0 ≤ M) (hq : 0 < q) (hE0 : 0 ≤ E)
    (hδ : 0 < δ) (hδw : δ ≤ w) (hEnd : x + w < T)
    (hA : A = 3 + h3AuditInitialLerayEnergyCoefficient *
      (‖h3AuditActualSpectralVelocityTotal hH3 x‖ + E))
    (hB : B = 12 * C ^ 2 + 2 *
      (velocityH3DissipationAt u x +
        h3CriticalSourceExcessEnhancedFloor M q))
    (hWidth : min w
      (1 / (h3CriticalSourcePeakSquareRootRadius σ (4 * q) A B) ^ 4) ≤ δ)
    (hFloor : ∀ s : ℝ, s ∈ Set.Icc x (x + δ) →
      h3CriticalSourceExcessEnhancedFloor M q <
        velocityH3DissipationAt u s) :
    (∃ s : ℝ, s ∈ Set.Icc x (x + δ) ∧
      h3CriticalSourceExcessEnhancedFloor M q <
        h3PathSqrtEnergyRiccatiCoefficient *
          Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
    (let H := h3CriticalSourceExcessEnhancedFloor M q
     let J := velocityH3EnergyAt u x - 1
     let S := max 1 σ + 1
     let P := 4 * q
     let K := A ^ 2 * B
     1 < velocityH3EnergyAt u x ∧
       (w ≤ J / H ∨
        H ≤ 16 * J * S ^ 4 ∨
        (S ^ 2 * P ^ 2 < K ∧ H * P ^ 4 ≤ 16 * J * K ^ 2 ∧
          (S < 3 + h3AuditInitialLerayEnergyCoefficient *
              (‖h3AuditActualSpectralVelocityTotal hH3 x‖ + E) ∨
           P ^ 2 < 12 * C ^ 2 + 2 *
              (velocityH3DissipationAt u x + H))))) := by
  let H : ℝ := h3CriticalSourceExcessEnhancedFloor M q
  let J : ℝ := velocityH3EnergyAt u x - 1
  let S : ℝ := max 1 σ + 1
  let P : ℝ := 4 * q
  let K : ℝ := A ^ 2 * B
  have hκ : 0 < 3 * (3 + h3AuditInitialLerayEnergyCoefficient) := by
    have hCL := h3AuditInitialLerayEnergyCoefficient_nonneg
    positivity
  have hH : 0 < H := by
    dsimp only [H, h3CriticalSourceExcessEnhancedFloor]
    exact add_pos_of_nonneg_of_pos hM (div_pos hq hκ)
  have hP : 0 < P := by
    dsimp only [P]
    exact mul_pos (by norm_num) hq
  have hS : 0 ≤ S := by
    dsimp only [S]
    have hMax : (1 : ℝ) ≤ max 1 σ := le_max_left _ _
    linarith only [hMax]
  have hRad : 0 < h3CriticalSourcePeakSquareRootRadius σ P A B := by
    have hSqrt : 0 ≤ Real.sqrt (A ^ 2 * B) := Real.sqrt_nonneg _
    have hDiv : 0 ≤ Real.sqrt (A ^ 2 * B) / P :=
      div_nonneg hSqrt hP.le
    have hMax : (1 : ℝ) ≤ max 1 σ := le_max_left _ _
    change 0 < max 1 σ + 1 + Real.sqrt (A ^ 2 * B) / P
    linarith only [hMax, hDiv]
  have hEndδ : x + δ < T :=
    lt_of_le_of_lt (add_le_add_right hδw x) hEnd
  have hAlt := h3Critical_sourceExcessWindow_endpointDrain_or_RiccatiEnergy
    hH3 hClass x δ H hx hδ.le hEndδ hFloor
  rcases hAlt with hLarge | hDrain
  · exact Or.inl hLarge
  · right
    have hQuartic := h3Critical_scalar_endpointEnergy_forces_calibratedQuarticGate
      (velocityH3EnergyAt u x) (velocityH3EnergyAt u (x + δ))
      H δ w (h3CriticalSourcePeakSquareRootRadius σ P A B)
      hH hδ hRad (by simpa only [P] using hWidth) hDrain
      (one_le_velocityH3EnergyAt u (x + δ))
    obtain ⟨hEnergy, hBranches⟩ := hQuartic
    have hJ : 0 < J := by
      dsimp only [J]
      linarith only [hEnergy]
    change 1 < velocityH3EnergyAt u x ∧
      (w ≤ J / H ∨ H ≤ 16 * J * S ^ 4 ∨
        (S ^ 2 * P ^ 2 < K ∧ H * P ^ 4 ≤ 16 * J * K ^ 2 ∧
          (S < 3 + h3AuditInitialLerayEnergyCoefficient *
            (‖h3AuditActualSpectralVelocityTotal hH3 x‖ + E) ∨
           P ^ 2 < 12 * C ^ 2 + 2 *
            (velocityH3DissipationAt u x + H))))
    refine ⟨hEnergy, ?_⟩
    rcases hBranches with hShort | hRadius
    · exact Or.inl hShort
    · have hHeight : H ≤ J * (S + Real.sqrt K / P) ^ 4 := by
        have hRaw : H / J ≤ (S + Real.sqrt K / P) ^ 4 := by
          simpa only [h3CriticalSourcePeakSquareRootRadius, S, K, P]
            using hRadius
        have hMul := (div_le_iff₀ hJ).mp hRaw
        calc
          H ≤ (S + Real.sqrt K / P) ^ 4 * J := hMul
          _ = J * (S + Real.sqrt K / P) ^ 4 := mul_comm _ _
      rcases h3Critical_scalar_quarticRadius_cutoffOr_quadraticPDECost
        S P K J H hS hP hJ.le hHeight with hCutoff | hPDE
      · exact Or.inr (Or.inl hCutoff)
      · obtain ⟨hThresh, hCharge⟩ := hPDE
        have hFactors :=
          h3Critical_scalar_positiveQuarticPDECost_forces_factorEscape
            S P A B hS hP hThresh
        have hCL : 0 ≤ h3AuditInitialLerayEnergyCoefficient :=
          h3AuditInitialLerayEnergyCoefficient_nonneg
        have hANonneg : 0 ≤ A := by
          rw [hA]
          have hSum : 0 ≤ ‖h3AuditActualSpectralVelocityTotal hH3 x‖ + E :=
            add_nonneg (norm_nonneg _) hE0
          have hProd := mul_nonneg hCL hSum
          linarith only [hProd]
        rcases hFactors with hFactorA | hFactorB
        · refine Or.inr (Or.inr ⟨hThresh, hCharge, Or.inl ?_⟩)
          calc
            S < |A| := hFactorA
            _ = A := abs_of_nonneg hANonneg
            _ = 3 + h3AuditInitialLerayEnergyCoefficient *
                  (‖h3AuditActualSpectralVelocityTotal hH3 x‖ + E) := hA
        · refine Or.inr (Or.inr ⟨hThresh, hCharge, Or.inr ?_⟩)
          simpa only [hB] using hFactorB

/-- Reconstruct the ACTUAL fivefold cofinal source witnesses but keep the
exact defining equations for the projected-source and spectral-state
coefficients that the earlier public cofinal result had hidden. -/
theorem h3Critical_noL2Trace_cofinalFivefold_explicitPhysicalPDEFactorGate
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
    ∃ C E A B δ : ℕ → ℝ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ k < t (v l)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          ENNReal.ofReal (h3CriticalSourceExcessEnhancedFloor
            (M (v k)) (q (v k))) * ENNReal.ofReal (δ k)) ≤
        ∑ k ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (t (v k)) (t (v k) + δ k),
            ENNReal.ofReal (velocityH3DissipationAt u s) ∂volume) ∧
      (∀ k : ℕ,
        t (v k) ∈ Set.Ioo (c (v k)) T ∧
        0 < w (v k) ∧ t (v k) + w (v k) < T ∧
        0 ≤ C k ∧ 0 ≤ E k ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) →
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C k ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ E k) ∧
        A k = 3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ + E k) ∧
        B k = 12 * (C k) ^ 2 + 2 *
          (velocityH3DissipationAt u (t (v k)) +
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))) ∧
        0 < δ k ∧ δ k ≤ w (v k) ∧
        min (w (v k))
          (1 / (h3CriticalSourcePeakSquareRootRadius
            (σ (v k)) (4 * q (v k)) (A k) (B k)) ^ 4) ≤ δ k ∧
        ((∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
              h3PathSqrtEnergyRiccatiCoefficient *
                Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
          (let H := h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))
           let J := velocityH3EnergyAt u (t (v k)) - 1
           let S := max 1 (σ (v k)) + 1
           let P := 4 * q (v k)
           let K := (A k) ^ 2 * B k
           1 < velocityH3EnergyAt u (t (v k)) ∧
             (w (v k) ≤ J / H ∨
              H ≤ 16 * J * S ^ 4 ∨
              (S ^ 2 * P ^ 2 < K ∧ H * P ^ 4 ≤ 16 * J * K ^ 2 ∧
                (S < 3 + h3AuditInitialLerayEnergyCoefficient *
                    (‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ + E k) ∨
                 P ^ 2 < 12 * (C k) ^ 2 + 2 *
                    (velocityH3DissipationAt u (t (v k)) + H))))))) := by
  let fiveq : ℕ → ℝ := fun n => 5 * q n
  have hFive : ∀ n, 0 ≤ fiveq n := by
    intro n
    dsimp only [fiveq]
    exact mul_nonneg (by norm_num) (hq n).le
  obtain ⟨i, t, w, v, hv, hLimit, hSeparated, hWindows, _hOldCost⟩ :=
    h3Critical_noL2Trace_sourceExcess_disjointEnhancedFullDissipationCosts
      hH3 hClass b hb hNoTrace c ρ σ M fiveq hc hcLimit hρ hσ hM hFive
  have hSelected (k : ℕ) :
      ∃ C E A B δ : ℝ,
        0 ≤ C ∧ 0 ≤ E ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) →
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤ C ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤ E) ∧
        A = 3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ + E) ∧
        B = 12 * C ^ 2 + 2 *
          (velocityH3DissipationAt u (t (v k)) +
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))) ∧
        0 < δ ∧ δ ≤ w (v k) ∧
        min (w (v k))
          (1 / (h3CriticalSourcePeakSquareRootRadius
            (σ (v k)) (4 * q (v k)) A B) ^ 4) ≤ δ ∧
        ∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ) →
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            velocityH3DissipationAt u s := by
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
    obtain ⟨C, E, _R0, _δ0, hC0, hE0, _hR0, _hσR0,
        _hδ0, _hδw0, _hClock0, hCeils, _hFloor0⟩ :=
      h3Critical_strictSourcePeak_automaticPersistence_withoutLocalCeilingAssumptions
        hH3 hClass b hb (ρ (v k)) (σ (v k)) (hσ (v k)) i
        (t (v k)) ht (M (v k)) (w (v k)) (hM (v k))
        (hWindows k).2.1 (hWindows k).2.2.1 hPeak
    obtain ⟨A, B, _R, δ, hA, hB, _hR, hδ, hδw,
        hWidth, hFull, _hGate⟩ :=
      h3Critical_fivefoldActualSourcePeak_certifiesPhysicalQuinticGate
        hH3 hClass b hb (ρ (v k)) (σ (v k)) (hσ (v k)) i
        (t (v k)) ht (M (v k)) (q (v k)) C E (w (v k))
        (hM (v k)) (hq (v k)) (hWindows k).2.1 (hWindows k).2.2.1
        (fun s hs => (hCeils s hs).1)
        (fun s hs => (hCeils s hs).2) hFivePeak
    exact ⟨C, E, A, B, δ, hC0, hE0, hCeils, hA, hB,
      hδ, hδw, hWidth, hFull⟩
  choose C E A B δ hC0 hE0 hCeils hA hB hδ hδw hWidth hFull using hSelected
  have hSep (k l : ℕ) (hkl : k < l) :
      t (v k) + δ k < t (v l) := by
    have hShort : t (v k) + δ k ≤ t (v k) + w (v k) :=
      add_le_add_right (hδw k) (t (v k))
    exact lt_of_le_of_lt hShort (hSeparated k l hkl)
  refine ⟨i, t, w, v, C, E, A, B, δ, hv, hLimit, hSep, ?_, ?_⟩
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
  · intro k
    have ht : t (v k) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (lt_trans (hc (v k)).1 (hWindows k).1.1),
        (hWindows k).1.2⟩
    have hAlt := h3Critical_fivefoldWindow_exactPhysicalPDEFactorGate
      hH3 hClass (t (v k)) (w (v k)) (δ k)
      (σ (v k)) (M (v k)) (q (v k)) (C k) (E k) (A k) (B k)
      ht (hM (v k)) (hq (v k)) (hE0 k) (hδ k) (hδw k)
      (hWindows k).2.2.1 (hA k) (hB k) (hWidth k) (hFull k)
    exact ⟨(hWindows k).1, (hWindows k).2.1,
      (hWindows k).2.2.1, hC0 k, hE0 k,
      hCeils k, hA k, hB k, hδ k, hδw k, hWidth k, hAlt⟩

end
end PrimeTensor.Bridge.Euclidean
