import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessExplicitPhysicalPDEFactorGate
import Mathlib.Tactic

/-!
# Unpack cofinal quintic PDE factor escape into actual source and viscosity

The fivefold physical source witnesses from the committed theorem carry
A = 3 + C_L (‖U(t)‖ + Eceil) and
B = 12 Cceil² + 2 (D(t) + H),
where the local ceilings Cceil and Eceil are certified on the original
compact window.  We remove the intermediate A/B alternatives:

  cutoff-scale < 3 + 2 C_L Eceil, or
  (4q)² < 24 Cceil², or
  (4q)² < 8 D(t), or
  (4q)² < 8 H.

The last branch explicitly records that the source floor itself may
pay the purported PDE escape.  Excluding that branch requires the genuine
additional inequality 8H <= (4q)².  Nothing here proves a terminal-uniform
bound on the local ceilings, a noncompressed window, or global regularity.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Physical A/B factor escape resolves into the actual spectral-state
ceiling, projected momentum source ceiling, instantaneous H³ viscous
dissipation, or the source floor itself.  No sign assumption on D or H is
needed for this four-way strict inequality. -/
theorem h3Critical_scalar_explicitAB_forces_physicalFourWay
    (S P CL U E C D H A B : ℝ)
    (hCL : 0 ≤ CL) (hU : U ≤ E) (hANonneg : 0 ≤ A)
    (hA : A = 3 + CL * (U + E))
    (hB : B = 12 * C ^ 2 + 2 * (D + H))
    (hFactor : S < |A| ∨ P ^ 2 < B) :
    S < 3 + 2 * CL * E ∨
      P ^ 2 < 24 * C ^ 2 ∨
      P ^ 2 < 8 * D ∨ P ^ 2 < 8 * H := by
  rcases hFactor with hState | hViscous
  · left
    have hSum : U + E ≤ 2 * E := by
      linarith only [hU]
    have hScaled := mul_le_mul_of_nonneg_left hSum hCL
    have hStateA : S < A := by
      simpa only [abs_of_nonneg hANonneg] using hState
    rw [hA] at hStateA
    linarith only [hScaled, hStateA]
  · right
    have hBViscous : P ^ 2 < 12 * C ^ 2 + 2 * (D + H) := by
      simpa only [hB] using hViscous
    by_cases hSource : P ^ 2 < 24 * C ^ 2
    · exact Or.inl hSource
    · by_cases hDiss : P ^ 2 < 8 * D
      · exact Or.inr (Or.inl hDiss)
      · right
        right
        by_contra hHNot
        have hCceil : 24 * C ^ 2 ≤ P ^ 2 := le_of_not_gt hSource
        have hDceil : 8 * D ≤ P ^ 2 := le_of_not_gt hDiss
        have hHceil : 8 * H ≤ P ^ 2 := le_of_not_gt hHNot
        nlinarith only [hBViscous, hCceil, hDceil, hHceil]

/-- Once the source floor is not itself large enough to pay the selected
P² scale, only actual spectral, projected source, or viscous escape remains. -/
theorem h3Critical_scalar_explicitAB_forces_physicalThreeWay
    (S P CL U E C D H A B : ℝ)
    (hCL : 0 ≤ CL) (hU : U ≤ E) (hANonneg : 0 ≤ A)
    (hA : A = 3 + CL * (U + E))
    (hB : B = 12 * C ^ 2 + 2 * (D + H))
    (hSmallFloor : 8 * H ≤ P ^ 2)
    (hFactor : S < |A| ∨ P ^ 2 < B) :
    S < 3 + 2 * CL * E ∨
      P ^ 2 < 24 * C ^ 2 ∨ P ^ 2 < 8 * D := by
  rcases h3Critical_scalar_explicitAB_forces_physicalFourWay
    S P CL U E C D H A B hCL hU hANonneg hA hB hFactor with
    hState | hSource | hDiss | hFloor
  · exact Or.inl hState
  · exact Or.inr (Or.inl hSource)
  · exact Or.inr (Or.inr hDiss)
  · exact False.elim ((not_lt_of_ge hSmallFloor) hFloor)

/-- Preserve the original separated cofinal fivefold source witnesses,
exact local C/E ceilings, their physical A/B identities and full-H³
integrated dissipation costs, while resolving the factor branch into actual
physical source, spectral, dissipation, and source-floor inequalities. -/
theorem h3Critical_noL2Trace_cofinalFivefold_physicalSourceViscousFactorGate
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
    ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
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
            (σ (v k)) (4 * q (v k)) (A k) (B k)) ^ 4) ≤ δ k) ∧
      (∀ k : ℕ,
        (∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            h3PathSqrtEnergyRiccatiCoefficient *
              Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
        (w (v k) ≤
            (velocityH3EnergyAt u (t (v k)) - 1) /
              h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ∨
         h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ≤
           16 * (velocityH3EnergyAt u (t (v k)) - 1) *
             (max 1 (σ (v k)) + 1) ^ 4 ∨
         (max 1 (σ (v k)) + 1 <
            3 + 2 * h3AuditInitialLerayEnergyCoefficient * E k ∨
          (4 * q (v k)) ^ 2 < 24 * (C k) ^ 2 ∨
          (4 * q (v k)) ^ 2 < 8 * velocityH3DissipationAt u (t (v k)) ∨
          (4 * q (v k)) ^ 2 < 8 *
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))))) ∧
      (∀ k : ℕ,
        8 * h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ≤
          (4 * q (v k)) ^ 2 →
        (∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            h3PathSqrtEnergyRiccatiCoefficient *
              Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
        (w (v k) ≤
            (velocityH3EnergyAt u (t (v k)) - 1) /
              h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ∨
         h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ≤
           16 * (velocityH3EnergyAt u (t (v k)) - 1) *
             (max 1 (σ (v k)) + 1) ^ 4 ∨
         (max 1 (σ (v k)) + 1 <
            3 + 2 * h3AuditInitialLerayEnergyCoefficient * E k ∨
          (4 * q (v k)) ^ 2 < 24 * (C k) ^ 2 ∨
          (4 * q (v k)) ^ 2 < 8 * velocityH3DissipationAt u (t (v k))))) := by
  obtain ⟨_i, t, w, v, C, E, A, B, δ,
      hv, hLimit, hSep, hCosts, hWindows⟩ :=
    h3Critical_noL2Trace_cofinalFivefold_explicitPhysicalPDEFactorGate
      hH3 hClass b hb hNoTrace c ρ σ M q hc hcLimit hρ hσ hM hq
  have hPhysical (k : ℕ) :
      (∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
        h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
          h3PathSqrtEnergyRiccatiCoefficient *
            Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
      (w (v k) ≤
          (velocityH3EnergyAt u (t (v k)) - 1) /
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ∨
       h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ≤
         16 * (velocityH3EnergyAt u (t (v k)) - 1) *
           (max 1 (σ (v k)) + 1) ^ 4 ∨
       (max 1 (σ (v k)) + 1 <
          3 + 2 * h3AuditInitialLerayEnergyCoefficient * E k ∨
        (4 * q (v k)) ^ 2 < 24 * (C k) ^ 2 ∨
        (4 * q (v k)) ^ 2 < 8 * velocityH3DissipationAt u (t (v k)) ∨
        (4 * q (v k)) ^ 2 < 8 *
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)))) := by
    obtain ⟨_ht, hw, _hEnd, _hC0, hE0, hCeil, hA, hB, _hδ, _hδw,
        _hWidth, hOldAlt⟩ := hWindows k
    rcases hOldAlt with hLarge | ⟨_hEnergy, hChoices⟩
    · exact Or.inl hLarge
    · rcases hChoices with hShort | hChoices
      · exact Or.inr (Or.inl hShort)
      · rcases hChoices with hCutoff | hPDE
        · exact Or.inr (Or.inr (Or.inl hCutoff))
        · obtain ⟨_hThreshold, _hCharge, hFactors⟩ := hPDE
          have hStart : t (v k) ∈ Set.Icc
              (t (v k)) (t (v k) + w (v k)) :=
            ⟨le_rfl, le_add_of_nonneg_right hw.le⟩
          have hStateCeil :
              ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ ≤ E k :=
            (hCeil (t (v k)) hStart).2
          have hCL : 0 ≤ h3AuditInitialLerayEnergyCoefficient :=
            h3AuditInitialLerayEnergyCoefficient_nonneg
          have hApos : 0 ≤ A k := by
            rw [hA]
            have hSum : 0 ≤
                ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ + E k :=
              add_nonneg (norm_nonneg _) hE0
            have hProd := mul_nonneg hCL hSum
            linarith only [hProd]
          -- The accepted cofinal theorem has already unfolded the physical
          -- A/B formulas in its factor disjunction. Reconstruct the abstract
          -- A/B alternative expected by the scalar factor-split lemma.
          have hFactorsAB :
              max 1 (σ (v k)) + 1 < |A k| ∨
                (4 * q (v k)) ^ 2 < B k := by
            rcases hFactors with hState | hViscous
            · left
              have hStateA :
                  max 1 (σ (v k)) + 1 < A k := by
                simpa only [hA] using hState
              simpa only [abs_of_nonneg hApos] using hStateA
            · right
              simpa only [hB] using hViscous
          have hSplit := h3Critical_scalar_explicitAB_forces_physicalFourWay
            (max 1 (σ (v k)) + 1) (4 * q (v k))
            h3AuditInitialLerayEnergyCoefficient
            ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖
            (E k) (C k) (velocityH3DissipationAt u (t (v k)))
            (h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)))
            (A k) (B k) hCL hStateCeil hApos hA hB hFactorsAB
          exact Or.inr (Or.inr (Or.inr hSplit))
  have hThree (k : ℕ)
      (hFloorSmall : 8 * h3CriticalSourceExcessEnhancedFloor
          (M (v k)) (q (v k)) ≤ (4 * q (v k)) ^ 2) :
      (∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
        h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
          h3PathSqrtEnergyRiccatiCoefficient *
            Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
      (w (v k) ≤
          (velocityH3EnergyAt u (t (v k)) - 1) /
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ∨
       h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ≤
         16 * (velocityH3EnergyAt u (t (v k)) - 1) *
           (max 1 (σ (v k)) + 1) ^ 4 ∨
       (max 1 (σ (v k)) + 1 <
          3 + 2 * h3AuditInitialLerayEnergyCoefficient * E k ∨
        (4 * q (v k)) ^ 2 < 24 * (C k) ^ 2 ∨
        (4 * q (v k)) ^ 2 < 8 * velocityH3DissipationAt u (t (v k)))) := by
    rcases hPhysical k with hLarge | hAlt
    · exact Or.inl hLarge
    · rcases hAlt with hShort | hAlt
      · exact Or.inr (Or.inl hShort)
      · rcases hAlt with hCutoff | hFour
        · exact Or.inr (Or.inr (Or.inl hCutoff))
        · rcases hFour with hState | hRest
          · exact Or.inr (Or.inr (Or.inr (Or.inl hState)))
          · rcases hRest with hSource | hRest
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hSource))))
            · rcases hRest with hDiss | hHeight
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hDiss))))
              · exact False.elim ((not_lt_of_ge hFloorSmall) hHeight)
  refine ⟨t, w, v, C, E, A, B, δ,
    hv, hLimit, hSep, hCosts, ?_, hPhysical, ?_⟩
  · intro k
    obtain ⟨ht, hw, hEnd, hC0, hE0, hCeil, hA, hB,
        hδ, hδw, hWidth, _hAlt⟩ := hWindows k
    exact ⟨ht, hw, hEnd, hC0, hE0, hCeil, hA, hB,
      hδ, hδw, hWidth⟩
  · intro k hFloor
    exact hThree k hFloor

end
end PrimeTensor.Bridge.Euclidean
