import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessAttainedPhysicalPDEFactorGate
import Mathlib.Tactic

/-!
# Actual H³ source-clock maxima: anchor concentration or temporal excursion

Compact-window maxima are genuine but need not belong to the calibrated
source subwindow. Decompose both physical Hilbert trajectories at the actual
source peak x. The triangle inequality forces each large attained maximum
to manifest either at the peak or as a quantified time increment from it.
No time-Lipschitz modulus or terminal-uniform continuity rate is assumed.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Every norm maximum splits into anchor amplitude plus temporal movement. -/
theorem h3Critical_norm_le_anchor_add_excursion
    {V : Type*} [NormedAddCommGroup V] (p x : V) :
    ‖p‖ ≤ ‖x‖ + ‖p - x‖ := by
  calc
    ‖p‖ = ‖x + (p - x)‖ := by
      congr 1
      abel
    _ ≤ ‖x‖ + ‖p - x‖ := norm_add_le _ _

/-- Spectral ceiling growth must reside at the peak or in actual temporal
variation, with a sharp factor-two allocation for each of the two parts. -/
theorem h3Critical_scalar_linearMax_anchorOrExcursion
    (S CL N U V : ℝ)
    (hCL : 0 ≤ CL) (hMax : N ≤ U + V)
    (hLarge : S < 3 + 2 * CL * N) :
    S < 3 + 4 * CL * U ∨ S < 3 + 4 * CL * V := by
  by_cases hAnchor : S < 3 + 4 * CL * U
  · exact Or.inl hAnchor
  · right
    have hAnchorBound : 3 + 4 * CL * U ≤ S := le_of_not_gt hAnchor
    have hScaled := mul_le_mul_of_nonneg_left hMax hCL
    nlinarith only [hLarge, hAnchorBound, hScaled]

/-- Projected-source squared maxima split into peak-source energy or
actual temporal difference energy, with the exact factor-four square loss. -/
theorem h3Critical_scalar_quadraticMax_anchorOrExcursion
    (P N U V : ℝ)
    (hN : 0 ≤ N) (hMax : N ≤ U + V)
    (_hU : 0 ≤ U) (_hV : 0 ≤ V)
    (hLarge : P ^ 2 < 24 * N ^ 2) :
    P ^ 2 < 96 * U ^ 2 ∨ P ^ 2 < 96 * V ^ 2 := by
  have hSquare : N ^ 2 ≤ (U + V) ^ 2 :=
    pow_le_pow_left₀ hN hMax 2
  have hYoung : (U + V) ^ 2 ≤ 2 * (U ^ 2 + V ^ 2) := by
    nlinarith only [sq_nonneg (U - V)]
  have hTotal : P ^ 2 < 48 * (U ^ 2 + V ^ 2) := by
    nlinarith only [hLarge, hSquare, hYoung]
  by_cases hAnchor : P ^ 2 < 96 * U ^ 2
  · exact Or.inl hAnchor
  · right
    have hAnchorBound : 96 * U ^ 2 ≤ P ^ 2 := le_of_not_gt hAnchor
    nlinarith only [hTotal, hAnchorBound]

/-- The physical source/spectral branches at attained times become
observations either at the original source peak or of real time increments.
The true viscous and source-floor branches are unchanged. -/
theorem h3Critical_attainedPhysicalPDE_anchorOrTemporalExcursion
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (x sSource sState S P D H : ℝ)
    (hPhysical :
      S < 3 + 2 * h3AuditInitialLerayEnergyCoefficient *
        ‖h3AuditActualSpectralVelocityTotal hH3 sState‖ ∨
      P ^ 2 < 24 * ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖ ^ 2 ∨
      P ^ 2 < 8 * D ∨ P ^ 2 < 8 * H) :
    (S < 3 + 4 * h3AuditInitialLerayEnergyCoefficient *
        ‖h3AuditActualSpectralVelocityTotal hH3 x‖ ∨
      S < 3 + 4 * h3AuditInitialLerayEnergyCoefficient *
        ‖h3AuditActualSpectralVelocityTotal hH3 sState -
          h3AuditActualSpectralVelocityTotal hH3 x‖) ∨
    (P ^ 2 < 96 * ‖h3PathActualProjectedMomentumSource244 hH3 x‖ ^ 2 ∨
      P ^ 2 < 96 * ‖h3PathActualProjectedMomentumSource244 hH3 sSource -
        h3PathActualProjectedMomentumSource244 hH3 x‖ ^ 2) ∨
    P ^ 2 < 8 * D ∨ P ^ 2 < 8 * H := by
  rcases hPhysical with hState | hSource | hDiss | hFloor
  · left
    exact h3Critical_scalar_linearMax_anchorOrExcursion
      S h3AuditInitialLerayEnergyCoefficient
      ‖h3AuditActualSpectralVelocityTotal hH3 sState‖
      ‖h3AuditActualSpectralVelocityTotal hH3 x‖
      ‖h3AuditActualSpectralVelocityTotal hH3 sState -
        h3AuditActualSpectralVelocityTotal hH3 x‖
      h3AuditInitialLerayEnergyCoefficient_nonneg
      (h3Critical_norm_le_anchor_add_excursion _ _) hState
  · exact Or.inr (Or.inl
      (h3Critical_scalar_quadraticMax_anchorOrExcursion
        P ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖
        ‖h3PathActualProjectedMomentumSource244 hH3 x‖
        ‖h3PathActualProjectedMomentumSource244 hH3 sSource -
          h3PathActualProjectedMomentumSource244 hH3 x‖
        (norm_nonneg _) (h3Critical_norm_le_anchor_add_excursion _ _)
        (norm_nonneg _) (norm_nonneg _) hSource))
  · exact Or.inr (Or.inr (Or.inl hDiss))
  · exact Or.inr (Or.inr (Or.inr hFloor))

/-- The exact SAME cofinal fivefold source witnesses, maxima, physical
coefficient definitions and disjoint viscous-charge inequality now satisfy
an anchor-versus-temporal-excursion PDE obstruction. Neither maximizing
observation time is assumed to lie in the shorter calibrated interval. -/
theorem h3Critical_noL2Trace_cofinalFivefold_anchoredTemporalExcursionGate
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
    ∃ sSource sState A B δ : ℕ → ℝ,
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
        sSource k ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) ∧
        sState k ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + w (v k)) →
          ‖h3PathActualProjectedMomentumSource244 hH3 s‖ ≤
            ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ ∧
          ‖h3AuditActualSpectralVelocityTotal hH3 s‖ ≤
            ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖) ∧
        A k = 3 + h3AuditInitialLerayEnergyCoefficient *
          (‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ +
            ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖) ∧
        B k = 12 * ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ ^ 2 +
          2 * (velocityH3DissipationAt u (t (v k)) +
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))) ∧
        0 < δ k ∧ δ k ≤ w (v k) ∧
        min (w (v k))
          (1 / (h3CriticalSourcePeakSquareRootRadius
            (σ (v k)) (4 * q (v k)) (A k) (B k)) ^ 4) ≤ δ k ∧
        (∀ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) →
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            velocityH3DissipationAt u s) ∧
        ((∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            h3PathSqrtEnergyRiccatiCoefficient *
              Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
         (w (v k) ≤ (velocityH3EnergyAt u (t (v k)) - 1) /
             h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ∨
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ≤
            16 * (velocityH3EnergyAt u (t (v k)) - 1) *
              (max 1 (σ (v k)) + 1) ^ 4 ∨
          (max 1 (σ (v k)) + 1 <
              3 + 4 * h3AuditInitialLerayEnergyCoefficient *
                ‖h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖ ∨
            max 1 (σ (v k)) + 1 <
              3 + 4 * h3AuditInitialLerayEnergyCoefficient *
                ‖h3AuditActualSpectralVelocityTotal hH3 (sState k) -
                  h3AuditActualSpectralVelocityTotal hH3 (t (v k))‖) ∨
          ((4 * q (v k)) ^ 2 < 96 *
               ‖h3PathActualProjectedMomentumSource244 hH3 (t (v k))‖ ^ 2 ∨
             (4 * q (v k)) ^ 2 < 96 *
               ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k) -
                 h3PathActualProjectedMomentumSource244 hH3 (t (v k))‖ ^ 2) ∨
          (4 * q (v k)) ^ 2 < 8 * velocityH3DissipationAt u (t (v k)) ∨
          (4 * q (v k)) ^ 2 < 8 *
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))))) := by
  obtain ⟨i, t, w, v, sSource, sState, A, B, δ,
      hv, hLimit, hSep, hCosts, hWindows⟩ :=
    h3Critical_noL2Trace_cofinalFivefold_attainedPhysicalPDEFactorGate
      hH3 hClass b hb hNoTrace c ρ σ M q hc hcLimit hρ hσ hM hq
  refine ⟨i, t, w, v, sSource, sState, A, B, δ,
    hv, hLimit, hSep, hCosts, ?_⟩
  intro k
  obtain ⟨ht, hw, hEnd, hsSource, hsState, hMax, hA, hB,
      hδ, hδw, hWidth, hFloor, hAlt⟩ := hWindows k
  refine ⟨ht, hw, hEnd, hsSource, hsState, hMax, hA, hB,
    hδ, hδw, hWidth, hFloor, ?_⟩
  rcases hAlt with hRiccati | hRest
  · exact Or.inl hRiccati
  · rcases hRest with hCompressed | hRest
    · exact Or.inr (Or.inl hCompressed)
    · rcases hRest with hCutoff | hPhysical
      · exact Or.inr (Or.inr (Or.inl hCutoff))
      · exact Or.inr (Or.inr (Or.inr
          (h3Critical_attainedPhysicalPDE_anchorOrTemporalExcursion
            hH3 (t (v k)) (sSource k) (sState k)
            (max 1 (σ (v k)) + 1) (4 * q (v k))
            (velocityH3DissipationAt u (t (v k)))
            (h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)))
            hPhysical)))

end
end PrimeTensor.Bridge.Euclidean
