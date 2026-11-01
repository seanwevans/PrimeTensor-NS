import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointQuarticPDECostGate
import Mathlib.Tactic

/-!
# Actual cofinal quartic PDE costs split into physical coefficient factors

The accepted no-terminal-trace cofinal source theorem has the genuine
physical PDE alternative K=A^2*B > S^2*P^2 and H*P^4 <= 16*J*K^2,
where S=max(1,sigma)+1, P=4*q, J=E(start)-1.

These are constraints on the SAME selected PDE coefficients and windows.
The first inequality forces either a large |A| (the spectral-state factor)
or large B (the projected source/dissipation factor). More sharply, a
positive quadratic budget overdraft against any proposed ceilings L,Q
forces |A|>L or B>Q when the geometric-compression, cutoff, and Riccati
branches have been excluded. No global or terminal upper bound is assumed.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A strict positive threshold on the product A²B forces a growth of
at least one of its two genuine physical factors. In particular, positive
PDE-cost product implies B>0 without a separate sign hypothesis. -/
theorem h3Critical_scalar_positiveQuarticPDECost_forces_factorEscape
    (S P A B : ℝ) (_hS : 0 ≤ S) (_hP : 0 < P)
    (hCost : S ^ 2 * P ^ 2 < A ^ 2 * B) :
    S < |A| ∨ P ^ 2 < B := by
  by_cases hState : S < |A|
  · exact Or.inl hState
  · right
    have hALe : |A| ≤ S := le_of_not_gt hState
    have hASq : A ^ 2 ≤ S ^ 2 := by
      simpa only [sq_abs] using
        (pow_le_pow_left₀ (abs_nonneg A) hALe 2)
    have hBPos : 0 < B := by
      by_contra hNot
      have hBLe : B ≤ 0 := le_of_not_gt hNot
      have hProdLe : A ^ 2 * B ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg A) hBLe
      have hThresholdNonneg : 0 ≤ S ^ 2 * P ^ 2 :=
        mul_nonneg (sq_nonneg S) (sq_nonneg P)
      linarith only [hProdLe, hThresholdNonneg, hCost]
    by_contra hNot
    have hBLe : B ≤ P ^ 2 := le_of_not_gt hNot
    have hProductLe : A ^ 2 * B ≤ S ^ 2 * P ^ 2 := by
      calc
        A ^ 2 * B ≤ S ^ 2 * B :=
          mul_le_mul_of_nonneg_right hASq hBPos.le
        _ ≤ S ^ 2 * P ^ 2 :=
          mul_le_mul_of_nonneg_left hBLe (sq_nonneg S)
    exact (not_lt_of_ge hProductLe) hCost

/-- If the actual quadratic PDE-cost bound holds and proposed nonnegative
ceilings L and Q cannot pay it, at least one actual factor exceeds its
ceiling. Neither sign nor integrability of the physical B factor is assumed;
its positive sign follows from the strictly positive product. -/
theorem h3Critical_scalar_quadraticQuarticPDECost_forces_factorEscape
    (H P J A B L Q : ℝ)
    (hJ : 0 ≤ J) (hL : 0 ≤ L) (_hQ : 0 ≤ Q)
    (hK : 0 < A ^ 2 * B)
    (hCharge : H * P ^ 4 ≤ 16 * J * (A ^ 2 * B) ^ 2)
    (hOverdraft : 16 * J * (L ^ 2 * Q) ^ 2 < H * P ^ 4) :
    L < |A| ∨ Q < B := by
  by_cases hA : L < |A|
  · exact Or.inl hA
  · by_cases hB : Q < B
    · exact Or.inr hB
    · exfalso
      have hALe : |A| ≤ L := le_of_not_gt hA
      have hBLe : B ≤ Q := le_of_not_gt hB
      have hASq : A ^ 2 ≤ L ^ 2 := by
        simpa only [sq_abs] using
          (pow_le_pow_left₀ (abs_nonneg A) hALe 2)
      have hBPos : 0 < B := by
        by_contra hNot
        have hBNonpos : B ≤ 0 := le_of_not_gt hNot
        have hProductNonpos : A ^ 2 * B ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sq_nonneg A) hBNonpos
        exact (not_lt_of_ge hProductNonpos) hK
      have hProductLe : A ^ 2 * B ≤ L ^ 2 * Q := by
        calc
          A ^ 2 * B ≤ L ^ 2 * B :=
            mul_le_mul_of_nonneg_right hASq hBPos.le
          _ ≤ L ^ 2 * Q :=
            mul_le_mul_of_nonneg_left hBLe (sq_nonneg L)
      have hSquareLe : (A ^ 2 * B) ^ 2 ≤ (L ^ 2 * Q) ^ 2 :=
        pow_le_pow_left₀ hK.le hProductLe 2
      have hScaled : 16 * J * (A ^ 2 * B) ^ 2 ≤
          16 * J * (L ^ 2 * Q) ^ 2 :=
        mul_le_mul_of_nonneg_left hSquareLe (by positivity)
      have hCannot : H * P ^ 4 ≤ 16 * J * (L ^ 2 * Q) ^ 2 :=
        hCharge.trans hScaled
      exact (not_lt_of_ge hCannot) hOverdraft

/-- Keep the ORIGINAL cofinal quintic source witnesses. Every selected
window either has its Riccati-energy observation, compresses geometrically,
is paid by the cutoff, or forces a large spectral/PDE coefficient factor.

Moreover, on a fixed window if the available energy cannot pay its width,
the cutoff-only budget fails, and proposed simultaneous |A| and B ceilings
cannot pay the quadratic PDE cost, the result is a genuine physical
factor spike against either proposed ceiling. -/
theorem h3Critical_noL2Trace_cofinalQuintic_quarticPDEFactorEscape
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
    ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ, ∃ A B δ : ℕ → ℝ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ k < t (v l)) ∧
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
         (max 1 (σ (v k)) + 1 < |A k| ∨
           (4 * q (v k)) ^ 2 < B k))) ∧
      (∀ k : ℕ, ∀ L Q : ℝ, 0 ≤ L → 0 ≤ Q →
        velocityH3EnergyAt u (t (v k)) - 1 <
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) * w (v k) →
        16 * (velocityH3EnergyAt u (t (v k)) - 1) *
          (max 1 (σ (v k)) + 1) ^ 4 <
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) →
        16 * (velocityH3EnergyAt u (t (v k)) - 1) *
          (L ^ 2 * Q) ^ 2 <
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) *
              (4 * q (v k)) ^ 4 →
        (∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
            h3PathSqrtEnergyRiccatiCoefficient *
              Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
        L < |A k| ∨ Q < B k) := by
  obtain ⟨t, w, v, A, B, δ, hv, hLimit, hSep, hWindows⟩ :=
    h3Critical_noL2Trace_cofinalQuintic_endpointQuarticPDECostGate
      hH3 hClass b hb hNoTrace c ρ σ M q hc hcLimit hρ hσ hM hq
  have hFactor (k : ℕ) :
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
       (max 1 (σ (v k)) + 1 < |A k| ∨ (4 * q (v k)) ^ 2 < B k)) := by
    rcases hWindows k with ⟨_hδ, _hWidth, hAlt⟩
    rcases hAlt with hLarge | ⟨_hEnergy, hChoices⟩
    · exact Or.inl hLarge
    · rcases hChoices with hShort | hChoices
      · exact Or.inr (Or.inl hShort)
      · rcases hChoices with hCutoff | hPDE
        · exact Or.inr (Or.inr (Or.inl hCutoff))
        · have hS : 0 ≤ max 1 (σ (v k)) + 1 := by
            have hMax : (1 : ℝ) ≤ max 1 (σ (v k)) := le_max_left _ _
            linarith only [hMax]
          have hP : 0 < 4 * q (v k) :=
            mul_pos (by norm_num) (hq (v k))
          have hFactors :=
            h3Critical_scalar_positiveQuarticPDECost_forces_factorEscape
              (max 1 (σ (v k)) + 1) (4 * q (v k)) (A k) (B k)
              hS hP hPDE.1
          exact Or.inr (Or.inr (Or.inr hFactors))
  refine ⟨t, w, v, A, B, δ, hv, hLimit, hSep, hFactor, ?_⟩
  intro k L Q hL hQ hNoCompression hCutoffFail hOverdraft
  rcases hWindows k with ⟨_hδ, _hWidth, hAlt⟩
  rcases hAlt with hLarge | ⟨hEnergy, hChoices⟩
  · exact Or.inl hLarge
  · rcases hChoices with hShort | hChoices
    · have hκ : 0 < 3 * (3 + h3AuditInitialLerayEnergyCoefficient) := by
        have hCL := h3AuditInitialLerayEnergyCoefficient_nonneg
        positivity
      have hH : 0 < h3CriticalSourceExcessEnhancedFloor
          (M (v k)) (q (v k)) := by
        dsimp only [h3CriticalSourceExcessEnhancedFloor]
        exact add_pos_of_nonneg_of_pos (hM (v k))
          (div_pos (hq (v k)) hκ)
      have hCharge :
          h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) * w (v k) ≤
            velocityH3EnergyAt u (t (v k)) - 1 := by
        have hMul := (le_div_iff₀ hH).mp hShort
        simpa only [mul_comm] using hMul
      exact False.elim ((not_lt_of_ge hCharge) hNoCompression)
    · rcases hChoices with hCutoff | hPDE
      · exact False.elim ((not_lt_of_ge hCutoff) hCutoffFail)
      · have hJ : 0 ≤ velocityH3EnergyAt u (t (v k)) - 1 := by
          linarith only [hEnergy]
        have hProduct0 : 0 ≤
            (max 1 (σ (v k)) + 1) ^ 2 * (4 * q (v k)) ^ 2 :=
          mul_nonneg (sq_nonneg _) (sq_nonneg _)
        have hK : 0 < (A k) ^ 2 * B k :=
          lt_of_le_of_lt hProduct0 hPDE.1
        exact Or.inr
          (h3Critical_scalar_quadraticQuarticPDECost_forces_factorEscape
            (h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)))
            (4 * q (v k)) (velocityH3EnergyAt u (t (v k)) - 1)
            (A k) (B k) L Q hJ hL hQ hK hPDE.2 hOverdraft)

end
end PrimeTensor.Bridge.Euclidean
