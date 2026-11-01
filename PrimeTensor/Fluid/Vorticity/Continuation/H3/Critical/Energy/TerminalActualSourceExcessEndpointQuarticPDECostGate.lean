import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointEnergyQuarticGate
import Mathlib.Tactic

/-!
# Quartic source clock: cutoff-only growth or physical PDE cost

The endpoint drain branch in the accepted quintic source windows demands
H <= (E(start)-1) * R^4, where the *actual calibrated* radius is
R = S + sqrt(A^2*B)/P, S=max 1 sigma+1, P=4q.

The square root is not assumed to have a nonnegative radicand. Instead,
if the cutoff alone cannot supply the radius, the inequality itself forces
A^2*B > S^2*P^2 > 0, and a sharp quadratic physical PDE cost:

    H*P^4 <= 16*(E(start)-1)*(A^2*B)^2.

Thus no separate positivity hypothesis on the selected B is needed. The
large-Riccati-energy and geometric-compression alternatives are preserved.
No terminal integrability or uniform PDE bound is asserted.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- If the calibrated fourth-power radius is bounded by the cutoff alone,
the source height is at most sixteen times the cutoff-only energy budget.
Otherwise the actual PDE radicand must exceed the cutoff square. This also
works for a negative radicand, since the real square root then vanishes. -/
theorem h3Critical_scalar_quarticRadius_cutoffOr_positivePDEThreshold
    (S P K J H : ℝ) (hS : 0 ≤ S) (hP : 0 < P) (hJ : 0 ≤ J)
    (hHeight : H ≤ J * (S + Real.sqrt K / P) ^ 4) :
    H ≤ 16 * J * S ^ 4 ∨ S ^ 2 * P ^ 2 < K := by
  by_cases hPDE : S ^ 2 * P ^ 2 < K
  · exact Or.inr hPDE
  · left
    have hKle : K ≤ (S * P) ^ 2 := by
      calc
        K ≤ S ^ 2 * P ^ 2 := le_of_not_gt hPDE
        _ = (S * P) ^ 2 := by ring
    have hSP : 0 ≤ S * P := mul_nonneg hS hP.le
    have hRoot : Real.sqrt K ≤ S * P :=
      (Real.sqrt_le_iff).2 ⟨hSP, hKle⟩
    have hDiv : Real.sqrt K / P ≤ S := by
      apply (div_le_iff₀ hP).2
      simpa only [mul_comm] using hRoot
    have hRnonneg : 0 ≤ S + Real.sqrt K / P :=
      add_nonneg hS (div_nonneg (Real.sqrt_nonneg _) hP.le)
    have hRle : S + Real.sqrt K / P ≤ 2 * S := by
      linarith only [hDiv]
    have hPow : (S + Real.sqrt K / P) ^ 4 ≤ (2 * S) ^ 4 :=
      pow_le_pow_left₀ hRnonneg hRle 4
    calc
      H ≤ J * (S + Real.sqrt K / P) ^ 4 := hHeight
      _ ≤ J * (2 * S) ^ 4 := mul_le_mul_of_nonneg_left hPow hJ
      _ = 16 * J * S ^ 4 := by ring

/-- Once the source height exceeds the cutoff-only fourth-power budget,
the radicand is strictly positive and itself carries a quadratic PDE cost.
No assumption `0 <= K` is needed: it is a consequence of the cutoff failure. -/
theorem h3Critical_scalar_quarticRadius_PDEcost_after_cutoffFailure
    (S P K J H : ℝ) (hS : 0 ≤ S) (hP : 0 < P) (hJ : 0 ≤ J)
    (hHeight : H ≤ J * (S + Real.sqrt K / P) ^ 4)
    (hCutoffFailure : 16 * J * S ^ 4 < H) :
    S ^ 2 * P ^ 2 < K ∧ H * P ^ 4 ≤ 16 * J * K ^ 2 := by
  have hPDE : S ^ 2 * P ^ 2 < K := by
    rcases h3Critical_scalar_quarticRadius_cutoffOr_positivePDEThreshold
      S P K J H hS hP hJ hHeight with hCutoff | hPositive
    · exact False.elim ((not_lt_of_ge hCutoff) hCutoffFailure)
    · exact hPositive
  have hSP : 0 ≤ S * P := mul_nonneg hS hP.le
  have hK : 0 ≤ K := by
    have hSquare : 0 ≤ S ^ 2 * P ^ 2 :=
      mul_nonneg (sq_nonneg S) (sq_nonneg P)
    exact le_trans hSquare hPDE.le
  have hSPsquare : (S * P) ^ 2 ≤ K := by
    calc
      (S * P) ^ 2 = S ^ 2 * P ^ 2 := by ring
      _ ≤ K := hPDE.le
  have hSPle : S * P ≤ Real.sqrt K :=
    (Real.le_sqrt hSP hK).2 hSPsquare
  let Y : ℝ := Real.sqrt K
  have hSum0 : 0 ≤ S * P + Y :=
    add_nonneg hSP (Real.sqrt_nonneg _)
  have hSumLe : S * P + Y ≤ 2 * Y := by
    dsimp only [Y]
    linarith only [hSPle]
  have hFourth : (S * P + Y) ^ 4 ≤ (2 * Y) ^ 4 :=
    pow_le_pow_left₀ hSum0 hSumLe 4
  have hProduct : (S + Y / P) * P = S * P + Y := by
    dsimp only [Y]
    field_simp [ne_of_gt hP]
    <;> ring
  have hFourthIdentity : (S + Y / P) ^ 4 * P ^ 4 =
      (S * P + Y) ^ 4 := by
    calc
      (S + Y / P) ^ 4 * P ^ 4 = ((S + Y / P) * P) ^ 4 := by ring
      _ = (S * P + Y) ^ 4 := by rw [hProduct]
  have hYSq : Y ^ 2 = K := Real.sq_sqrt hK
  refine ⟨hPDE, ?_⟩
  calc
    H * P ^ 4 ≤ (J * (S + Y / P) ^ 4) * P ^ 4 := by
      exact mul_le_mul_of_nonneg_right hHeight (pow_nonneg hP.le 4)
    _ = J * (S * P + Y) ^ 4 := by
      calc
        (J * (S + Y / P) ^ 4) * P ^ 4 =
            J * ((S + Y / P) ^ 4 * P ^ 4) := by ring
        _ = J * (S * P + Y) ^ 4 := by rw [hFourthIdentity]
    _ ≤ J * (2 * Y) ^ 4 := mul_le_mul_of_nonneg_left hFourth hJ
    _ = 16 * J * K ^ 2 := by rw [← hYSq]; ring

/-- An exact quartic endpoint height demand has a fully quantified
cutoff-or-physical-PDE-cost alternative, with no sign assumption on K. -/
theorem h3Critical_scalar_quarticRadius_cutoffOr_quadraticPDECost
    (S P K J H : ℝ) (hS : 0 ≤ S) (hP : 0 < P) (hJ : 0 ≤ J)
    (hHeight : H ≤ J * (S + Real.sqrt K / P) ^ 4) :
    H ≤ 16 * J * S ^ 4 ∨
      (S ^ 2 * P ^ 2 < K ∧ H * P ^ 4 ≤ 16 * J * K ^ 2) := by
  by_cases hCutoff : H ≤ 16 * J * S ^ 4
  · exact Or.inl hCutoff
  · right
    have hFailure : 16 * J * S ^ 4 < H := lt_of_not_ge hCutoff
    exact h3Critical_scalar_quarticRadius_PDEcost_after_cutoffFailure
      S P K J H hS hP hJ hHeight hFailure

/-- On the exact cofinal source-driven Navier--Stokes windows, a calibrated
endpoint-energy drain is paid by one of three mechanisms: original width
compression, cutoff-only fourth-power growth, or actual local spectral/PDE
cost A²B strong enough to support the source height at quadratic order.
The Riccati-energy alternative remains. Importantly, positivity of the
physical radicand is *concluded* in the PDE branch rather than assumed. -/
theorem h3Critical_noL2Trace_cofinalQuintic_endpointQuarticPDECostGate
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
        0 < δ k ∧
        min (w (v k))
          (1 / (h3CriticalSourcePeakSquareRootRadius
            (σ (v k)) (4 * q (v k)) (A k) (B k)) ^ 4) ≤ δ k ∧
        ((∃ s : ℝ, s ∈ Set.Icc (t (v k)) (t (v k) + δ k) ∧
            h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) <
              h3PathSqrtEnergyRiccatiCoefficient *
                Real.sqrt (velocityH3EnergyAt u s) * velocityH3EnergyAt u s) ∨
          (1 < velocityH3EnergyAt u (t (v k)) ∧
            (w (v k) ≤
                (velocityH3EnergyAt u (t (v k)) - 1) /
                  h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ∨
             h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) ≤
                16 * (velocityH3EnergyAt u (t (v k)) - 1) *
                  (max 1 (σ (v k)) + 1) ^ 4 ∨
             ((max 1 (σ (v k)) + 1) ^ 2 * (4 * q (v k)) ^ 2 <
                  (A k) ^ 2 * B k ∧
               h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k)) *
                   (4 * q (v k)) ^ 4 ≤
                 16 * (velocityH3EnergyAt u (t (v k)) - 1) *
                   ((A k) ^ 2 * B k) ^ 2))))) := by
  obtain ⟨t, w, v, A, B, δ, hv, hLimit, hSeparated, hGates⟩ :=
    h3Critical_noL2Trace_cofinalQuintic_endpointEnergyQuarticGate
      hH3 hClass b hb hNoTrace c ρ σ M q hc hcLimit hρ hσ hM hq
  refine ⟨t, w, v, A, B, δ, hv, hLimit, hSeparated, ?_⟩
  intro k
  obtain ⟨hδ, hWidth, hAlt⟩ := hGates k
  refine ⟨hδ, hWidth, ?_⟩
  rcases hAlt with hLarge | ⟨hEnergy, hCompression | hRadius⟩
  · exact Or.inl hLarge
  · exact Or.inr ⟨hEnergy, Or.inl hCompression⟩
  · let H : ℝ := h3CriticalSourceExcessEnhancedFloor (M (v k)) (q (v k))
    let J : ℝ := velocityH3EnergyAt u (t (v k)) - 1
    let S : ℝ := max 1 (σ (v k)) + 1
    let P : ℝ := 4 * q (v k)
    let K : ℝ := (A k) ^ 2 * B k
    have hJ : 0 < J := by
      dsimp only [J]
      linarith only [hEnergy]
    have hS : 0 ≤ S := by
      dsimp only [S]
      have hMax : (1 : ℝ) ≤ max 1 (σ (v k)) := le_max_left _ _
      linarith only [hMax]
    have hP : 0 < P := by
      dsimp only [P]
      exact mul_pos (by norm_num) (hq (v k))
    have hRadiusScalar : H / J ≤ (S + Real.sqrt K / P) ^ 4 := by
      change H / J ≤ (S + Real.sqrt K / P) ^ 4 at hRadius
      exact hRadius
    have hHeight : H ≤ J * (S + Real.sqrt K / P) ^ 4 := by
      have hMul := (div_le_iff₀ hJ).mp hRadiusScalar
      calc
        H ≤ (S + Real.sqrt K / P) ^ 4 * J := hMul
        _ = J * (S + Real.sqrt K / P) ^ 4 := mul_comm _ _
    rcases h3Critical_scalar_quarticRadius_cutoffOr_quadraticPDECost
      S P K J H hS hP hJ.le hHeight with hCutoff | hPDE
    · exact Or.inr ⟨hEnergy, Or.inr (Or.inl hCutoff)⟩
    · exact Or.inr ⟨hEnergy, Or.inr (Or.inr hPDE)⟩

end
end PrimeTensor.Bridge.Euclidean
