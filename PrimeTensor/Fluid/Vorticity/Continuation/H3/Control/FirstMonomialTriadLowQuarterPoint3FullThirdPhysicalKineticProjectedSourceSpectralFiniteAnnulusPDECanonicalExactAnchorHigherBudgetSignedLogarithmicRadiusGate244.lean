import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudgetSignedExponentialSecant244
import Mathlib.Tactic

/-!
# Signed logarithmic radius gate at the original canonical H³ anchors

The committed physical signed log-secant gate has

  R^(16m+3) <= A * (B * exp((t-b)*g(s)) + 1)^4

with A=(512*eps²)^4 D^5, B=2304 E₃(b) S² and g the exact
positive normalized full-dissipation transport excess. Since s lies
between b and t, its nonnegative rate gives x=(t-b)*g(s) >= 0,
so B exp x+1 <= (B+1) exp x. Taking an ordinary real logarithm yields

  (16m+3) log R <= log(A*(B+1)^4) + 4 (t-b) g(s).

A is NOT assumed positive: the already-established R>=1 fourth-power
inequality forces A>0, making the logarithm legitimate. The resulting
finite-gap variant replaces t-b by T-b with g>=0.

This is conditional: the higher radial moment majorant, attained projected
source bound, critical annular cap and noncompressed clock are unchanged.
No unconditional physical transport upper bound is proved here.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Fourth-power exponential radius growth forces a LOGARITHMIC lower
budget on the exponential time-action. Positivity of A is derived from
the existing cost, not added as a separate assumption. -/
theorem h3Path_higherBudget_signedExpFourth_forces_logRadiusBudget244
    (R A B x : ℝ) (m : ℕ)
    (hR : 1 ≤ R) (hB : 0 ≤ B) (hx : 0 ≤ x)
    (hCost : R ^ (16 * m + 3) ≤ A * (B * Real.exp x + 1) ^ 4) :
    ((16 * m + 3 : ℕ) : ℝ) * Real.log R ≤
      Real.log (A * (B + 1) ^ 4) + 4 * x := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  have hRPow : 0 < R ^ (16 * m + 3) := pow_pos hRpos _
  have hExpOne : 1 ≤ Real.exp x := by
    have hExp := Real.add_one_le_exp x
    linarith only [hExp, hx]
  have hInnerNonneg : 0 ≤ B * Real.exp x + 1 := by
    have hMul : 0 ≤ B * Real.exp x :=
      mul_nonneg hB (Real.exp_pos x).le
    linarith only [hMul]
  have hA : 0 < A := by
    by_contra hn
    have hAle : A ≤ 0 := le_of_not_gt hn
    have hUpper : A * (B * Real.exp x + 1) ^ 4 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hAle (pow_nonneg hInnerNonneg _)
    have hLower : 0 < A * (B * Real.exp x + 1) ^ 4 :=
      lt_of_lt_of_le hRPow hCost
    exact (not_lt_of_ge hUpper) hLower
  have hInner : B * Real.exp x + 1 ≤ (B + 1) * Real.exp x := by
    calc
      B * Real.exp x + 1 ≤ B * Real.exp x + Real.exp x :=
        by linarith only [hExpOne]
      _ = (B + 1) * Real.exp x := by ring
  have hFourth : (B * Real.exp x + 1) ^ 4 ≤
      ((B + 1) * Real.exp x) ^ 4 :=
    pow_le_pow_left₀ hInnerNonneg hInner 4
  have hScaled := mul_le_mul_of_nonneg_left hFourth hA.le
  have hBound : R ^ (16 * m + 3) ≤
      A * ((B + 1) * Real.exp x) ^ 4 :=
    le_trans hCost hScaled
  have hBP : 0 < B + 1 := by linarith only [hB]
  have hBExp : 0 < (B + 1) * Real.exp x :=
    mul_pos hBP (Real.exp_pos x)
  have hLogBound : Real.log (R ^ (16 * m + 3)) ≤
      Real.log (A * ((B + 1) * Real.exp x) ^ 4) :=
    Real.log_le_log hRPow hBound
  have hLogLeft : Real.log (R ^ (16 * m + 3)) =
      ((16 * m + 3 : ℕ) : ℝ) * Real.log R := by
    rw [Real.log_pow]
  have hLogRight : Real.log (A * ((B + 1) * Real.exp x) ^ 4) =
      Real.log (A * (B + 1) ^ 4) + 4 * x := by
    calc
      Real.log (A * ((B + 1) * Real.exp x) ^ 4) =
          Real.log A + Real.log (((B + 1) * Real.exp x) ^ 4) :=
        Real.log_mul (ne_of_gt hA) (ne_of_gt (pow_pos hBExp 4))
      _ = Real.log A + 4 * (Real.log (B + 1) + x) := by
        rw [Real.log_pow,
          Real.log_mul (ne_of_gt hBP) (ne_of_gt (Real.exp_pos x)),
          Real.log_exp]
        ring
      _ = Real.log (A * (B + 1) ^ 4) + 4 * x := by
        rw [Real.log_mul (ne_of_gt hA) (ne_of_gt (pow_pos hBP 4)),
          Real.log_pow]
        ring
  rw [hLogLeft, hLogRight] at hLogBound
  exact hLogBound

/-- A finite terminal gap turns the logarithmic budget into a uniform
T-b signed-rate cost. No pointwise bound for g is assumed. -/
theorem h3Path_higherBudget_logRadiusBudget_to_terminalGap244
    (R A B g b t T : ℝ) (m : ℕ)
    (hR : 1 ≤ R) (hB : 0 ≤ B)
    (hbt : b < t) (htT : t < T) (hg : 0 ≤ g)
    (hCost : R ^ (16 * m + 3) ≤
      A * (B * Real.exp ((t - b) * g) + 1) ^ 4) :
    ((16 * m + 3 : ℕ) : ℝ) * Real.log R ≤
      Real.log (A * (B + 1) ^ 4) + 4 * (T - b) * g := by
  have hx : 0 ≤ (t - b) * g :=
    mul_nonneg (sub_nonneg.mpr hbt.le) hg
  have hLog := h3Path_higherBudget_signedExpFourth_forces_logRadiusBudget244
    R A B ((t - b) * g) m hR hB hx hCost
  have hGap : t - b ≤ T - b := by linarith only [htT]
  have hRate : (t - b) * g ≤ (T - b) * g :=
    mul_le_mul_of_nonneg_right hGap hg
  linarith only [hLog, hRate]

/-- The SAME all-orders canonical anchors exhibit an explicit logarithmic
radius forcing rate at an intermediate physical time. C_b is constant in
k: it depends only on fixed b, S, D and epsilon. -/
theorem h3Path_noL2Trace_exactAnchor_higherBudget_signedLogRadiusGate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
    ∃ hτ : (∀ n, τ n ∈ Set.Ioo a T),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2)) ∧
      (∀ m : ℕ, ∀ F : ℝ → ℝ,
        (∀ s : ℝ, 0 ≤ F s) →
        IntervalIntegrable F volume a T →
        (∀ s : ℝ, ∀ hs : s ∈ Set.Ioo a T,
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass m s hs ≤ ENNReal.ofReal (F s)) →
        ∀ S D η ε : ℝ,
          0 ≤ S → 0 ≤ D → 0 < η → 0 < ε → ε < η →
          16 * ε ^ 2 * (36 * S ^ 2 * (D + 256) + 1) < 1 →
          (∀ᶠ k : ℕ in atTop, C (v k) ≤ S) →
          (∀ᶠ k : ℕ in atTop,
            ((N (v k) : ℝ) + 2) ^ 8 ≤ D * ((v k : ℝ) + 1) ^ 9) →
          (∀ᶠ k : ℕ in atTop,
            η ≤ ((v k : ℝ) + 1) ^ (2 * m + 3) * ((T - τ (v k)) / 4)) →
          ∀ b : ℝ, b ∈ Set.Ioo a T →
          ∀ᶠ k : ℕ in atTop,
            ∃ s : ℝ, s ∈ Set.Ioo b (τ (v k)) ∧
              ((16 * m + 3 : ℕ) : ℝ) *
                Real.log ((v k : ℝ) + 1) ≤
                Real.log (
                  ((512 * ε ^ 2) ^ 4 * D ^ 5) *
                  (2304 * velocityH3EnergyAt u b * S ^ 2 + 1) ^ 4) +
                4 * (τ (v k) - b) *
                  h3PathFullDissipationTransportExcessRate u s ∧
              ((16 * m + 3 : ℕ) : ℝ) *
                Real.log ((v k : ℝ) + 1) ≤
                Real.log (
                  ((512 * ε ^ 2) ^ 4 * D ^ 5) *
                  (2304 * velocityH3EnergyAt u b * S ^ 2 + 1) ^ 4) +
                4 * (T - b) *
                  h3PathFullDissipationTransportExcessRate u s) := by
  obtain ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
      hSeparate, hAnchor, hHigher⟩ :=
    h3Path_noL2Trace_exactAnchor_higherBudget_signedExponentialSecantGate244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
    hSeparate, hAnchor, ?_⟩
  intro m F hF hFInt hUpper S D η ε hS hD hη hε hεη
    hSmall hCeil hCap hGeom b hb
  have hExpCost := hHigher m F hF hFInt hUpper
    S D η ε hS hD hη hε hεη hSmall hCeil hCap hGeom b hb
  filter_upwards [hExpCost] with k hk
  obtain ⟨s, hs, hCost⟩ := hk
  let R : ℝ := (v k : ℝ) + 1
  let A : ℝ := (512 * ε ^ 2) ^ 4 * D ^ 5
  let B : ℝ := 2304 * velocityH3EnergyAt u b * S ^ 2
  let g : ℝ := h3PathFullDissipationTransportExcessRate u s
  have hR : 1 ≤ R := by
    dsimp only [R]
    have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hn]
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hEnergy : 0 ≤ velocityH3EnergyAt u b :=
      le_trans zero_le_one (one_le_velocityH3EnergyAt u b)
    positivity
  have hg : 0 ≤ g :=
    h3PathFullDissipationTransportExcessRate_nonneg u s
  have hbt : b < τ (v k) := lt_trans hs.1 hs.2
  have hAlgebra : R ^ (16 * m + 3) ≤
      A * (B * Real.exp ((τ (v k) - b) * g) + 1) ^ 4 := by
    dsimp only [R, A, B, g]
    convert hCost using 1 <;> ring
  have hLog := h3Path_higherBudget_signedExpFourth_forces_logRadiusBudget244
    R A B ((τ (v k) - b) * g) m hR hB
    (mul_nonneg (sub_nonneg.mpr hbt.le) hg) hAlgebra
  have hFinal := h3Path_higherBudget_logRadiusBudget_to_terminalGap244
    R A B g b (τ (v k)) T m hR hB hbt (hτ (v k)).2 hg hAlgebra
  refine ⟨s, hs, ?_, ?_⟩
  · simpa only [R, A, B, g, mul_assoc] using hLog
  · simpa only [R, A, B, g] using hFinal

end
end PrimeTensor.FirstMonomialTriad
