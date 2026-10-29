import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorWindowTopHigherBudget244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorCofinal244
import Mathlib.Tactic

/-!
# Higher top-order spacetime budgets force stronger exact canonical PDE rates

On a common canonical disjoint window, an integrable real-valued majorant of
physical q^(4+m) moments implies delta_k R_k^(2m+3) -> 0. Since delta_k
is the ACTUAL quadratically sharp min-selector and the annular gap is at
least R_k^3/4, this strengthens the established cubic three-scale barrier:

  R_k^(2m+3) * (T-t_k)/4 <= eps, or
  (R_k^2)^m * R_k^6 <= 16 eps (Lambda_k+1), or
  ((R_k^2)^m)^2 * R_k^9 <= 16 eps^2 (Xi_k+1).

The extra higher-order time-integrability premise remains EXPLICIT.
This is not an unconditional regularity theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- The quadratic sharp clock's linear cap at m extra radial orders
requires the physical linear PDE coefficient to pay m additional q-powers. -/
theorem h3Path_scalar_higherRadialLinearCap_forces_rate244
    (R gap Λ ε : ℝ) (m : ℕ)
    (hR : 1 ≤ R) (hΛ : 0 ≤ Λ)
    (hGap : R ^ 3 / 4 ≤ gap)
    (hCap : ((R ^ 2) ^ m * R ^ 3) *
      (gap / (4 * (Λ + 1))) ≤ ε) :
    (R ^ 2) ^ m * R ^ 6 ≤ 16 * ε * (Λ + 1) := by
  let p : ℝ := (R ^ 2) ^ m
  have hp : 0 < p := by
    dsimp only [p]
    exact pow_pos (pow_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR) 2) m
  have hCapBase : R ^ 3 * (gap / (4 * (Λ + 1))) ≤ ε / p := by
    apply (le_div_iff₀ hp).2
    calc
      (R ^ 3 * (gap / (4 * (Λ + 1)))) * p =
          (p * R ^ 3) * (gap / (4 * (Λ + 1))) := by ring
      _ ≤ ε := by simpa only [p] using hCap
  have hBase := h3Path_quarterGap_quadraticClockLinearCap_forces_sixth244
    R gap Λ (ε / p)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR)
    hΛ hGap hCapBase
  have hScaled := mul_le_mul_of_nonneg_left hBase hp.le
  change p * R ^ 6 ≤ 16 * ε * (Λ + 1)
  calc
    p * R ^ 6 ≤
      p * (16 * (ε / p) * (Λ + 1)) := hScaled
    _ = 16 * ε * (Λ + 1) := by
      field_simp [ne_of_gt hp]
      <;> ring

/-- Quadratic source clock cap pays two extra m-th radial weights. -/
theorem h3Path_scalar_higherRadialQuadraticCap_forces_rate244
    (R gap Ξ ε : ℝ) (m : ℕ)
    (hR : 1 ≤ R) (hΞ : 0 ≤ Ξ)
    (hGap : R ^ 3 / 4 ≤ gap)
    (hCap : ((R ^ 2) ^ m * R ^ 3) *
      Real.sqrt (gap / (4 * (Ξ + 1))) ≤ ε) :
    ((R ^ 2) ^ m) ^ 2 * R ^ 9 ≤ 16 * ε ^ 2 * (Ξ + 1) := by
  let p : ℝ := (R ^ 2) ^ m
  have hp : 0 < p := by
    dsimp only [p]
    exact pow_pos (pow_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR) 2) m
  have hCapBase : R ^ 3 * Real.sqrt (gap / (4 * (Ξ + 1))) ≤ ε / p := by
    apply (le_div_iff₀ hp).2
    calc
      (R ^ 3 * Real.sqrt (gap / (4 * (Ξ + 1)))) * p =
          (p * R ^ 3) * Real.sqrt (gap / (4 * (Ξ + 1))) := by ring
      _ ≤ ε := by simpa only [p] using hCap
  have hBase := h3Path_quarterGap_quadraticClockRootCap_forces_ninth244
    R gap Ξ (ε / p)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR)
    hΞ hGap hCapBase
  have hScaled := mul_le_mul_of_nonneg_left hBase (sq_nonneg p)
  change p ^ 2 * R ^ 9 ≤ 16 * ε ^ 2 * (Ξ + 1)
  calc
    p ^ 2 * R ^ 9 ≤
      p ^ 2 * (16 * (ε / p) ^ 2 * (Ξ + 1)) := hScaled
    _ = 16 * ε ^ 2 * (Ξ + 1) := by
      field_simp [ne_of_gt hp]
      <;> ring

/-- The EXACT physical quadratic-sharp selector, together with higher
moment-induced clock compression, forces frequency-amplified temporal,
linear, or quadratic rate escape. The original cutoff is not reselected. -/
theorem h3Path_scalar_higherBudget_exactPDE_threeScale244
    (v : ℕ → ℕ) (δ b gap Λ Ξ : ℕ → ℝ) (m : ℕ)
    (hv : StrictMono v)
    (hExact : ∀ k,
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k)))
    (hCompression : Tendsto (fun k : ℕ =>
      δ (v k) * (((v k : ℝ) + 1) ^ (2 * m + 3)))
        atTop (𝓝 (0 : ℝ)))
    (hGap : ∀ k, (((v k : ℝ) + 1) ^ 3) / 4 ≤ gap (v k))
    (hΛ : ∀ k, 0 ≤ Λ (v k))
    (hΞ : ∀ k, 0 ≤ Ξ (v k)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      (((v k : ℝ) + 1) ^ (2 * m + 3)) * (b (v k) / 2) ≤ ε ∨
      ((((v k : ℝ) + 1) ^ 2) ^ m) * (((v k : ℝ) + 1) ^ 6) ≤
        16 * ε * (Λ (v k) + 1) ∨
      (((((v k : ℝ) + 1) ^ 2) ^ m) ^ 2) *
        (((v k : ℝ) + 1) ^ 9) ≤ 16 * ε ^ 2 * (Ξ (v k) + 1) := by
  intro ε hε
  have hLarge := h3Path_strictMonoCubicHeight_eventually_above_mass244 v hv ε
  have hSmall : ∀ᶠ k : ℕ in atTop,
      δ (v k) * (((v k : ℝ) + 1) ^ (2 * m + 3)) < ε :=
    hCompression.eventually (eventually_lt_nhds hε)
  filter_upwards [hLarge, hSmall] with k hkLarge hkSmall
  let R : ℝ := (v k : ℝ) + 1
  let p : ℝ := (R ^ 2) ^ m
  let A : ℝ := p * R ^ 3
  have hR : 1 ≤ R := by
    dsimp only [R]
    have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hn]
  have hp : 1 ≤ p := by
    dsimp only [p]
    have hSq : (1 : ℝ) ≤ R ^ 2 := by
      have h := pow_le_pow_left₀
        (by norm_num : (0 : ℝ) ≤ 1) hR 2
      simpa only [one_pow] using h
    have hPow := pow_le_pow_left₀
      (by norm_num : (0 : ℝ) ≤ 1) hSq m
    simpa only [one_pow] using hPow
  have hR3 : 0 < R ^ 3 := pow_pos
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR) 3
  have hA : 0 < A := mul_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp) hR3
  have hAOne : R ^ 3 ≤ A := by
    dsimp only [A]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hR3.le
  have hUnit : ε < A := by
    have hLargeR : ε < R ^ 3 := by
      dsimp only [R] at hkLarge hR3 ⊢
      linarith only [hkLarge, hR3]
    exact lt_of_lt_of_le hLargeR hAOne
  have hPow : R ^ (2 * m + 3) = A := by
    dsimp only [A, p]
    rw [pow_add, pow_mul]
  have hCost : A * δ (v k) ≤ ε := by
    calc
      A * δ (v k) = δ (v k) * R ^ (2 * m + 3) := by
        rw [hPow]
        ring
      _ ≤ ε := by simpa only [R] using hkSmall.le
  have hCaps := h3Path_quadraticSharpMin_smallCost_forces_threeCaps244
    A ε (b (v k)) (gap (v k)) (Λ (v k)) (Ξ (v k)) (δ (v k))
    hA hUnit (hExact k) hCost
  rcases hCaps with hTime | hLinear | hQuadratic
  · left
    change R ^ (2 * m + 3) * (b (v k) / 2) ≤ ε
    rw [hPow]
    exact hTime
  · right; left
    have h := h3Path_scalar_higherRadialLinearCap_forces_rate244
      R (gap (v k)) (Λ (v k)) ε m hR (hΛ k) (hGap k)
      (by simpa only [A, p] using hLinear)
    simpa only [R] using h
  · right; right
    have h := h3Path_scalar_higherRadialQuadraticCap_forces_rate244
      R (gap (v k)) (Ξ (v k)) ε m hR (hΞ k) (hGap k)
      (by simpa only [A, p] using hQuadratic)
    simpa only [R] using h

/-- Physical output: on the unreselected canonical first-crossing PDE
windows, ANY integrable majorant for a fixed actual higher top-order
moment strengthens the terminal/linear/quadratic three-scale alternative
by exactly 2m / 2m / 4m additional radial powers, respectively. -/
theorem h3Path_noL2Trace_exactAnchor_higherBudget_forces_physicalPDERates244
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
      (∀ k, K (v k) =
        ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        0 < δ (v k)) ∧
      (∀ m : ℕ, ∀ F : ℝ → ℝ,
        (∀ s : ℝ, 0 ≤ F s) →
        IntervalIntegrable F volume a T →
        (∀ s : ℝ, ∀ hs : s ∈ Set.Ioo a T,
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass m s hs ≤ ENNReal.ofReal (F s)) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
          (((v k : ℝ) + 1) ^ (2 * m + 3)) *
            (((T - τ (v k)) / 2) / 2) ≤ ε ∨
          ((((v k : ℝ) + 1) ^ 2) ^ m) *
            (((v k : ℝ) + 1) ^ 6) ≤
              16 * ε * (h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1) ∨
          (((((v k : ℝ) + 1) ^ 2) ^ m) ^ 2) *
            (((v k : ℝ) + 1) ^ 9) ≤
              16 * ε ^ 2 * (h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1)) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, _hSummable, hAll, _hBarrier, _hPeaks⟩ :=
    h3Path_noL2Trace_finiteDissipation_exactAnchorCanonicalThreeScale244
      hH3 hClass hMass hNoTrace hDInt
  have hCanonical (k : ℕ) :
      K (v k) = ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∧
      C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
        (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
      0 < δ (v k) := by
    rcases hAll k with ⟨hK, _, _, _, hC, _, hδ, _, _, _, _, _⟩
    exact ⟨hK, hC, hδ⟩
  have hWidth (k : ℕ) : 0 < δ (v k) := (hCanonical k).2.2
  have hEnd (k : ℕ) : τ (v k) + δ (v k) < T := by
    rcases hAll k with ⟨_, _, _, _, _, _, _, he, _, _, _, _⟩
    exact he
  have hExact (k : ℕ) :
      δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
        ((T - τ (v k)) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
        (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
        (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)) := by
    rcases hAll k with ⟨_, _, _, _, _, _, _, _, hx, _, _, _⟩
    exact hx
  have hGap (k : ℕ) : ((v k : ℝ) + 1) ^ 3 / 4 ≤
      h3PathCubicAnnulusActualGap244 hH3 τ N (v k) := by
    rcases hAll k with ⟨_, _, _, _, _, _, _, _, _, _, hg, _⟩
    exact hg.le
  have hΛ (k : ℕ) :
      0 ≤ h3PathCubicAnnulusActualLinearRate244 N K C (v k) := by
    have hK : 0 ≤ K (v k) := by
      rw [(hCanonical k).1]
      exact norm_nonneg _
    have hC : 0 ≤ C (v k) := by
      rcases hAll k with ⟨_, _, _, _, _, hAttain, _, _, _, _, _, _⟩
      obtain ⟨s, _hs, hNorm⟩ := hAttain
      rw [← hNorm]
      exact norm_nonneg _
    change 0 ≤ h3PathFiniteAnnulusPDEVariationCoefficient244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (K (v k)) (C (v k))
    exact h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244 _ _ _ _ hK hC
  have hΞ (k : ℕ) :
      0 ≤ h3PathCubicAnnulusActualQuadraticRate244 N C (v k) := by
    unfold h3PathCubicAnnulusActualQuadraticRate244
    exact h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))
  refine ⟨τ, N, K, C, δ, v, hTime, hv, hCofinal,
    hSeparate, hCanonical, ?_⟩
  intro m F hF hFInt hUpper ε hε
  let R : ℕ → ℝ := fun k => (v k : ℝ) + 1
  let A : ℕ → ℝ := fun k => ((R k) ^ 2) ^ m * ((R k) ^ 3 / 8)
  have hRnonneg (k : ℕ) : 0 ≤ R k := by
    dsimp only [R]
    positivity
  have hA (k : ℕ) : 0 ≤ A k := by
    dsimp only [A]
    exact mul_nonneg (pow_nonneg (sq_nonneg (R k)) m)
      (div_nonneg (pow_nonneg (hRnonneg k) 3) (by norm_num))
  have hFloor (k : ℕ) (s : ℝ)
      (hsWindow : s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k))) :
      A k ≤ F s := by
    have hsTime : s ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le (hTime (v k)).1 hsWindow.1,
        lt_of_le_of_lt hsWindow.2 (hEnd k)⟩
    have hAnn : (R k) ^ 3 / 2 <
        h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s) -
        h3PathActualLowRadialDissipation244 (R k)
          (h3AuditActualSpectralVelocityTotal hH3 s) := by
      rcases hAll k with ⟨_, _, _, _, _, _, _, _, _, hp, _, _⟩
      simpa only [R] using hp s hsWindow
    have hR : 1 ≤ R k := by
      dsimp only [R]
      have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
      linarith only [hn]
    have hMoment := h3Path_physicalHalfAnnulus_forces_windowTopHigherMoment244
      hH3 hClass s hsTime m (R k) ((N (v k) : ℝ) + 1) hR hAnn
    exact h3Path_physicalTopHigherMoment_upperEnvelope_forces_realFloor244
      hH3 hClass hsTime m (F s) (A k) (hF s)
      (by simpa only [A] using hMoment) (hUpper s hsTime)
  have hSum : Summable (fun k => δ (v k) * A k) :=
    h3Path_scalar_disjointWindows_integrableMajorant_weightedCharge244
      F a T (fun k => τ (v k)) (fun k => δ (v k)) A
      hClass.terminal_start.2.le hF hFInt
      (fun k => (hTime (v k)).1.le) (fun k => (hWidth k).le)
      (fun k => (hEnd k).le)
      (fun k => (hSeparate k (k + 1) (Nat.lt_succ_self k)).le)
      hA hFloor
  have hCompress : Tendsto (fun k => δ (v k) * (R k) ^ (2 * m + 3))
      atTop (𝓝 (0 : ℝ)) :=
    h3Path_scalar_summable_higherCubicCharge_forces_widthCompression244
      R (fun k => δ (v k)) m hSum
  have hAlt := h3Path_scalar_higherBudget_exactPDE_threeScale244
    v δ (fun n => (T - τ n) / 2)
    (h3PathCubicAnnulusActualGap244 hH3 τ N)
    (h3PathCubicAnnulusActualLinearRate244 N K C)
    (h3PathCubicAnnulusActualQuadraticRate244 N C)
    m hv hExact (by simpa only [R] using hCompress) hGap hΛ hΞ ε hε
  simpa only using hAlt

end
end PrimeTensor.FirstMonomialTriad
