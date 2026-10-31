import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudgetPhysicalSourceGain244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEQuadraticEighthCutoff244
import Mathlib.Tactic

/-!
# Higher radial budgets: actual source, physical H³ energy and outer radius

A source-gain alternative is not yet a physical frequency obstruction until
its linear and quadratic gains are replaced by the existing physical bounds.
The linear clock is charged to the anchor H³ energy and the source square;
the quadratic clock is charged to eighth powers of the actual cutoffs.
The original first-crossing canonical witness is retained, including R ≤ Q.
The higher-order spacetime envelope remains an explicit extra assumption.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Replace the exact source-linear frequency gain with the previously
proved physical H³ energy and a tenth-power outer radius. -/
theorem h3Path_higherBudget_linearGain_forces_energyOuterTenth244
    (R Q K S E A ε : ℝ)
    (hR : 0 ≤ R) (hRQ : R ≤ Q)
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hKE : K ^ 2 ≤ E)
    (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hRate : A ≤ 16 * ε *
      (S * h3PathFiniteAnnulusPDELinearGain244 R Q K + 1)) :
    A ^ 2 ≤ 512 * ε ^ 2 *
      (2304 * E * S ^ 2 * (Q + 1) ^ 10 + 1) := by
  have hPhysical : A ≤ 16 * ε *
      (h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K S + 1) := by
    rw [h3Path_higherBudget_linearRate_eq_sourceGain244]
    exact hRate
  exact h3Path_scalar_higherLinearRate_forces_energySourceSquare244
    R Q K S E A ε hR hRQ hK hS hKE hA hε hPhysical

/-- Replace the exact source-quadratic frequency gain with the proven
physical eighth-power radius bound, without an assumed outer cutoff cap. -/
theorem h3Path_higherBudget_quadraticGain_forces_outerEighth244
    (R Q S B ε : ℝ)
    (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hRate : B ≤ 16 * ε ^ 2 *
      (S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q + 1)) :
    B ≤ 16 * ε ^ 2 *
      (36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1) := by
  have hGain := h3Path_quadraticGain_le_eighthRadiusSum244 R Q hR hQ
  have hScaled : S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q ≤
      36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) := by
    have hMul := mul_le_mul_of_nonneg_left hGain (sq_nonneg S)
    calc
      S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q ≤
          S ^ 2 * (36 * ((Q + 1) ^ 8 + (R + 1) ^ 8)) := hMul
      _ = 36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) := by ring
  have hAdd : S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q + 1 ≤
      36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1 := by
    linarith only [hScaled]
  exact hRate.trans
    (mul_le_mul_of_nonneg_left hAdd (by positivity))

/-- The exact source/gain split can be expressed entirely in the original
projected-source peak, physical H³ energy, and outer cutoff geometry.
In particular neither an outer-width cap nor a source ceiling is inserted. -/
theorem h3Path_scalar_higherBudget_sourceEnergyOrOuterEighth244
    (R Q K C E S A B G ε : ℝ)
    (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hKE : K ^ 2 ≤ E) (hA : 0 ≤ A)
    (hAlt : G ≤ ε ∨
      A ≤ 16 * ε *
        (h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C + 1) ∨
      B ≤ 16 * ε ^ 2 *
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C + 1)) :
    S < C ∨ G ≤ ε ∨
      A ^ 2 ≤ 512 * ε ^ 2 *
        (2304 * E * S ^ 2 * (Q + 1) ^ 10 + 1) ∨
      B ≤ 16 * ε ^ 2 *
        (36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1) := by
  have hSplit := h3Path_scalar_higherBudget_sourceOrCutoffGain244
    R Q K C S A B G ε hK hC hS hε hAlt
  have hR0 : 0 ≤ R :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) hR
  rcases hSplit with hSource | hTime | hLinear | hQuadratic
  · exact Or.inl hSource
  · exact Or.inr (Or.inl hTime)
  · exact Or.inr (Or.inr (Or.inl
      (h3Path_higherBudget_linearGain_forces_energyOuterTenth244
        R Q K S E A ε hR0 hRQ hK hS hKE hA hε hLinear)))
  · exact Or.inr (Or.inr (Or.inr
      (h3Path_higherBudget_quadraticGain_forces_outerEighth244
        R Q S B ε hR0 (le_trans hR0 hRQ) hS hε hQuadratic)))

/-- On the original exact first-crossing physical PDE windows, any
integrable upper envelope of a fixed extended q^(4+m) top-order moment
forces an attained source peak, compressed terminal clock, H³ energy and
source growth at the tenth-power outer radius, or eighth-power outer
cutoff cost. The same witnesses satisfy v(k) ≤ N(v(k)), K² ≤ E₃, and
no extra source bound or frequency cap is assumed. -/
theorem h3Path_noL2Trace_exactAnchor_higherBudget_sourceEnergyOuterGeometry244
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
        K (v k) = ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        0 < δ (v k) ∧
        K (v k) ^ 2 ≤ velocityH3EnergyAt u (τ (v k))) ∧
      (∀ m : ℕ, ∀ F : ℝ → ℝ,
        (∀ s : ℝ, 0 ≤ F s) →
        IntervalIntegrable F volume a T →
        (∀ s : ℝ, ∀ hs : s ∈ Set.Ioo a T,
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass m s hs ≤ ENNReal.ofReal (F s)) →
        ∀ S : ℝ, 0 ≤ S →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
          (∃ s : ℝ,
            s ∈ Set.Icc (τ (v k))
              (τ (v k) + (T - τ (v k)) / 2) ∧
            S < ‖h3PathActualProjectedMomentumSource244 hH3 s‖) ∨
          (((v k : ℝ) + 1) ^ (2 * m + 3)) *
            (((T - τ (v k)) / 2) / 2) ≤ ε ∨
          (((((v k : ℝ) + 1) ^ 2) ^ m) *
            (((v k : ℝ) + 1) ^ 6)) ^ 2 ≤
              512 * ε ^ 2 *
                (2304 * velocityH3EnergyAt u (τ (v k)) * S ^ 2 *
                  (((N (v k) : ℝ) + 2) ^ 10) + 1) ∨
          (((((v k : ℝ) + 1) ^ 2) ^ m) ^ 2) *
            (((v k : ℝ) + 1) ^ 9) ≤
              16 * ε ^ 2 *
                (36 * S ^ 2 *
                  ((((N (v k) : ℝ) + 2) ^ 8) +
                    (((v k : ℝ) + 2) ^ 8)) + 1)) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, _hSummable, hAll, _hBarrier, _hPeaks⟩ :=
    h3Path_noL2Trace_finiteDissipation_exactAnchorCanonicalThreeScale244
      hH3 hClass hMass hNoTrace hDInt
  have hAnchor (k : ℕ) :
      v k ≤ N (v k) ∧
      K (v k) = ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∧
      C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
        (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
      0 < δ (v k) ∧
      K (v k) ^ 2 ≤ velocityH3EnergyAt u (τ (v k)) := by
    rcases hAll k with ⟨hK, hKE, _, hN, hC, _, hδ, _, _, _, _, _⟩
    exact ⟨hN, hK, hC, hδ, hKE⟩
  have hPeak (k : ℕ) :
      ∃ s : ℝ,
        s ∈ Set.Icc (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C (v k) := by
    rcases hAll k with ⟨_, _, _, _, _, hp, _, _, _, _, _, _⟩
    exact hp
  have hKnonneg (k : ℕ) : 0 ≤ K (v k) := by
    rw [(hAnchor k).2.1]
    exact norm_nonneg _
  have hCnonneg (k : ℕ) : 0 ≤ C (v k) := by
    obtain ⟨s, _hs, hEq⟩ := hPeak k
    rw [← hEq]
    exact norm_nonneg _
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
    change 0 ≤ h3PathFiniteAnnulusPDEVariationCoefficient244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (K (v k)) (C (v k))
    exact h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
      _ _ _ _ (hKnonneg k) (hCnonneg k)
  have hΞ (k : ℕ) :
      0 ≤ h3PathCubicAnnulusActualQuadraticRate244 N C (v k) := by
    unfold h3PathCubicAnnulusActualQuadraticRate244
    exact h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))
  refine ⟨τ, N, K, C, δ, v, hTime, hv, hCofinal,
    hSeparate, hAnchor, ?_⟩
  intro m F hF hFInt hUpper S hS ε hε
  let R : ℕ → ℝ := fun k => (v k : ℝ) + 1
  let A : ℕ → ℝ := fun k => ((R k) ^ 2) ^ m * ((R k) ^ 3 / 8)
  have hRnonneg (k : ℕ) : 0 ≤ R k := by
    dsimp only [R]
    positivity
  have hAnonneg (k : ℕ) : 0 ≤ A k := by
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
      (fun k => (hTime (v k)).1.le) (fun k => (hAnchor k).2.2.2.1.le)
      (fun k => (hEnd k).le)
      (fun k => (hSeparate k (k + 1) (Nat.lt_succ_self k)).le)
      hAnonneg hFloor
  have hCompress : Tendsto
      (fun k => δ (v k) * ((v k : ℝ) + 1) ^ (2 * m + 3))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [R] using
      (h3Path_scalar_summable_higherCubicCharge_forces_widthCompression244
        R (fun k => δ (v k)) m hSum)
  have hOld := h3Path_scalar_higherBudget_exactPDE_threeScale244
    v δ (fun n => (T - τ n) / 2)
    (h3PathCubicAnnulusActualGap244 hH3 τ N)
    (h3PathCubicAnnulusActualLinearRate244 N K C)
    (h3PathCubicAnnulusActualQuadraticRate244 N C)
    m hv hExact hCompress hGap hΛ hΞ ε hε
  filter_upwards [hOld] with k hk
  let Rk : ℝ := (v k : ℝ) + 1
  let Qk : ℝ := (N (v k) : ℝ) + 1
  have hRk : 1 ≤ Rk := by
    dsimp only [Rk]
    have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hn]
  have hRQk : Rk ≤ Qk := by
    have hCast : (v k : ℝ) ≤ (N (v k) : ℝ) := by
      exact_mod_cast (hAnchor k).1
    dsimp only [Rk, Qk]
    linarith only [hCast]
  have hAk : 0 ≤ (((Rk ^ 2) ^ m) * Rk ^ 6) := by
    positivity
  have hSplit := h3Path_scalar_higherBudget_sourceEnergyOrOuterEighth244
    Rk Qk (K (v k)) (C (v k))
    (velocityH3EnergyAt u (τ (v k))) S
    (((Rk ^ 2) ^ m) * Rk ^ 6)
    ((((Rk ^ 2) ^ m) ^ 2) * Rk ^ 9)
    (Rk ^ (2 * m + 3) * (((T - τ (v k)) / 2) / 2)) ε
    hRk hRQk (hKnonneg k) (hCnonneg k) hS hε.le
    (hAnchor k).2.2.2.2 hAk
    (by simpa only [Rk, Qk,
      h3PathCubicAnnulusActualLinearRate244,
      h3PathCubicAnnulusActualQuadraticRate244] using hk)
  rcases hSplit with hSource | hTime | hLinear | hQuadratic
  · left
    obtain ⟨s, hs, hEq⟩ := hPeak k
    exact ⟨s, hs, by rw [hEq]; exact hSource⟩
  · exact Or.inr (Or.inl (by simpa only [Rk] using hTime))
  · right; right; left
    convert hLinear using 1 <;> ring
  · right; right; right
    convert hQuadratic using 1 <;> ring

end
end PrimeTensor.FirstMonomialTriad
