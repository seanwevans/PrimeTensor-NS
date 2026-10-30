import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudgetSecondMomentCriticalEnergy244
import Mathlib.Tactic

/-!
# Sharp fourth-power critical energy burden from the same q⁶ canonical windows

The previous q⁶ energy cost used the intentionally weak
  (Q+1)^10 ≤ D² R^18.
The exact eighth-power cap instead implies the root-free
  ((Q+1)^10)^4 ≤ D^5 R^45.
Raising the physical linear alternative to the fourth power and
cancelling the positive R^45 leaves R^35 charged to the fourth power
of physical H³ energy/source. The same original conditional hypotheses
and actual first-crossing cofinal witness remain unchanged.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Sharp root-free 8-to-10 transfer: the tenth-power cutoff cost to
its fourth power is bounded by the fifth power of the critical eighth
cutoff budget. -/
theorem h3Path_higherBudget_criticalEighth_forces_outerTenthFourth244
    (R Q D : ℝ) (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hCap : (Q + 1) ^ 8 ≤ D * R ^ 9) :
    ((Q + 1) ^ 10) ^ 4 ≤ D ^ 5 * R ^ 45 := by
  have hQpos : 0 ≤ Q + 1 := by linarith only [hR, hRQ]
  have hPow : ((Q + 1) ^ 8) ^ 5 ≤ (D * R ^ 9) ^ 5 :=
    pow_le_pow_left₀ (pow_nonneg hQpos 8) hCap 5
  calc
    ((Q + 1) ^ 10) ^ 4 = ((Q + 1) ^ 8) ^ 5 := by ring
    _ ≤ (D * R ^ 9) ^ 5 := hPow
    _ = D ^ 5 * R ^ 45 := by ring

/-- The q⁶ physical linear rate at a critical eighth-power outer cutoff
charges R^35 to the fourth power of actual H³ energy. This sharpens
R² ≤ 512 ε² (2304 E S² D² + 1) without additional assumptions. -/
theorem h3Path_higherBudget_secondMoment_linear_forces_sharpEnergyFourth244
    (R Q E S D ε : ℝ)
    (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hE : 0 ≤ E) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hCap : (Q + 1) ^ 8 ≤ D * R ^ 9)
    (hLinear : (((R ^ 2) ^ 2) * R ^ 6) ^ 2 ≤
      512 * ε ^ 2 * (2304 * E * S ^ 2 * (Q + 1) ^ 10 + 1)) :
    R ^ 35 ≤ (512 * ε ^ 2) ^ 4 *
      (2304 * E * S ^ 2 + 1) ^ 4 * D ^ 5 := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  have hR45 : 0 < R ^ 45 := pow_pos hRpos _
  have hQone : 1 ≤ Q + 1 := by linarith only [hR, hRQ]
  have hQten : 1 ≤ (Q + 1) ^ 10 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hQone 10)
  have hWindow : 2304 * E * S ^ 2 * (Q + 1) ^ 10 + 1 ≤
      (2304 * E * S ^ 2 + 1) * (Q + 1) ^ 10 := by
    calc
      _ ≤ 2304 * E * S ^ 2 * (Q + 1) ^ 10 + (Q + 1) ^ 10 := by
        linarith only [hQten]
      _ = (2304 * E * S ^ 2 + 1) * (Q + 1) ^ 10 := by ring
  have hBasic : R ^ 20 ≤
      (512 * ε ^ 2 * (2304 * E * S ^ 2 + 1)) * (Q + 1) ^ 10 := by
    calc
      R ^ 20 = (((R ^ 2) ^ 2) * R ^ 6) ^ 2 := by ring
      _ ≤ 512 * ε ^ 2 *
        (2304 * E * S ^ 2 * (Q + 1) ^ 10 + 1) := hLinear
      _ ≤ 512 * ε ^ 2 *
        ((2304 * E * S ^ 2 + 1) * (Q + 1) ^ 10) :=
        mul_le_mul_of_nonneg_left hWindow (by positivity)
      _ = (512 * ε ^ 2 * (2304 * E * S ^ 2 + 1)) *
        (Q + 1) ^ 10 := by ring
  have hPower : (R ^ 20) ^ 4 ≤
      ((512 * ε ^ 2 * (2304 * E * S ^ 2 + 1)) *
        (Q + 1) ^ 10) ^ 4 :=
    pow_le_pow_left₀ (pow_nonneg hRpos.le 20) hBasic 4
  have hOuter := h3Path_higherBudget_criticalEighth_forces_outerTenthFourth244
    R Q D hR hRQ hCap
  have hScaled :
      (512 * ε ^ 2 * (2304 * E * S ^ 2 + 1)) ^ 4 *
        ((Q + 1) ^ 10) ^ 4 ≤
      (512 * ε ^ 2 * (2304 * E * S ^ 2 + 1)) ^ 4 *
        (D ^ 5 * R ^ 45) :=
    mul_le_mul_of_nonneg_left hOuter (by positivity)
  have hCross : R ^ 35 * R ^ 45 ≤
      ((512 * ε ^ 2) ^ 4 *
        (2304 * E * S ^ 2 + 1) ^ 4 * D ^ 5) * R ^ 45 := by
    calc
      R ^ 35 * R ^ 45 = (R ^ 20) ^ 4 := by ring
      _ ≤ ((512 * ε ^ 2 * (2304 * E * S ^ 2 + 1)) *
          (Q + 1) ^ 10) ^ 4 := hPower
      _ = (512 * ε ^ 2 * (2304 * E * S ^ 2 + 1)) ^ 4 *
          ((Q + 1) ^ 10) ^ 4 := by ring
      _ ≤ (512 * ε ^ 2 * (2304 * E * S ^ 2 + 1)) ^ 4 *
          (D ^ 5 * R ^ 45) := hScaled
      _ = ((512 * ε ^ 2) ^ 4 *
          (2304 * E * S ^ 2 + 1) ^ 4 * D ^ 5) * R ^ 45 := by ring
  by_contra hNot
  have hReverse : (512 * ε ^ 2) ^ 4 *
      (2304 * E * S ^ 2 + 1) ^ 4 * D ^ 5 < R ^ 35 :=
    lt_of_not_ge hNot
  have hStrict := mul_lt_mul_of_pos_right hReverse hR45
  exact (not_lt_of_ge hCross) hStrict

/-- The old terminal-clock/source/quadratic exclusions are unchanged;
the surviving linear arm now pays the sharper fourth-power energy bill. -/
theorem h3Path_higherBudget_secondMoment_criticalBranches_force_sharpEnergyFourth244
    (R Q E S D G ε η : ℝ)
    (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hE : 0 ≤ E) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hNoncompress : ε < η) (hGeometry : η ≤ G)
    (hCap : (Q + 1) ^ 8 ≤ D * R ^ 9)
    (hSmall : 16 * ε ^ 2 * (36 * S ^ 2 * (D + 256) + 1) < 1)
    (hAlt : G ≤ ε ∨
      (((R ^ 2) ^ 2) * R ^ 6) ^ 2 ≤
        512 * ε ^ 2 * (2304 * E * S ^ 2 * (Q + 1) ^ 10 + 1) ∨
      (((R ^ 2) ^ 2) ^ 2) * R ^ 9 ≤
        16 * ε ^ 2 * (36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1)) :
    R ^ 35 ≤ (512 * ε ^ 2) ^ 4 *
      (2304 * E * S ^ 2 + 1) ^ 4 * D ^ 5 := by
  rcases hAlt with hTime | hLinear | hQuadratic
  · exact False.elim (by linarith only [hNoncompress, hGeometry, hTime])
  · exact h3Path_higherBudget_secondMoment_linear_forces_sharpEnergyFourth244
      R Q E S D ε hR hRQ hE hS hε hCap hLinear
  · exact False.elim
      ((h3Path_higherBudget_secondMoment_outerCap_excludesQuadratic244
        R Q S D ε hR hRQ hS hCap hSmall) hQuadratic)

/-- Same actual cofinal witnesses and full conditional assumptions of the
committed q⁶ critical-energy theorem, with the sharp exponent 35. -/
theorem h3Path_noL2Trace_exactAnchor_secondHigherBudget_criticalOuter_sharpEnergyFourth244
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
      (∀ F : ℝ → ℝ,
        (∀ s : ℝ, 0 ≤ F s) →
        IntervalIntegrable F volume a T →
        (∀ s : ℝ, ∀ hs : s ∈ Set.Ioo a T,
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass 2 s hs ≤ ENNReal.ofReal (F s)) →
        ∀ S D η ε : ℝ,
          0 ≤ S → 0 ≤ D → 0 < η → 0 < ε → ε < η →
          16 * ε ^ 2 * (36 * S ^ 2 * (D + 256) + 1) < 1 →
          (∀ᶠ k : ℕ in atTop, C (v k) ≤ S) →
          (∀ᶠ k : ℕ in atTop,
            ((N (v k) : ℝ) + 2) ^ 8 ≤ D * ((v k : ℝ) + 1) ^ 9) →
          (∀ᶠ k : ℕ in atTop,
            η ≤ ((v k : ℝ) + 1) ^ 7 * ((T - τ (v k)) / 4)) →
          ∀ᶠ k : ℕ in atTop,
            ((v k : ℝ) + 1) ^ 35 ≤
              (512 * ε ^ 2) ^ 4 *
                (2304 * velocityH3EnergyAt u (τ (v k)) * S ^ 2 + 1) ^ 4 * D ^ 5) := by
  obtain ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
      hSeparate, hAnchor, hFour⟩ :=
    h3Path_noL2Trace_exactAnchor_higherBudget_sourceEnergyOuterGeometry244
      hH3 hClass hMass hNoTrace hDInt
  have hAnchor' (k : ℕ) :
      v k ≤ N (v k) ∧
      C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
        (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) :=
    ⟨(hAnchor k).1, (hAnchor k).2.2.1⟩
  refine ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
    hSeparate, hAnchor', ?_⟩
  intro F hF hFInt hUpper S D η ε hS _hD _hη hε hεη hSmall hCeil hCap hGeom
  have hAlt := hFour 2 F hF hFInt hUpper S hS ε hε
  filter_upwards [hAlt, hCeil, hCap, hGeom] with k hk hkC hkQ hkG
  let R : ℝ := (v k : ℝ) + 1
  let Q : ℝ := (N (v k) : ℝ) + 1
  have hR : 1 ≤ R := by
    dsimp only [R]
    have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hn]
  have hRQ : R ≤ Q := by
    have hn : (v k : ℝ) ≤ (N (v k) : ℝ) := by
      exact_mod_cast (hAnchor' k).1
    dsimp only [R, Q]
    linarith only [hn]
  have hE : 0 ≤ velocityH3EnergyAt u (τ (v k)) :=
    (sq_nonneg (K (v k))).trans (hAnchor k).2.2.2.2
  have hCapped : (Q + 1) ^ 8 ≤ D * R ^ 9 := by
    change (((N (v k) : ℝ) + 1) + 1) ^ 8 ≤
      D * (((v k : ℝ) + 1) ^ 9)
    rw [show ((N (v k) : ℝ) + 1) + 1 =
      (N (v k) : ℝ) + 2 by ring]
    exact hkQ
  rcases hk with hSource | hTime | hLinear | hQuadratic
  · obtain ⟨s, hs, hsBig⟩ := hSource
    have ht := hτ (v k)
    have ht0 : 0 < τ (v k) :=
      lt_trans hClass.terminal_start.1 ht.1
    have hMid : τ (v k) < τ (v k) + (T - τ (v k)) / 2 := by
      linarith only [ht.2]
    have hb : τ (v k) + (T - τ (v k)) / 2 < T := by
      linarith only [ht.2]
    have hSourceLe := h3Path_actualSourceWindowEnvelope_pointwise_le244
      hH3 ht0 hMid hb s hs
    rw [←(hAnchor' k).2] at hSourceLe
    exact False.elim ((not_lt_of_ge (hSourceLe.trans hkC)) hsBig)
  · have hGeom' : η ≤ R ^ 7 * ((T - τ (v k)) / 4) := by
      simpa only [R] using hkG
    have hTime' : R ^ 7 * ((T - τ (v k)) / 4) ≤ ε := by
      convert hTime using 1 <;> ring
    exact False.elim (by linarith only [hTime', hGeom', hεη])
  · have hRate : (((R ^ 2) ^ 2) * R ^ 6) ^ 2 ≤
        512 * ε ^ 2 *
          (2304 * velocityH3EnergyAt u (τ (v k)) * S ^ 2 * (Q + 1) ^ 10 + 1) := by
      convert hLinear using 1 <;> ring
    exact h3Path_higherBudget_secondMoment_linear_forces_sharpEnergyFourth244
      R Q (velocityH3EnergyAt u (τ (v k))) S D ε
      hR hRQ hE hS hε.le hCapped hRate
  · have hRate : (((R ^ 2) ^ 2) ^ 2) * R ^ 9 ≤
        16 * ε ^ 2 *
          (36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1) := by
      convert hQuadratic using 1 <;> ring
    exact False.elim
      ((h3Path_higherBudget_secondMoment_outerCap_excludesQuadratic244
        R Q S D ε hR hRQ hS hCapped hSmall) hRate)


end
end PrimeTensor.FirstMonomialTriad
