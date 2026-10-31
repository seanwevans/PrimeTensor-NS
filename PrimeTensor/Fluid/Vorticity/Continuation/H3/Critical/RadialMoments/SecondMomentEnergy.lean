import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.AnnularGeometry.EnergyOuter
import Mathlib.Tactic

/-!
# Critical outer cutoff and a q^6 spacetime budget force an H^3 energy cost

The second higher radial weight (m=2) produces a linear coefficient cost
R^20. The critical outer cutoff bound (Q+1)^8 <= D R^9 implies the
cruder (but root-free) (Q+1)^10 <= D^2 R^18. Thus the surviving
linear-rate branch forces an explicit quadratic inner-radius burden on
physical H^3 energy. This does not postulate higher-moment integrability,
source boundedness, a noncompressed terminal clock, or a cutoff cap:
all four are visible as conditional hypotheses in the final theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A critical eighth-power cutoff cap controls its tenth-power cost by
D^2 R^18, without fractional powers. -/
theorem h3Path_higherBudget_criticalEighth_forces_outerTenth244
    (R Q D : ℝ) (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hCap : (Q + 1) ^ 8 ≤ D * R ^ 9) :
    (Q + 1) ^ 10 ≤ D ^ 2 * R ^ 18 := by
  have hQOne : 1 ≤ Q + 1 := by linarith only [hR, hRQ]
  have hQSix : 1 ≤ (Q + 1) ^ 6 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hQOne 6)
  calc
    (Q + 1) ^ 10 = (Q + 1) ^ 10 * 1 := by ring
    _ ≤ (Q + 1) ^ 10 * (Q + 1) ^ 6 :=
      mul_le_mul_of_nonneg_left hQSix (by positivity)
    _ = ((Q + 1) ^ 8) ^ 2 := by ring
    _ ≤ (D * R ^ 9) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hCap 2
    _ = D ^ 2 * R ^ 18 := by ring

/-- The second higher radial (q^6) linear branch has R^20 on its left.
Under a critical cutoff cap its energy term carries at most R^18,
leaving a genuine R^2 H^3 energy burden. -/
theorem h3Path_higherBudget_secondMoment_linear_forces_energyQuadratic244
    (R Q E S D ε : ℝ)
    (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hE : 0 ≤ E) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hCap : (Q + 1) ^ 8 ≤ D * R ^ 9)
    (hLinear : (((R ^ 2) ^ 2) * R ^ 6) ^ 2 ≤
      512 * ε ^ 2 * (2304 * E * S ^ 2 * (Q + 1) ^ 10 + 1)) :
    R ^ 2 ≤ 512 * ε ^ 2 * (2304 * E * S ^ 2 * D ^ 2 + 1) := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  have hR18 : 0 < R ^ 18 := pow_pos hRpos _
  have hR18One : 1 ≤ R ^ 18 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hR 18)
  have hQ10 := h3Path_higherBudget_criticalEighth_forces_outerTenth244
    R Q D hR hRQ hCap
  have hScaled : 2304 * E * S ^ 2 * (Q + 1) ^ 10 ≤
      2304 * E * S ^ 2 * (D ^ 2 * R ^ 18) :=
    mul_le_mul_of_nonneg_left hQ10 (by positivity)
  have hAdd : 2304 * E * S ^ 2 * (Q + 1) ^ 10 + 1 ≤
      2304 * E * S ^ 2 * (D ^ 2 * R ^ 18) + R ^ 18 :=
    add_le_add hScaled hR18One
  have hBound : 2304 * E * S ^ 2 * (Q + 1) ^ 10 + 1 ≤
      (2304 * E * S ^ 2 * D ^ 2 + 1) * R ^ 18 := by
    calc
      _ ≤ 2304 * E * S ^ 2 * (D ^ 2 * R ^ 18) + R ^ 18 := hAdd
      _ = (2304 * E * S ^ 2 * D ^ 2 + 1) * R ^ 18 := by ring
  have hMul := mul_le_mul_of_nonneg_left hBound
    (show 0 ≤ 512 * ε ^ 2 by positivity)
  have hCross : R ^ 2 * R ^ 18 ≤
      (512 * ε ^ 2 * (2304 * E * S ^ 2 * D ^ 2 + 1)) * R ^ 18 := by
    calc
      R ^ 2 * R ^ 18 = (((R ^ 2) ^ 2) * R ^ 6) ^ 2 := by ring
      _ ≤ 512 * ε ^ 2 * (2304 * E * S ^ 2 * (Q + 1) ^ 10 + 1) := hLinear
      _ ≤ 512 * ε ^ 2 * ((2304 * E * S ^ 2 * D ^ 2 + 1) * R ^ 18) := hMul
      _ = (512 * ε ^ 2 * (2304 * E * S ^ 2 * D ^ 2 + 1)) * R ^ 18 := by ring
  by_contra hNot
  have hReverse : 512 * ε ^ 2 * (2304 * E * S ^ 2 * D ^ 2 + 1) < R ^ 2 :=
    lt_of_not_ge hNot
  have hStrict := mul_lt_mul_of_pos_right hReverse hR18
  exact (not_lt_of_ge hCross) hStrict

/-- With bounded source and an eighth-power outer cutoff, the quadratic
PDE rate cannot pay for the q^6 frequency floor at a sufficiently small
clock tolerance. -/
theorem h3Path_higherBudget_secondMoment_outerCap_excludesQuadratic244
    (R Q S D ε : ℝ)
    (hR : 1 ≤ R) (hRQ : R ≤ Q) (hS : 0 ≤ S)
    (hCap : (Q + 1) ^ 8 ≤ D * R ^ 9)
    (hSmall : 16 * ε ^ 2 * (36 * S ^ 2 * (D + 256) + 1) < 1) :
    ¬ (((R ^ 2) ^ 2) ^ 2 * R ^ 9 ≤
      16 * ε ^ 2 *
        (36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1)) := by
  intro hQuad
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  have hR9 : 0 < R ^ 9 := pow_pos hRpos _
  have hR9One : 1 ≤ R ^ 9 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hR 9)
  have hRplus : R + 1 ≤ 2 * R := by linarith only [hR]
  have hR8le9 : R ^ 8 ≤ R ^ 9 := by
    calc
      R ^ 8 = R ^ 8 * 1 := by ring
      _ ≤ R ^ 8 * R := mul_le_mul_of_nonneg_left hR (by positivity)
      _ = R ^ 9 := by ring
  have hPlus : (R + 1) ^ 8 ≤ 256 * R ^ 9 := by
    calc
      (R + 1) ^ 8 ≤ (2 * R) ^ 8 :=
        pow_le_pow_left₀ (by positivity) hRplus 8
      _ = 256 * R ^ 8 := by ring
      _ ≤ 256 * R ^ 9 := mul_le_mul_of_nonneg_left hR8le9 (by norm_num)
  have hSum : (Q + 1) ^ 8 + (R + 1) ^ 8 ≤ (D + 256) * R ^ 9 := by
    linarith only [hCap, hPlus]
  have hSq : 1 ≤ (((R ^ 2) ^ 2) ^ 2) := by
    calc
      (1 : ℝ) = 1 ^ 8 := by ring
      _ ≤ R ^ 8 :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hR 8
      _ = (((R ^ 2) ^ 2) ^ 2) := by ring
  have hFloor : R ^ 9 ≤
      16 * ε ^ 2 * (36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1) := by
    calc
      R ^ 9 = 1 * R ^ 9 := by ring
      _ ≤ (((R ^ 2) ^ 2) ^ 2) * R ^ 9 :=
        mul_le_mul_of_nonneg_right hSq (pow_nonneg hRpos.le _)
      _ ≤ 16 * ε ^ 2 * (36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1) := hQuad
  have hScaled := mul_le_mul_of_nonneg_left hSum
    (show 0 ≤ 36 * S ^ 2 by positivity)
  let W : ℝ := 36 * S ^ 2 * (D + 256) + 1
  have hAdd : 36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1 ≤
      36 * S ^ 2 * ((D + 256) * R ^ 9) + R ^ 9 :=
    add_le_add hScaled hR9One
  have hW : 36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1 ≤
      W * R ^ 9 := by
    calc
      _ ≤ 36 * S ^ 2 * ((D + 256) * R ^ 9) + R ^ 9 := hAdd
      _ = W * R ^ 9 := by dsimp only [W]; ring
  have hBound := mul_le_mul_of_nonneg_left hW
    (show 0 ≤ 16 * ε ^ 2 by positivity)
  have hCross : R ^ 9 ≤ (16 * ε ^ 2 * W) * R ^ 9 := by
    calc
      _ ≤ 16 * ε ^ 2 * (36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1) := hFloor
      _ ≤ 16 * ε ^ 2 * (W * R ^ 9) := hBound
      _ = (16 * ε ^ 2 * W) * R ^ 9 := by ring
  have hStrict : (16 * ε ^ 2 * W) * R ^ 9 < (1 : ℝ) * R ^ 9 := by
    apply mul_lt_mul_of_pos_right
    simpa only [W] using hSmall
    exact hR9
  exact (not_lt_of_ge hCross) (by simpa only [one_mul] using hStrict)

/-- A q^6 spacetime envelope plus three explicit noncompression/ceiling
conditions leaves only the physical energy branch, with a quadratic
inner-radius burden. -/
theorem h3Path_higherBudget_secondMoment_criticalBranches_force_energy244
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
    R ^ 2 ≤ 512 * ε ^ 2 * (2304 * E * S ^ 2 * D ^ 2 + 1) := by
  rcases hAlt with hTime | hLinear | hQuadratic
  · exact False.elim (by linarith only [hNoncompress, hGeometry, hTime])
  · exact h3Path_higherBudget_secondMoment_linear_forces_energyQuadratic244
      R Q E S D ε hR hRQ hE hS hε hCap hLinear
  · exact False.elim
      ((h3Path_higherBudget_secondMoment_outerCap_excludesQuadratic244
        R Q S D ε hR hRQ hS hCap hSmall) hQuadratic)

/-- The same original cofinal physical PDE anchors: if the actual q^6
extended top moment has an integrable upper envelope and the attained
source, critical outer cutoff, and weighted terminal lag are controlled,
then the original H^3 energy pays a growing quadratic inner-radius cost.
Every additional premise remains visible, not inferred from finite H^3
dissipation. No terminal regularity or contradiction is asserted. -/
theorem h3Path_noL2Trace_exactAnchor_secondHigherBudget_criticalOuter_energyCost244
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
            ((v k : ℝ) + 1) ^ 2 ≤
              512 * ε ^ 2 *
                (2304 * velocityH3EnergyAt u (τ (v k)) * S ^ 2 * D ^ 2 + 1)) := by
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
    exact h3Path_higherBudget_secondMoment_linear_forces_energyQuadratic244
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
