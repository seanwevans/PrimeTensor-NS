import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.RadialMoments.SharpFourthEnergy
import Mathlib.Tactic

/-!
# Arbitrary higher radial order: sharp critical physical H³ energy cost

For every fixed m : ℕ, the same exact canonical PDE windows and a real
interval-integrable upper envelope of the physical q^(4+m) top moment
force weighted clock compression. Under an eventually bounded attained
source, a critical eighth-power outer cutoff, a noncompressed weighted
terminal time and a small tolerance, the linear arm is unavoidable.

  R^(16*m+3) ≤ (512 ε²)^4 (2304 E₃ S²+1)^4 D^5.

The exponent is exact for this fourth-power elimination:
  4*(4*m+12) - 45 = 16*m+3.
No source, outer-cutoff, noncompression, or higher-moment budget bound
is derived from the H³ energy class here. The premises stay explicit.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- At any natural extra radial order m, the fourth power of the linear
physical PDE energy branch leaves precisely R^(16*m+3) after the critical
outer cutoff contributes R^45. No fractional exponents are introduced. -/
theorem h3Path_higherBudget_anyMoment_linear_forces_sharpEnergyFourth244
    (R Q E S D ε : ℝ) (m : ℕ)
    (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hE : 0 ≤ E) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hCap : (Q + 1) ^ 8 ≤ D * R ^ 9)
    (hLinear : (((R ^ 2) ^ m) * R ^ 6) ^ 2 ≤
      512 * ε ^ 2 * (2304 * E * S ^ 2 * (Q + 1) ^ 10 + 1)) :
    R ^ (16 * m + 3) ≤ (512 * ε ^ 2) ^ 4 *
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
  have hInnerPower : (R ^ 2) ^ m * R ^ 6 = R ^ (2 * m + 6) := by
    rw [pow_add, pow_mul]
  have hBaseSquare : (((R ^ 2) ^ m) * R ^ 6) ^ 2 =
      R ^ (4 * m + 12) := by
    rw [hInnerPower, ← pow_mul]
    congr 1
    omega
  have hExponent : (16 * m + 3) + 45 = (4 * m + 12) * 4 := by
    omega
  have hFourthMonomial : R ^ (16 * m + 3) * R ^ 45 =
      (R ^ (4 * m + 12)) ^ 4 := by
    calc
      R ^ (16 * m + 3) * R ^ 45 =
          R ^ ((16 * m + 3) + 45) := (pow_add R _ _).symm
      _ = R ^ ((4 * m + 12) * 4) :=
        congrArg (fun n : ℕ => R ^ n) hExponent
      _ = (R ^ (4 * m + 12)) ^ 4 := by rw [pow_mul]
  have hBasic : R ^ (4 * m + 12) ≤
      (512 * ε ^ 2 * (2304 * E * S ^ 2 + 1)) * (Q + 1) ^ 10 := by
    calc
      R ^ (4 * m + 12) = (((R ^ 2) ^ m) * R ^ 6) ^ 2 := hBaseSquare.symm
      _ ≤ 512 * ε ^ 2 *
        (2304 * E * S ^ 2 * (Q + 1) ^ 10 + 1) := hLinear
      _ ≤ 512 * ε ^ 2 *
        ((2304 * E * S ^ 2 + 1) * (Q + 1) ^ 10) :=
        mul_le_mul_of_nonneg_left hWindow (by positivity)
      _ = (512 * ε ^ 2 * (2304 * E * S ^ 2 + 1)) *
        (Q + 1) ^ 10 := by ring
  have hPower : (R ^ (4 * m + 12)) ^ 4 ≤
      ((512 * ε ^ 2 * (2304 * E * S ^ 2 + 1)) *
        (Q + 1) ^ 10) ^ 4 :=
    pow_le_pow_left₀ (pow_nonneg hRpos.le (4 * m + 12)) hBasic 4
  have hOuter := h3Path_higherBudget_criticalEighth_forces_outerTenthFourth244
    R Q D hR hRQ hCap
  have hScaled :
      (512 * ε ^ 2 * (2304 * E * S ^ 2 + 1)) ^ 4 *
        ((Q + 1) ^ 10) ^ 4 ≤
      (512 * ε ^ 2 * (2304 * E * S ^ 2 + 1)) ^ 4 *
        (D ^ 5 * R ^ 45) :=
    mul_le_mul_of_nonneg_left hOuter (by positivity)
  have hCross : R ^ (16 * m + 3) * R ^ 45 ≤
      ((512 * ε ^ 2) ^ 4 *
        (2304 * E * S ^ 2 + 1) ^ 4 * D ^ 5) * R ^ 45 := by
    calc
      R ^ (16 * m + 3) * R ^ 45 = (R ^ (4 * m + 12)) ^ 4 := hFourthMonomial
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
      (2304 * E * S ^ 2 + 1) ^ 4 * D ^ 5 < R ^ (16 * m + 3) :=
    lt_of_not_ge hNot
  have hStrict := mul_lt_mul_of_pos_right hReverse hR45
  exact (not_lt_of_ge hCross) hStrict

/-- The same critical outer cap and a small epsilon exclude the quadratic
rate arm at EVERY m, since the radial weight (R²)^m ≥ 1 for R≥1. -/
theorem h3Path_higherBudget_anyMoment_outerCap_excludesQuadratic244
    (R Q S D ε : ℝ) (m : ℕ)
    (hR : 1 ≤ R) (hRQ : R ≤ Q) (hS : 0 ≤ S)
    (hCap : (Q + 1) ^ 8 ≤ D * R ^ 9)
    (hSmall : 16 * ε ^ 2 * (36 * S ^ 2 * (D + 256) + 1) < 1) :
    ¬ (((R ^ 2) ^ m) ^ 2 * R ^ 9 ≤
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
  have hSq : 1 ≤ (((R ^ 2) ^ m) ^ 2) := by
    have hRtwo : 1 ≤ R ^ 2 := by
      simpa only [one_pow] using
        (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hR 2)
    have hM : 1 ≤ (R ^ 2) ^ m := by
      simpa only [one_pow] using
        (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hRtwo m)
    simpa only [one_pow] using
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hM 2)
  have hFloor : R ^ 9 ≤
      16 * ε ^ 2 * (36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1) := by
    calc
      R ^ 9 = 1 * R ^ 9 := by ring
      _ ≤ (((R ^ 2) ^ m) ^ 2) * R ^ 9 :=
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

/-- With source and geometric branches excluded, only the physical energy
arm remains, now with exponent 16*m+3 for arbitrary m. -/
theorem h3Path_higherBudget_anyMoment_criticalBranches_force_sharpEnergyFourth244
    (R Q E S D G ε η : ℝ) (m : ℕ)
    (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hE : 0 ≤ E) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hNoncompress : ε < η) (hGeometry : η ≤ G)
    (hCap : (Q + 1) ^ 8 ≤ D * R ^ 9)
    (hSmall : 16 * ε ^ 2 * (36 * S ^ 2 * (D + 256) + 1) < 1)
    (hAlt : G ≤ ε ∨
      (((R ^ 2) ^ m) * R ^ 6) ^ 2 ≤
        512 * ε ^ 2 * (2304 * E * S ^ 2 * (Q + 1) ^ 10 + 1) ∨
      (((R ^ 2) ^ m) ^ 2) * R ^ 9 ≤
        16 * ε ^ 2 * (36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1)) :
    R ^ (16 * m + 3) ≤ (512 * ε ^ 2) ^ 4 *
      (2304 * E * S ^ 2 + 1) ^ 4 * D ^ 5 := by
  rcases hAlt with hTime | hLinear | hQuadratic
  · exact False.elim (by linarith only [hNoncompress, hGeometry, hTime])
  · exact h3Path_higherBudget_anyMoment_linear_forces_sharpEnergyFourth244
      R Q E S D ε m hR hRQ hE hS hε hCap hLinear
  · exact False.elim
      ((h3Path_higherBudget_anyMoment_outerCap_excludesQuadratic244
        R Q S D ε m hR hRQ hS hCap hSmall) hQuadratic)

/-- The SAME physical first-crossing canonical PDE anchors yield the
sharp fourth-power cost at every radial order m having an additional
integrable real majorant of the physical q^(4+m) top moment. All source,
cutoff, time and tolerance hypotheses remain explicit. -/
theorem h3Path_noL2Trace_exactAnchor_anyHigherBudget_criticalOuter_sharpEnergyFourth244
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
          ∀ᶠ k : ℕ in atTop,
            ((v k : ℝ) + 1) ^ (16 * m + 3) ≤
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
  intro m F hF hFInt hUpper S D η ε hS _hD _hη hε hεη hSmall hCeil hCap hGeom
  have hAlt := hFour m F hF hFInt hUpper S hS ε hε
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
  · have hGeom' : η ≤ R ^ (2 * m + 3) * ((T - τ (v k)) / 4) := by
      simpa only [R] using hkG
    have hTime' : R ^ (2 * m + 3) * ((T - τ (v k)) / 4) ≤ ε := by
      convert hTime using 1 <;> ring
    exact False.elim (by linarith only [hTime', hGeom', hεη])
  · have hRate : (((R ^ 2) ^ m) * R ^ 6) ^ 2 ≤
        512 * ε ^ 2 *
          (2304 * velocityH3EnergyAt u (τ (v k)) * S ^ 2 * (Q + 1) ^ 10 + 1) := by
      convert hLinear using 1 <;> ring
    exact h3Path_higherBudget_anyMoment_linear_forces_sharpEnergyFourth244
      R Q (velocityH3EnergyAt u (τ (v k))) S D ε m
      hR hRQ hE hS hε.le hCapped hRate
  · have hRate : (((R ^ 2) ^ m) ^ 2) * R ^ 9 ≤
        16 * ε ^ 2 *
          (36 * S ^ 2 * ((Q + 1) ^ 8 + (R + 1) ^ 8) + 1) := by
      convert hQuadratic using 1 <;> ring
    exact False.elim
      ((h3Path_higherBudget_anyMoment_outerCap_excludesQuadratic244
        R Q S D ε m hR hRQ hS hCapped hSmall) hRate)


end
end PrimeTensor.FirstMonomialTriad
