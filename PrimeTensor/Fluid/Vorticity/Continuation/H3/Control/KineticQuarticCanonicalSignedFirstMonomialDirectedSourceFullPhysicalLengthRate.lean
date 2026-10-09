import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourcePhysicalLengthCorridor
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Characteristic.Length.Rate

/-!
# Quantitative full physical H³ length collapse from the top length rate

The previously proved top characteristic length bound, under nonextension,

  ell_top(t)^6 <= 3 K^2 (E0(b)+1) (T-t)^2,

holds on a strict left terminal interval. Independently, the fixed physical
length corridor gives ell_full(t)/ell_top(t) -> 1 on the ENTIRE terminal tail.
Thus, for every fixed epsilon>0, the exact same kinetic anchor provides

  ell_full(t)^6 <= (1+epsilon)^6 * 3 K^2 (E0(b)+1) (T-t)^2

eventually, without a new frequency or transport estimate. On the original
fixed directed-source witness T-1/(n+1)<tau(n)<T, this entails

  (n+1)^2 ell_full(tau(n))^6
    <= (1+epsilon)^6 * 3 K^2 (E0(b)+1)

eventually. The index, three critical clocks, and the exhaustive gradient
versus fixed ordered signed-monomial branches are retained. These are only
conditional necessary consequences of nonextension, not singularity existence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Positive top energy and dissipation give a strictly positive
characteristic top length, needed when multiplying a ratio corridor. -/
theorem h3PathCanonical_topPhysicalLength_pos_of_topBlocks_pos
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (hE3 : 0 < velocityH3Energy3At u t)
    (hD3 : 0 < velocityH3Dissipation3At u t) :
    0 < h3TopCharacteristicLengthAt u t := by
  unfold h3TopCharacteristicLengthAt h3TopCharacteristicFrequencyAt
  exact inv_pos.mpr (Real.sqrt_pos.2 (div_pos hD3 hE3))

/-- Relative length corridors give sixth-power comparison, with the
precise factor `(1+epsilon)^6` and no loss in the exponent. -/
theorem h3PathCanonical_fullLength_pow_six_le_scaled_top
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t epsilon : ℝ)
    (hE3 : 0 < velocityH3Energy3At u t)
    (hD3 : 0 < velocityH3Dissipation3At u t)
    (hRatio : h3PathCanonicalFullToTopPhysicalLengthRatioAt u t < 1 + epsilon) :
    h3PathCanonicalFullPhysicalLengthAt u t ^ 6 <=
      (1 + epsilon) ^ 6 * h3TopCharacteristicLengthAt u t ^ 6 := by
  have hTopLength : 0 < h3TopCharacteristicLengthAt u t :=
    h3PathCanonical_topPhysicalLength_pos_of_topBlocks_pos u t hE3 hD3
  have hFullNonneg : 0 <= h3PathCanonicalFullPhysicalLengthAt u t := by
    unfold h3PathCanonicalFullPhysicalLengthAt
      h3PathCanonicalFullPhysicalFrequencyAt
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hRatio' :
      h3PathCanonicalFullPhysicalLengthAt u t /
        h3TopCharacteristicLengthAt u t < 1 + epsilon := by
    exact hRatio
  have hLengthLe :
      h3PathCanonicalFullPhysicalLengthAt u t <=
        (1 + epsilon) * h3TopCharacteristicLengthAt u t :=
    le_of_lt ((div_lt_iff₀ hTopLength).mp hRatio')
  have hPow := pow_le_pow_left₀ hFullNonneg hLengthLe 6
  simpa only [mul_pow] using hPow

/-- For every relative tolerance, full physical H³ length collapse obeys
the SAME `(T-t)^2` sixth-power law as the top characteristic length, with
only the asymptotically sharp factor `(1+epsilon)^6`. -/
theorem h3PathCanonical_fullPhysicalLength_sixthPower_terminalRate_eventually
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      h3PathCanonicalFullPhysicalLengthAt u t ^ 6 <=
        (1 + epsilon) ^ 6 *
          (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
            (velocityH3Energy0At u b + 1)) * (T - t) ^ 2 := by
  let C : ℝ :=
    3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
      (velocityH3Energy0At u b + 1)
  obtain ⟨c, hc, hTopRate⟩ :=
    exists_terminalTail_characteristicLength_pow_six_le_terminalDistance_sq_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  have hTopBound : ∀ᶠ t : ℝ in 𝓝[<] T,
      h3TopCharacteristicLengthAt u t ^ 6 <= C * (T - t) ^ 2 := by
    filter_upwards [Ioo_mem_nhdsLT hc.2] with t ht
    simpa only [C, mul_assoc] using hTopRate t ht
  have hRatio : ∀ᶠ t : ℝ in 𝓝[<] T,
      h3PathCanonicalFullToTopPhysicalLengthRatioAt u t <
        1 + epsilon := by
    have hCorridor := h3PathCanonical_physicalLengthRatio_eventually_strictCorridor
      hH3 hNoExtension hClass hb hEpsilon
    filter_upwards [hCorridor] with t ht
    exact ht.2
  have hE3T : Tendsto (velocityH3Energy3At u) (𝓝[<] T) atTop :=
    velocityH3Energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hD3T : Tendsto (velocityH3Dissipation3At u) (𝓝[<] T) atTop :=
    velocityH3Dissipation3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hE3Pos : ∀ᶠ t : ℝ in 𝓝[<] T,
      0 < velocityH3Energy3At u t := by
    filter_upwards [(tendsto_atTop.1 hE3T) 1] with t ht
    linarith only [ht]
  have hD3Pos : ∀ᶠ t : ℝ in 𝓝[<] T,
      0 < velocityH3Dissipation3At u t := by
    filter_upwards [(tendsto_atTop.1 hD3T) 1] with t ht
    linarith only [ht]
  have hCoeff : 0 <= (1 + epsilon) ^ 6 := by
    have hOne : 0 <= 1 + epsilon := by linarith only [hEpsilon]
    positivity
  filter_upwards [hTopBound, hRatio, hE3Pos, hD3Pos]
    with t hTop hCorr hE3 hD3
  have hScale :=
    h3PathCanonical_fullLength_pow_six_le_scaled_top
      u t epsilon hE3 hD3 hCorr
  have hMultiply := mul_le_mul_of_nonneg_left hTop hCoeff
  calc
    h3PathCanonicalFullPhysicalLengthAt u t ^ 6 <=
        (1 + epsilon) ^ 6 * h3TopCharacteristicLengthAt u t ^ 6 := hScale
    _ <= (1 + epsilon) ^ 6 * (C * (T - t) ^ 2) := hMultiply
    _ = (1 + epsilon) ^ 6 *
        (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
          (velocityH3Energy0At u b + 1)) * (T - t) ^ 2 := by
      dsimp only [C]
      ring

/-- Ordinary physical late-interval version of the full H³ length rate. -/
theorem h3PathCanonical_exists_terminalTail_fullPhysicalLength_sixthPower_rate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ c : ℝ, c ∈ Set.Ioo b T ∧
      ∀ t : ℝ, t ∈ Set.Ioo c T →
        h3PathCanonicalFullPhysicalLengthAt u t ^ 6 <=
          (1 + epsilon) ^ 6 *
            (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
              (velocityH3Energy0At u b + 1)) * (T - t) ^ 2 := by
  have hEventually :=
    h3PathCanonical_fullPhysicalLength_sixthPower_terminalRate_eventually
      hH3 hNoExtension hClass hb epsilon hEpsilon
  obtain ⟨c, hcT, hSub⟩ :=
    (mem_nhdsLT_iff_exists_Ioo_subset).mp hEventually
  let m : ℝ := (b + T) / 2
  have hm : m ∈ Set.Ioo b T := by
    dsimp only [m]
    constructor <;> linarith only [hb.2]
  let d : ℝ := max m c
  have hd : d ∈ Set.Ioo b T := by
    constructor
    · exact lt_of_lt_of_le hm.1 (le_max_left m c)
    · exact max_lt hm.2 hcT
  refine ⟨d, hd, ?_⟩
  intro t ht
  have hct : c < t := lt_of_le_of_lt (le_max_right m c) ht.1
  exact hSub ⟨hct, ht.2⟩

/-- On the SAME fixed directed ten-source witness, the full physical
characteristic length obeys an indexed sixth-power upper rate while the
source rate, critical clocks and both exhaustive sign branches are retained. -/
theorem h3PathCanonical_fixedDirectedSource_fullPhysicalLength_indexedRate_withPhysicalAlternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ (i : Fin 10) (tau : ℕ → ℝ),
      (∀ n : ℕ,
        tau n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          h3PathCanonicalJointDirectedTenSourceAt u (tau n) i /
            (9 * velocityH3EnergyAt u (tau n))) ∧
      Tendsto tau atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3Energy3At u (tau n)) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        velocityH3Energy3At u (tau n) / velocityH3EnergyAt u (tau n))
        atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalTopToFullIntrinsicFrequencyRatioAt u (tau n))
        atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalTopToFullPhysicalFrequencyRatioAt u (tau n))
        atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => h3TopCharacteristicLengthAt u (tau n))
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => h3PathCanonicalFullPhysicalLengthAt u (tau n))
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalFullToTopPhysicalLengthRatioAt u (tau n))
        atTop (𝓝 1) ∧
      (∀ᶠ n : ℕ in atTop,
        ((n : ℝ) + 1) ^ 2 *
          h3PathCanonicalFullPhysicalLengthAt u (tau n) ^ 6 <=
            (1 + epsilon) ^ 6 *
              (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
                (velocityH3Energy0At u b + 1))) ∧
      (∀ᶠ n : ℕ in atTop,
        h3PathCanonicalDirectedCriticalClocksAt u T b (tau n)) ∧
      ((i = 0 ∧
          (∀ n : ℕ,
            h3PathCanonicalGradientFullDissipationBudgetAt u (tau n) (n : ℝ)) ∧
          (∀ᶠ n : ℕ in atTop,
            h3PathCanonicalGradientTopShareClockAt u T b (tau n) (n : ℝ))) ∨
        (i ≠ 0 ∧
          ∃ j r : PrimeTensor.Axis Depth.three,
            ∀ n : ℕ,
              (n : ℝ) <
                -(2 * h3PathCanonicalFirstMonomialComponentAt u (tau n) j r) /
                  velocityH3EnergyAt u (tau n))) := by
  obtain ⟨i, tau, hWitness, hTauT, hTopT, hEnergyShare, hSquaredRatio,
    hFrequencyRatio, hTopLengthT, hFullLengthT, hLengthRatioT,
    hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_physicalLengthRatio_withPhysicalAlternative
      hH3 hNoExtension hClass hb
  have hTauLT : Tendsto tau atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hTauT, Eventually.of_forall (fun n => (hWitness n).1.2)⟩
  have hRateTail :=
    h3PathCanonical_fullPhysicalLength_sixthPower_terminalRate_eventually
      hH3 hNoExtension hClass hb epsilon hEpsilon
  have hRateSeq := hTauLT.eventually hRateTail
  let C : ℝ :=
    (1 + epsilon) ^ 6 *
      (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
        (velocityH3Energy0At u b + 1))
  have hE0 : 0 <= velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hOneEps : 0 <= 1 + epsilon := by linarith only [hEpsilon]
  have hC : 0 <= C := by
    dsimp only [C]
    positivity
  have hRateIndexed : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) + 1) ^ 2 *
        h3PathCanonicalFullPhysicalLengthAt u (tau n) ^ 6 <= C := by
    filter_upwards [hRateSeq] with n hRateN
    have hNear := (hWitness n).1
    have hnPos : 0 < (n : ℝ) + 1 := by positivity
    have hDistPos : 0 < T - tau n := by linarith only [hNear.2]
    have hDistUpper : T - tau n < 1 / ((n : ℝ) + 1) := by
      linarith only [hNear.1]
    have hScaledRaw := mul_lt_mul_of_pos_left hDistUpper hnPos
    have hCancel : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by
      rw [one_div]
      exact mul_inv_cancel₀ (ne_of_gt hnPos)
    have hScaled : ((n : ℝ) + 1) * (T - tau n) < 1 :=
      lt_of_lt_of_eq hScaledRaw hCancel
    have hScaledNonneg : 0 <= ((n : ℝ) + 1) * (T - tau n) := by
      positivity
    have hScaledSq : (((n : ℝ) + 1) * (T - tau n)) ^ 2 <= 1 := by
      have hPow := pow_le_pow_left₀ hScaledNonneg (le_of_lt hScaled) 2
      simpa only [one_pow] using hPow
    have hLength : h3PathCanonicalFullPhysicalLengthAt u (tau n) ^ 6 <=
        C * (T - tau n) ^ 2 := by
      simpa only [C] using hRateN
    have hMultiply :=
      mul_le_mul_of_nonneg_left hLength (sq_nonneg ((n : ℝ) + 1))
    have hContract := mul_le_mul_of_nonneg_left hScaledSq hC
    calc
      ((n : ℝ) + 1) ^ 2 *
          h3PathCanonicalFullPhysicalLengthAt u (tau n) ^ 6 <=
          ((n : ℝ) + 1) ^ 2 * (C * (T - tau n) ^ 2) := hMultiply
      _ = C * (((n : ℝ) + 1) * (T - tau n)) ^ 2 := by ring
      _ <= C * 1 := hContract
      _ = C := by ring
  refine ⟨i, tau, hWitness, hTauT, hTopT, hEnergyShare,
    hSquaredRatio, hFrequencyRatio, hTopLengthT, hFullLengthT,
    hLengthRatioT, ?_, hClocks, hAlternative⟩
  simpa only [C] using hRateIndexed

end
end Euclidean
end Bridge
end PrimeTensor
