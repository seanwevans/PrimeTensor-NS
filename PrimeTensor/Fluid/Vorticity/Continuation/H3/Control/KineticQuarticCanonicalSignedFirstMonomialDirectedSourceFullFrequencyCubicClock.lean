import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceFullPhysicalLengthRate

/-!
# Full physical H³ frequency cubic terminal-clock floor

The full physical characteristic length satisfies, under hypothetical
nonextension, for every fixed epsilon > 0 eventually,

  ell_full(t)^6 <= (1+epsilon)^6 * C_b * (T-t)^2,
  C_b = 3 K^2 (E0(b)+1).

Since ell_full = Omega_full^{-1}, with Omega_full^2 = D/E and Omega_full
strictly positive near T, this is equivalent to

  1 <= (1+epsilon)^6 * C_b * (T-t)^2 * (D(t)/E(t))^3.

The same exact cubic floor transfers to the fixed indexed ten-source witness,
with (n+1)^2 in place of the reciprocal terminal time distance. No new
Navier--Stokes sign or nonlinear bound is introduced, and neither signed-source
branch is excluded.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- The sixth power of the full physical frequency is exactly the cube of
physical H³ dissipation divided by physical H³ energy. -/
theorem h3PathCanonical_fullPhysicalFrequency_sixth_eq_dissipationCube
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) :
    h3PathCanonicalFullPhysicalFrequencyAt u t ^ 6 =
      (velocityH3DissipationAt u t / velocityH3EnergyAt u t) ^ 3 := by
  have hD : 0 <= velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hE : 0 <= velocityH3EnergyAt u t :=
    le_trans (by norm_num) (one_le_velocityH3EnergyAt u t)
  have hRatio : 0 <= velocityH3DissipationAt u t /
      velocityH3EnergyAt u t := div_nonneg hD hE
  unfold h3PathCanonicalFullPhysicalFrequencyAt
  calc
    (Real.sqrt (velocityH3DissipationAt u t /
        velocityH3EnergyAt u t)) ^ 6 =
        ((Real.sqrt (velocityH3DissipationAt u t /
          velocityH3EnergyAt u t)) ^ 2) ^ 3 := by ring
    _ = (velocityH3DissipationAt u t /
          velocityH3EnergyAt u t) ^ 3 := by
      rw [Real.sq_sqrt hRatio]

/-- Algebraic reciprocal-length duality, also valid with an indexed
nonnegative clock factor `s` on the left. -/
theorem h3PathCanonical_indexedLengthRate_implies_frequencyFloor
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t s C : ℝ)
    (hFreq : 0 < h3PathCanonicalFullPhysicalFrequencyAt u t)
    (hLength : s * h3PathCanonicalFullPhysicalLengthAt u t ^ 6 <= C) :
    s <= C * h3PathCanonicalFullPhysicalFrequencyAt u t ^ 6 := by
  have hFreqPower : 0 <= h3PathCanonicalFullPhysicalFrequencyAt u t ^ 6 :=
    pow_nonneg hFreq.le 6
  have hMultiply := mul_le_mul_of_nonneg_right hLength hFreqPower
  have hCancel : h3PathCanonicalFullPhysicalLengthAt u t ^ 6 *
      h3PathCanonicalFullPhysicalFrequencyAt u t ^ 6 = 1 := by
    unfold h3PathCanonicalFullPhysicalLengthAt
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hFreq), one_pow]
  calc
    s = (s * h3PathCanonicalFullPhysicalLengthAt u t ^ 6) *
          h3PathCanonicalFullPhysicalFrequencyAt u t ^ 6 := by
      rw [mul_assoc, hCancel, mul_one]
    _ <= C * h3PathCanonicalFullPhysicalFrequencyAt u t ^ 6 := hMultiply

/-- The full physical `D/E` ratio obeys the terminal-distance cubic lower
clock with the asymptotically sharp top-order coefficient for any epsilon. -/
theorem h3PathCanonical_fullPhysicalDissipationCubic_terminalClock_eventually
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      1 <= ((1 + epsilon) ^ 6 *
        (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
          (velocityH3Energy0At u b + 1)) * (T - t) ^ 2) *
        (velocityH3DissipationAt u t / velocityH3EnergyAt u t) ^ 3 := by
  have hRate :=
    h3PathCanonical_fullPhysicalLength_sixthPower_terminalRate_eventually
      hH3 hNoExtension hClass hb epsilon hEpsilon
  have hD3T : Tendsto (velocityH3Dissipation3At u) (𝓝[<] T) atTop :=
    velocityH3Dissipation3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hD3Pos : ∀ᶠ t : ℝ in 𝓝[<] T,
      0 < velocityH3Dissipation3At u t := by
    filter_upwards [(tendsto_atTop.1 hD3T) 1] with t ht
    linarith only [ht]
  filter_upwards [hRate, hD3Pos] with t ht hD3
  have hFreq : 0 < h3PathCanonicalFullPhysicalFrequencyAt u t :=
    h3PathCanonical_fullPhysicalFrequency_pos_of_topDissipation_pos
      u t hD3
  have hLength : 1 * h3PathCanonicalFullPhysicalLengthAt u t ^ 6 <=
      (1 + epsilon) ^ 6 *
        (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
          (velocityH3Energy0At u b + 1)) * (T - t) ^ 2 := by
    simpa only [one_mul] using ht
  have hFloor := h3PathCanonical_indexedLengthRate_implies_frequencyFloor
    u t 1
      ((1 + epsilon) ^ 6 *
        (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
          (velocityH3Energy0At u b + 1)) * (T - t) ^ 2)
      hFreq hLength
  rw [h3PathCanonical_fullPhysicalFrequency_sixth_eq_dissipationCube] at hFloor
  exact hFloor

/-- A single unchanged ten-source terminal witness simultaneously has the
indexed source blowup, top/full concentration, three critical clocks, both
sign alternatives, and the physical dissipation cubic indexed floor. -/
theorem h3PathCanonical_fixedDirectedSource_fullDissipationCubicIndexed_withPhysicalAlternative
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
        ((n : ℝ) + 1) ^ 2 <=
          ((1 + epsilon) ^ 6 *
            (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
              (velocityH3Energy0At u b + 1))) *
            (velocityH3DissipationAt u (tau n) /
              velocityH3EnergyAt u (tau n)) ^ 3) ∧
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
    hLengthRate, hClocks, hAlternative⟩ :=
    h3PathCanonical_fixedDirectedSource_fullPhysicalLength_indexedRate_withPhysicalAlternative
      hH3 hNoExtension hClass hb epsilon hEpsilon
  have hTauLT : Tendsto tau atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hTauT, Eventually.of_forall (fun n => (hWitness n).1.2)⟩
  have hD3T : Tendsto (velocityH3Dissipation3At u) (𝓝[<] T) atTop :=
    velocityH3Dissipation3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hD3Positive : ∀ᶠ n : ℕ in atTop,
      0 < velocityH3Dissipation3At u (tau n) := by
    have hD3Large := (tendsto_atTop.1 (hD3T.comp hTauLT)) 1
    filter_upwards [hD3Large] with n hDn
    change (1 : ℝ) ≤ velocityH3Dissipation3At u (tau n) at hDn
    exact lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) hDn
  have hIndexedFloor : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) + 1) ^ 2 <=
        ((1 + epsilon) ^ 6 *
          (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
            (velocityH3Energy0At u b + 1))) *
          (velocityH3DissipationAt u (tau n) /
            velocityH3EnergyAt u (tau n)) ^ 3 := by
    filter_upwards [hLengthRate, hD3Positive] with n hLength hD3
    have hFreq : 0 < h3PathCanonicalFullPhysicalFrequencyAt u (tau n) :=
      h3PathCanonical_fullPhysicalFrequency_pos_of_topDissipation_pos
        u (tau n) hD3
    have hFloor := h3PathCanonical_indexedLengthRate_implies_frequencyFloor
      u (tau n) (((n : ℝ) + 1) ^ 2)
      ((1 + epsilon) ^ 6 *
        (3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
          (velocityH3Energy0At u b + 1)))
      hFreq hLength
    rw [h3PathCanonical_fullPhysicalFrequency_sixth_eq_dissipationCube] at hFloor
    exact hFloor
  exact ⟨i, tau, hWitness, hTauT, hTopT, hEnergyShare, hSquaredRatio,
    hFrequencyRatio, hTopLengthT, hFullLengthT, hLengthRatioT, hLengthRate,
    hIndexedFloor, hClocks, hAlternative⟩

end
end Euclidean
end Bridge
end PrimeTensor
