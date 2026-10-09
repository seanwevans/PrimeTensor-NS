import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceShiftedEnergyClock

/-!
# Preserve the original source index rate through the physical H³ split

The original fixed-ten-source construction selected terminal times `τ n`
with the *pointwise indexed witness* `n < S_i(τ n)/(9 E(τ n))` for every
natural `n`. Later physical-clocks and signed-source theorems retained only
that the ratio tends to infinity, losing this more precise bound.

We restore the original indexed witness and intersect its times with the
already-established three late-time physical clocks. In the gradient branch:

    9 n < 24 C1 sqrt(E(τ n)) - Λ3(τ n)^2

holds for every n, and the *moving*, rather than constant, shifted-energy
clock with shift `R = n` holds eventually. In the velocity branch one fixed
ordered physical monomial has `n < -2 Q(j,r)(τ n)/E(τ n)` for every n.

The branch classification is neutral: neither branch is excluded, and no
claim of global regularity or an actual singularity is made.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Ordered axes of one nonzero directed source. The index-zero value is
arbitrary; that case is excluded when the pair is used. -/
private def h3PathCanonicalIndexedSourcePair
    (i : Fin 10) :
    PrimeTensor.Axis Depth.three × PrimeTensor.Axis Depth.three :=
  match i.val with
  | 1 => (xAxis, xAxis)
  | 2 => (yAxis, yAxis)
  | 3 => (zAxis, zAxis)
  | 4 => (xAxis, yAxis)
  | 5 => (yAxis, xAxis)
  | 6 => (xAxis, zAxis)
  | 7 => (zAxis, xAxis)
  | 8 => (yAxis, zAxis)
  | _ => (zAxis, yAxis)

/-- Convert the exact index-level source bound to a physical ordered
monomial bound. Diagonal sources carry weight nine and off-diagonal
sources carry weight eighteen. -/
private theorem h3PathCanonical_indexedSource_forces_orderedDeficit
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ) (i : Fin 10) (hi : i ≠ 0) (R : ℝ)
    (hR : 0 ≤ R)
    (hLarge :
      R < h3PathCanonicalJointDirectedTenSourceAt u t i /
        (9 * velocityH3EnergyAt u t)) :
    R <
      -(2 * h3PathCanonicalFirstMonomialComponentAt u t
        (h3PathCanonicalIndexedSourcePair i).1
        (h3PathCanonicalIndexedSourcePair i).2) /
          velocityH3EnergyAt u t := by
  have hE : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hDen : 0 < 9 * velocityH3EnergyAt u t := by
    positivity
  have hRaw : 9 * R * velocityH3EnergyAt u t <
      h3PathCanonicalJointDirectedTenSourceAt u t i := by
    calc
      9 * R * velocityH3EnergyAt u t =
          R * (9 * velocityH3EnergyAt u t) := by ring
      _ < _ := (lt_div_iff₀ hDen).mp hLarge
  have hRE : 0 ≤ R * velocityH3EnergyAt u t :=
    mul_nonneg hR hE.le
  have hOrdered :
      R * velocityH3EnergyAt u t <
        -(2 * h3PathCanonicalFirstMonomialComponentAt u t
          (h3PathCanonicalIndexedSourcePair i).1
          (h3PathCanonicalIndexedSourcePair i).2) := by
    fin_cases i
    · exact (hi rfl).elim
    all_goals
      simp [h3PathCanonicalJointDirectedTenSourceAt,
        h3PathCanonicalIndexedSourcePair] at hRaw ⊢ <;>
        nlinarith only [hRaw, hRE]
  exact (lt_div_iff₀ hE).2 hOrdered

/-- The full original indexed source witness is compatible with all three
physical critical clocks on the *same* terminal times. The stronger indexed
witness, not only convergence of the source ratio, is retained. -/
theorem h3PathCanonical_fixedDirectedSource_indexedCriticalClocks
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ (i : Fin 10) (τ : ℕ → ℝ),
      (∀ n : ℕ,
        τ n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n))) ∧
      Tendsto τ atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
          (9 * velocityH3EnergyAt u (τ n))) atTop atTop ∧
      Tendsto (fun n : ℕ => velocityH3Energy3At u (τ n)) atTop atTop ∧
      (∀ᶠ n : ℕ in atTop,
        h3PathCanonicalDirectedCriticalClocksAt u T b (τ n)) := by
  obtain ⟨i, τ, hWitness, hτT, hSourceT, _hRate, hThirdT⟩ :=
    h3PathCanonical_fixedDirectedSource_thirdEnergyBlowup_sameSequence
      hH3 hNoExtension hClass hb
  obtain ⟨cF, hcF, hFrequencyClock⟩ :=
    exists_terminalTail_characteristicFrequency_pow_six_rate_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  obtain ⟨cD, hcDT, hDissipationClock⟩ :=
    (mem_nhdsLT_iff_exists_Ioo_subset).1
      (eventually_normalized_dissipation3_cubic_rate_of_noH3PathExtension
        hH3 hNoExtension hClass hb)
  obtain ⟨cG, hcG, hBalanceClock⟩ :=
    exists_terminalTail_normalized_balanceGap_cubic_rate_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  have hLateF : ∀ᶠ n : ℕ in atTop, cF < τ n :=
    (tendsto_order.1 hτT).1 cF hcF.2
  have hLateD : ∀ᶠ n : ℕ in atTop, cD < τ n :=
    (tendsto_order.1 hτT).1 cD hcDT
  have hLateG : ∀ᶠ n : ℕ in atTop, cG < τ n :=
    (tendsto_order.1 hτT).1 cG hcG.2
  have hClocks : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalDirectedCriticalClocksAt u T b (τ n) := by
    filter_upwards [hLateF, hLateD, hLateG] with n hnF hnD hnG
    change
      (1 ≤
        3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
          (velocityH3Energy0At u b + 1) *
          (T - τ n) ^ 2 * h3TopCharacteristicFrequencyAt u (τ n) ^ 6) ∧
      (1 ≤
        3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
          (velocityH3Energy0At u b + 1) *
          (4 + 3 * velocityH3Energy0At u b) ^ 3 *
          (T - τ n) ^ 2 *
          (velocityH3Dissipation3At u (τ n) /
            velocityH3EnergyAt u (τ n)) ^ 3) ∧
      (8 ≤
        3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
          (velocityH3Energy0At u b + 1) *
          (4 + 3 * velocityH3Energy0At u b) ^ 3 *
          (T - τ n) ^ 2 *
          (((-velocityH3TransportDerivativeAt u (τ n) -
            deriv (velocityH3EnergyAt u) (τ n)) /
            velocityH3EnergyAt u (τ n)) ^ 3))
    exact ⟨hFrequencyClock (τ n) ⟨hnF, (hWitness n).1.2⟩,
      hDissipationClock ⟨hnD, (hWitness n).1.2⟩,
      hBalanceClock (τ n) ⟨hnG, (hWitness n).1.2⟩⟩
  exact ⟨i, τ, hWitness, hτT, hSourceT, hThirdT, hClocks⟩

/-- Quantitative original-index physical dichotomy. Unlike a statement for
every fixed shift R, the gradient clock is shifted by the *varying* index n
itself. Likewise the ordered velocity alternative has an indexed lower bound
at each time, not merely asymptotic divergence. -/
theorem h3PathCanonical_fixedDirectedSource_indexedGap_or_indexedSignedMonomial
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ (i : Fin 10) (τ : ℕ → ℝ),
      (∀ n : ℕ,
        τ n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n))) ∧
      Tendsto τ atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ => velocityH3Energy3At u (τ n)) atTop atTop ∧
      (∀ᶠ n : ℕ in atTop,
        h3PathCanonicalDirectedCriticalClocksAt u T b (τ n)) ∧
      ((i = 0 ∧
          (∀ n : ℕ,
            9 * (n : ℝ) <
              24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
                Real.sqrt (velocityH3EnergyAt u (τ n))) -
                h3TopCharacteristicFrequencyAt u (τ n) ^ 2) ∧
          (∀ᶠ n : ℕ in atTop,
            h3PathCanonicalGradientShiftedEnergyClockAt
              u T b (τ n) (n : ℝ))) ∨
        (i ≠ 0 ∧
          ∃ j r : PrimeTensor.Axis Depth.three,
            ∀ n : ℕ,
              (n : ℝ) <
                -(2 * h3PathCanonicalFirstMonomialComponentAt u (τ n) j r) /
                  velocityH3EnergyAt u (τ n))) := by
  obtain ⟨i, τ, hWitness, hτT, _hSourceT, hThirdT, hClocks⟩ :=
    h3PathCanonical_fixedDirectedSource_indexedCriticalClocks
      hH3 hNoExtension hClass hb
  refine ⟨i, τ, hWitness, hτT, hThirdT, hClocks, ?_⟩
  by_cases hi : i = 0
  · left
    refine ⟨hi, ?_, ?_⟩
    · intro n
      have hGradient :
          (n : ℝ) <
            (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
              Real.sqrt (velocityH3EnergyAt u (τ n))) *
              velocityH3Energy3At u (τ n) -
              velocityH3DissipationAt u (τ n)) /
              (9 * velocityH3EnergyAt u (τ n)) := by
        simpa [hi, h3PathCanonicalJointDirectedTenSourceAt] using
          (hWitness n).2
      exact h3PathCanonical_gradientSource_rate_forces_spectralGap
        u (τ n) (n : ℝ) (Nat.cast_nonneg n) hGradient
    · filter_upwards [hClocks] with n hnClock
      have hGradient :
          (n : ℝ) <
            (24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
              Real.sqrt (velocityH3EnergyAt u (τ n))) *
              velocityH3Energy3At u (τ n) -
              velocityH3DissipationAt u (τ n)) /
              (9 * velocityH3EnergyAt u (τ n)) := by
        simpa [hi, h3PathCanonicalJointDirectedTenSourceAt] using
          (hWitness n).2
      exact h3PathCanonical_gradientSource_rate_forces_shiftedEnergyClock
        u T b (τ n) (n : ℝ) (hWitness n).1.2
        (Nat.cast_nonneg n) hnClock.1 hGradient
  · right
    refine ⟨hi,
      (h3PathCanonicalIndexedSourcePair i).1,
      (h3PathCanonicalIndexedSourcePair i).2, ?_⟩
    intro n
    exact h3PathCanonical_indexedSource_forces_orderedDeficit
      u (τ n) i hi (n : ℝ) (Nat.cast_nonneg n) (hWitness n).2

end
end Euclidean
end Bridge
end PrimeTensor
