import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalSignedFirstMonomialDirectedSourceFrequency
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Normalized.Dissipation.Threshold.Continuation

/-!
# Fixed directed signed H³ source with physical critical terminal clocks

The prior fixed-source theorem produces an actual sequence approaching `T`
on which a *single* directed signed source grows without normalized bound
and the top-order characteristic frequency diverges.  Independently, the
physical Navier--Stokes energy/dissipation and exact balance identities force
three inverse-terminal-distance inequalities on sufficiently late slices of
a hypothetically nonextendible path.  Their finite intersection therefore
holds on the *same* signed-source sequence.

The three clocks are the top frequency, normalized top dissipation, and the
exact full transport/energy-derivative balance gap.  The second theorem
identifies the favorable gradient-absorption regime as one in which the
selected persistent source cannot be the gradient-excess index zero.  These
are conditional necessary conditions, not a proof of regularity, existence
of nonextension, or a favorable sign for any ordered nonlinear pairing.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- The three previously proved critical terminal inequalities, evaluated
at one physical time.  The last is the exact PDE balance gap, not a new
adverse-transport assumption. -/
def h3PathCanonicalDirectedCriticalClocksAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b t : ℝ) : Prop :=
  (1 ≤
    3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
      (velocityH3Energy0At u b + 1) *
      (T - t) ^ 2 * h3TopCharacteristicFrequencyAt u t ^ 6) ∧
  (1 ≤
    3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
      (velocityH3Energy0At u b + 1) *
      (4 + 3 * velocityH3Energy0At u b) ^ 3 *
      (T - t) ^ 2 *
      (velocityH3Dissipation3At u t / velocityH3EnergyAt u t) ^ 3) ∧
  (8 ≤
    3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
      (velocityH3Energy0At u b + 1) *
      (4 + 3 * velocityH3Energy0At u b) ^ 3 *
      (T - t) ^ 2 *
      (((-velocityH3TransportDerivativeAt u t -
        deriv (velocityH3EnergyAt u) t) /
        velocityH3EnergyAt u t) ^ 3))

/-- One and the same physical time sequence carries a fixed signed source,
frequency divergence, and all three quantitative critical-time clocks. -/
theorem h3PathCanonical_fixedDirectedSource_criticalClocks_sameSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ (i : Fin 10) (τ : ℕ → ℝ),
      (∀ n : ℕ, τ n ∈ Set.Ioo
        (T - (1 : ℝ) / ((n : ℝ) + 1)) T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      Tendsto
        (fun n : ℕ =>
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n))) atTop atTop ∧
      Tendsto (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ n))
        atTop atTop ∧
      (∀ᶠ n : ℕ in atTop,
        h3PathCanonicalDirectedCriticalClocksAt u T b (τ n)) := by
  obtain ⟨i, τ, hNear, hτT, hSourceT, _hRatioT, hFreqT,
      _hDissipationRatioT⟩ :=
    h3PathCanonical_fixedDirectedSource_intrinsicFrequency_sameSequence
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
    exact ⟨hFrequencyClock (τ n) ⟨hnF, (hNear n).2⟩,
      hDissipationClock ⟨hnD, (hNear n).2⟩,
      hBalanceClock (τ n) ⟨hnG, (hNear n).2⟩⟩
  exact ⟨i, τ, hNear, hτT, hSourceT, hFreqT, hClocks⟩

/-- If the physical third-order gradient allowance is absorbed by full
viscous dissipation on one terminal tail, the SAME fixed-source/critical-clock
sequence can be chosen with `i ≠ 0`. Thus it comes from a genuine *ordered*
velocity first-monomial channel, rather than the gradient-excess source.
The absorption condition is explicit and is not asserted to hold generally. -/
theorem h3PathCanonical_fixedVelocitySource_criticalClocks_of_gradientAbsorption
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hAbsorption : ∃ d : ℝ, d ∈ Set.Ioo b T ∧
      ∀ t : ℝ, t ∈ Set.Ioo d T →
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u t)) * velocityH3Energy3At u t ≤
          velocityH3DissipationAt u t) :
    ∃ (i : Fin 10) (τ : ℕ → ℝ),
      i ≠ 0 ∧
      (∀ n : ℕ, τ n ∈ Set.Ioo
        (T - (1 : ℝ) / ((n : ℝ) + 1)) T) ∧
      Tendsto τ atTop (𝓝 T) ∧
      Tendsto
        (fun n : ℕ =>
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n))) atTop atTop ∧
      Tendsto (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ n))
        atTop atTop ∧
      (∀ᶠ n : ℕ in atTop,
        h3PathCanonicalDirectedCriticalClocksAt u T b (τ n)) := by
  obtain ⟨d, hd, hAbsorb⟩ := hAbsorption
  obtain ⟨i, τ, hNear, hτT, hSourceT, hFreqT, hClocks⟩ :=
    h3PathCanonical_fixedDirectedSource_criticalClocks_sameSequence
      hH3 hNoExtension hClass hb
  have hLate : ∀ᶠ n : ℕ in atTop, d < τ n :=
    (tendsto_order.1 hτT).1 d hd.2
  have hPositive : ∀ᶠ n : ℕ in atTop,
      0 < h3PathCanonicalJointDirectedTenSourceAt u (τ n) i := by
    have hOne : ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) ≤
          h3PathCanonicalJointDirectedTenSourceAt u (τ n) i /
            (9 * velocityH3EnergyAt u (τ n)) :=
      (tendsto_atTop.1 hSourceT) 1
    filter_upwards [hOne] with n hn
    have hE : 0 < velocityH3EnergyAt u (τ n) :=
      lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u (τ n))
    have hDen : 0 < 9 * velocityH3EnergyAt u (τ n) := by
      positivity
    have hNum : (1 : ℝ) * (9 * velocityH3EnergyAt u (τ n)) ≤
        h3PathCanonicalJointDirectedTenSourceAt u (τ n) i :=
      (le_div_iff₀ hDen).mp hn
    exact lt_of_lt_of_le hDen (by simpa only [one_mul] using hNum)
  have hi : i ≠ (0 : Fin 10) := by
    intro hZero
    obtain ⟨n, hnLate, hnPositive⟩ := (hLate.and hPositive).exists
    have hAbs :
        24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
          Real.sqrt (velocityH3EnergyAt u (τ n))) *
          velocityH3Energy3At u (τ n) ≤
            velocityH3DissipationAt u (τ n) :=
      hAbsorb (τ n) ⟨hnLate, (hNear n).2⟩
    rw [hZero] at hnPositive
    change 0 <
      24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u (τ n))) *
        velocityH3Energy3At u (τ n) -
        velocityH3DissipationAt u (τ n) at hnPositive
    linarith only [hnPositive, hAbs]
  exact ⟨i, τ, hi, hNear, hτT, hSourceT, hFreqT, hClocks⟩

end
end Euclidean
end Bridge
end PrimeTensor
