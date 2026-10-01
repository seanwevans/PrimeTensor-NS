import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.Bound.Transfer
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Characteristic.Frequency.Amplitude.Corridor

/-!
# Logarithmic energy factor controlled by characteristic frequency

On a late positive-growth tail under hypothetical nonextension, the
existing amplitude corridor bounds H³ energy by an anchor constant
times the sixth power of the top characteristic frequency. This file
transfers its logarithmic consequence to the quantitative native
witness, including the refined persistent BKM factor branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The H³ logarithmic energy factor is eventually bounded by the
logarithm of the existing characteristic-frequency amplitude bound
on any quantitative native positive-growth witness. -/
theorem positiveGrowth_nativeWitness_logEnergy_le_frequencyLog
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y) :
    ∀ᶠ n : ℕ in atTop,
      1 + Real.log (velocityH3EnergyAt u (τ n)) ≤
        1 + Real.log
          ((4 + 3 * velocityH3Energy0At u b) *
            (velocityH3Energy0At u b + 1) *
            h3TopCharacteristicFrequencyAt u (τ n) ^ 6) := by
  obtain ⟨c, hc, hCorridor⟩ :=
    exists_terminalTail_positiveGrowth_characteristicFrequencyAmplitudeCorridor_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  obtain ⟨hAt, hTau, hEnergy, _, _, _, _, _, _⟩ := hData
  have hLate : ∀ᶠ n : ℕ in atTop, c < τ n :=
    (tendsto_order.1 hTau).1 c hc.2
  have hEnergyOne : ∀ᶠ n : ℕ in atTop,
      1 ≤ velocityH3EnergyAt u (τ n) :=
    hEnergy.eventually (eventually_ge_atTop 1)
  filter_upwards [hLate, hEnergyOne] with n hnLate hnEnergy
  have hAtTail : τ n ∈ Set.Ioo c T :=
    ⟨hnLate, (hAt n).1.2⟩
  have hDerivative : 0 < deriv (velocityH3EnergyAt u) (τ n) := by
    have hnNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact lt_of_le_of_lt hnNonneg (hAt n).2.2.1
  have hAmplitude := (hCorridor (τ n) hAtTail hDerivative).2
  have hLog := Real.log_le_log
    (by linarith : 0 < velocityH3EnergyAt u (τ n)) hAmplitude
  linarith

/-- The refined persistent factor-rate witness retains the logarithmic
energy upper control by characteristic frequency on the same indices. -/
theorem endpointFactor_relativeRefinedWitness_logEnergy_le_frequencyLog
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    {ratio : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hWitness :
      H3TerminalEndpointFactorRelativeRefinedWitness
        u b T p sCurl sGradient τ y k g ratio) :
    ∃ l : ℕ → ℕ,
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l n))) (fun n => y (k (l n))) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l n)) ∧
      (Tendsto
          (fun n : ℕ =>
            (1 + |g (τ (k (l n)))|) ^ 2 /
              ((k (l n) : ℝ) + 1))
          atTop atTop ∨
        Tendsto
          (fun n : ℕ =>
            (1 + Real.log (velocityH3EnergyAt u (τ (k (l n))))) ^ 2 /
              ((k (l n) : ℝ) + 1))
          atTop atTop) ∧
      (∀ᶠ n : ℕ in atTop,
        1 + Real.log (velocityH3EnergyAt u (τ (k (l n)))) ≤
          1 + Real.log
            ((4 + 3 * velocityH3Energy0At u b) *
              (velocityH3Energy0At u b + 1) *
              h3TopCharacteristicFrequencyAt u (τ (k (l n))) ^ 6)) := by
  obtain ⟨l, _, _, hNative, _, hRate, hRatio⟩ := hWitness
  exact ⟨l, hNative, hRatio, hRate,
    positiveGrowth_nativeWitness_logEnergy_le_frequencyLog
      hH3 hNoExtension hClass hb hNative⟩

end

end Euclidean
end Bridge
end PrimeTensor
