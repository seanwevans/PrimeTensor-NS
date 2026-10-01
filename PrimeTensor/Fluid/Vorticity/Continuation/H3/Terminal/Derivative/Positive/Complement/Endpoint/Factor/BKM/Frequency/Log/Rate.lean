import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Log.Energy.Rate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.Frequency.Log

/-!
# Anchored frequency logarithm forced by the physical endpoint branch

The positive-growth amplitude corridor bounds the logarithmic H³ energy
factor by the logarithm of an anchored sixth power of characteristic
frequency. The superpolynomial energy-log rate therefore passes to that
anchored frequency logarithm on the same selected witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- An eventual upper bound preserves every superpolynomial lower rate
after division by a common positive scale. -/
theorem superpolynomial_rate_of_eventually_le
    (L R scale : ℕ → ℝ)
    (hScale : ∀ n, 0 < scale n)
    (hL : ∀ degree : ℕ,
      Tendsto (fun n => L n / scale n ^ degree) atTop atTop)
    (hBound : ∀ᶠ n : ℕ in atTop, L n ≤ R n) :
    ∀ degree : ℕ,
      Tendsto (fun n => R n / scale n ^ degree) atTop atTop := by
  intro degree
  refine tendsto_atTop.2 ?_
  intro C
  filter_upwards
      [(hL degree).eventually (eventually_ge_atTop C), hBound]
    with n hnLarge hnBound
  have hp : 0 < scale n ^ degree := pow_pos (hScale n) _
  have hLower : C * scale n ^ degree ≤ L n :=
    (le_div_iff₀ hp).mp hnLarge
  exact (le_div_iff₀ hp).2 (hLower.trans hnBound)

/-- With polynomial energy-growth and bounded normalized vorticity,
the anchored characteristic-frequency logarithm outruns every fixed
power of the original index on the same physical and native witness. -/
theorem endpointFactor_relativeRefinedWitness_anchoredFrequencyLogSuperpolynomial
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
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hWitness :
      H3TerminalEndpointFactorRelativeRefinedWitness
        u b T p sCurl sGradient τ y k g ratio)
    (C : ℝ) (growthDegree : ℕ)
    (hGrowthCeiling : ∀ᶠ i : ℕ in atTop,
      deriv (velocityH3EnergyAt u) (τ i) /
          velocityH3EnergyAt u (τ i) ≤
        C * (((i : ℝ) + 1) ^ growthDegree))
    (B : ℝ)
    (hVorticityCeiling : ∀ᶠ i : ℕ in atTop,
      (1 + |g (τ i)|) ^ 2 / ((i : ℝ) + 1) ≤ B) :
    ∃ l r : ℕ → ℕ,
      Tendsto (fun n : ℕ => k (l (r n))) atTop atTop ∧
      (∀ n : ℕ, n ≤ r n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l (r n)))) (fun n => y (k (l (r n)))) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l (r n))) ∧
      H3TerminalEndpointPhysicalDissipationCorridorData u τ
        (fun n => k (l (r n))) ∧
      Tendsto
        (fun n : ℕ =>
          (deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) /
            velocityH3EnergyAt u (τ (k (l (r n))))) /
          ((-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) /
            velocityH3EnergyAt u (τ (k (l (r n))))))
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto
        (fun n : ℕ =>
          h3PathTransportExcessRate u (τ (k (l (r n)))) /
          ((-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) /
            velocityH3EnergyAt u (τ (k (l (r n))))))
        atTop (𝓝 ((1 : ℝ) / 2)) ∧
      (∀ degree : ℕ,
        Tendsto
          (fun n : ℕ =>
            (1 + Real.log (velocityH3EnergyAt u (τ (k (l (r n)))))) /
              (((k (l (r n)) : ℝ) + 1) ^ degree))
          atTop atTop) ∧
      (∀ degree : ℕ,
        Tendsto
          (fun n : ℕ =>
            (1 + Real.log
              ((4 + 3 * velocityH3Energy0At u b) *
                (velocityH3Energy0At u b + 1) *
                h3TopCharacteristicFrequencyAt u
                  (τ (k (l (r n)))) ^ 6)) /
              (((k (l (r n)) : ℝ) + 1) ^ degree))
          atTop atTop) := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio,
      hPhysical, hGrowthShare, hExcessShare, hLogRate⟩ :=
    endpointFactor_relativeRefinedWitness_logEnergySuperpolynomial
      hH3 hNoExtension hClass hb hg hWitness
      C growthDegree hGrowthCeiling B hVorticityCeiling
  refine ⟨l, r, hIndex, hrIndex, hNative, hRatio,
    hPhysical, hGrowthShare, hExcessShare, hLogRate, ?_⟩
  exact superpolynomial_rate_of_eventually_le
    (fun n => 1 + Real.log (velocityH3EnergyAt u (τ (k (l (r n))))))
    (fun n => 1 + Real.log
      ((4 + 3 * velocityH3Energy0At u b) *
        (velocityH3Energy0At u b + 1) *
        h3TopCharacteristicFrequencyAt u (τ (k (l (r n)))) ^ 6))
    (fun n => (k (l (r n)) : ℝ) + 1)
    (fun n => by positivity)
    hLogRate
    (positiveGrowth_nativeWitness_logEnergy_le_frequencyLog
      hH3 hNoExtension hClass hb hNative)

end

end Euclidean
end Bridge
end PrimeTensor
