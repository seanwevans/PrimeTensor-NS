import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Frequency.Exponential.Rate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.Frequency.Dissipation.Barrier

/-!
# Exponential polynomial dissipation ratios on the endpoint witness

The top characteristic frequency squared is exactly top-order
dissipation divided by top-order energy. The established amplitude
comparison also bounds that square by an anchored multiple of full
normalized dissipation on the positive-growth witness. Thus the
frequency's exponential polynomial lower bounds transfer to both ratios.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Every exponential polynomial frequency lower bound transfers to
the intrinsic top-order dissipation ratio and to anchored full
normalized dissipation on the same native witness. -/
theorem endpointFactor_relativeRefinedWitness_exponentialDissipationRate
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
      (∀ M : ℝ, ∀ degree : ℕ,
        ∀ᶠ n : ℕ in atTop,
          Real.exp (M * (((k (l (r n)) : ℝ) + 1) ^ degree)) <
            h3TopCharacteristicFrequencyAt u (τ (k (l (r n))))) ∧
      (∀ M : ℝ, ∀ degree : ℕ,
        ∀ᶠ n : ℕ in atTop,
          Real.exp (M * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
            velocityH3Dissipation3At u (τ (k (l (r n)))) /
              velocityH3Energy3At u (τ (k (l (r n)))) ∧
          Real.exp (M * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
            (4 + 3 * velocityH3Energy0At u b) *
              (velocityH3DissipationAt u (τ (k (l (r n)))) /
                velocityH3EnergyAt u (τ (k (l (r n)))))) := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio,
      hPhysical, hGrowthShare, hExcessShare, _, hFrequency⟩ :=
    endpointFactor_relativeRefinedWitness_frequencyExponentialPolynomialRate
      hH3 hNoExtension hClass hb hg hWitness
      C growthDegree hGrowthCeiling B hVorticityCeiling
  refine ⟨l, r, hIndex, hrIndex, hNative, hRatio,
    hPhysical, hGrowthShare, hExcessShare, hFrequency, ?_⟩
  have hFull := positiveGrowth_nativeWitness_frequencySq_le_dissipationRatio
    hH3 hNoExtension hClass hb hNative
  intro M degree
  filter_upwards [hFrequency M degree, hFull] with n hnFreq hnFull
  have hExpNonneg :
      0 ≤ Real.exp (M * (((k (l (r n)) : ℝ) + 1) ^ degree)) :=
    le_of_lt (Real.exp_pos _)
  have hSquare :
      Real.exp (M * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
        h3TopCharacteristicFrequencyAt u (τ (k (l (r n)))) ^ 2 :=
    pow_lt_pow_left₀ hnFreq hExpNonneg (by norm_num)
  have hTop :
      Real.exp (M * (((k (l (r n)) : ℝ) + 1) ^ degree)) ^ 2 <
        velocityH3Dissipation3At u (τ (k (l (r n)))) /
          velocityH3Energy3At u (τ (k (l (r n)))) := by
    simpa only [h3TopCharacteristicFrequencyAt_sq] using hSquare
  exact ⟨hTop, hSquare.trans_le hnFull⟩

end

end Euclidean
end Bridge
end PrimeTensor
