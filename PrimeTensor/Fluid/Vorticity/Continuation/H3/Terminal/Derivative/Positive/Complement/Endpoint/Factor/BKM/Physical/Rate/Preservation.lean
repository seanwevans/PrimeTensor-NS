import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Growth.Witness.Extraction

/-!
# Physical rates retained after energy-growth extraction

The physical-frequency branch has superpolynomial normalized
dissipation, one-copy transport excess, and adverse transport.
All three limits survive the cofinal extraction that separates
energy-growth dominance from dissipation dominance.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Three physical rates on a common original-index sequence. -/
def H3TerminalEndpointPhysicalRateData
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (τ : ℕ → ℝ) (m : ℕ → ℕ) : Prop :=
  ∀ degree : ℕ,
    Tendsto
      (fun n : ℕ =>
        (velocityH3DissipationAt u (τ (m n)) /
          velocityH3EnergyAt u (τ (m n))) /
          (((m n : ℝ) + 1) ^ degree))
      atTop atTop ∧
    Tendsto
      (fun n : ℕ =>
        h3PathTransportExcessRate u (τ (m n)) /
          (((m n : ℝ) + 1) ^ degree))
      atTop atTop ∧
    Tendsto
      (fun n : ℕ =>
        ((-velocityH3TransportDerivativeAt u (τ (m n))) /
          velocityH3EnergyAt u (τ (m n))) /
          (((m n : ℝ) + 1) ^ degree))
      atTop atTop

/-- Vorticity escape or a physical-rate witness with a persistent
dissipation-versus-logarithmic-growth split. Every physical rate
remains on the final, common native and relative-ratio witness. -/
theorem endpointFactor_relativeRefinedWitness_BKMPhysicalRatePreservation
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
        u b T p sCurl sGradient τ y k g ratio) :
    ∃ l r : ℕ → ℕ,
      Tendsto (fun n : ℕ => k (l (r n))) atTop atTop ∧
      (∀ n : ℕ, n ≤ r n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l (r n)))) (fun n => y (k (l (r n)))) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l (r n))) ∧
      (Tendsto
          (fun n : ℕ =>
            (1 + |g (τ (k (l (r n))))|) ^ 2 /
              ((k (l (r n)) : ℝ) + 1))
          atTop atTop ∨
        (H3TerminalEndpointPhysicalRateData u τ
            (fun n => k (l (r n))) ∧
          ((∀ᶠ n : ℕ in atTop,
              h3PathTransportExcessRate u (τ (k (l (r n)))) ≤
                2 * (velocityH3DissipationAt u (τ (k (l (r n)))) /
                  velocityH3EnergyAt u (τ (k (l (r n)))))) ∨
            (∀ degree : ℕ,
              Tendsto
                (fun n : ℕ =>
                  (deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) /
                    velocityH3EnergyAt u (τ (k (l (r n))))) /
                    (((k (l (r n)) : ℝ) + 1) ^ degree))
                atTop atTop)))) := by
  obtain ⟨l, q, hIndex, hqIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMAdverseTransportRate
      hH3 hNoExtension hClass hb hg hWitness
  rcases hBranches with hVorticity | hPhysical
  · exact ⟨l, q, hIndex, hqIndex, hNative, hRatio,
      Or.inl hVorticity⟩
  have hNativeCopy := hNative
  obtain ⟨hAt, _, _, _, _, _, _, _, _⟩ := hNativeCopy
  have hBalance : ∀ n : ℕ,
      h3PathTransportExcessRate u (τ (k (l (q n)))) =
        deriv (velocityH3EnergyAt u) (τ (k (l (q n)))) /
          velocityH3EnergyAt u (τ (k (l (q n)))) +
        velocityH3DissipationAt u (τ (k (l (q n)))) /
          velocityH3EnergyAt u (τ (k (l (q n)))) := by
    intro n
    have ht : τ (k (l (q n))) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (hAt n).1.1, (hAt n).1.2⟩
    have hDerivative :
        0 ≤ deriv (velocityH3EnergyAt u) (τ (k (l (q n)))) :=
      (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n).trans
        (le_of_lt (hAt n).2.2.1)
    exact h3PathTransportExcessRate_eq_deriv_div_energy_add_dissipation_div_energy_of_nonnegative_deriv
      hH3 hClass ht hDerivative
  have hSplit := endpointPhysical_halfExcess_split
    (fun n => h3PathTransportExcessRate u (τ (k (l (q n)))))
    (fun n =>
      deriv (velocityH3EnergyAt u) (τ (k (l (q n)))) /
        velocityH3EnergyAt u (τ (k (l (q n)))))
    (fun n =>
      velocityH3DissipationAt u (τ (k (l (q n)))) /
        velocityH3EnergyAt u (τ (k (l (q n)))))
    (fun degree n => ((k (l (q n)) : ℝ) + 1) ^ degree)
    hBalance (fun degree n => by positivity)
    (fun degree => (hPhysical degree).2.1)
  rcases hSplit with hDissipation | ⟨j, hj, hGrowth⟩
  · exact ⟨l, q, hIndex, hqIndex, hNative, hRatio,
      Or.inr ⟨hPhysical, Or.inl hDissipation⟩⟩
  have hjTop : Tendsto j atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hj n)
  have hNative' :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l (q (j n)))))
          (fun n => y (k (l (q (j n))))) :=
    positiveGrowth_quantitativeNativeData_comp_cofinal hNative hj
  have hRatio' : ∀ n : ℕ,
      (n : ℝ) + 1 < ratio (l (q (j n))) := by
    intro n
    have hCast : (n : ℝ) ≤ (j n : ℝ) := by
      exact_mod_cast (hj n)
    exact lt_of_le_of_lt (by linarith) (hRatio (j n))
  have hPhysical' : H3TerminalEndpointPhysicalRateData u τ
      (fun n => k (l (q (j n)))) := by
    intro degree
    obtain ⟨hD, hQ, hT⟩ := hPhysical degree
    exact ⟨hD.comp hjTop, hQ.comp hjTop, hT.comp hjTop⟩
  exact ⟨l, (fun n => q (j n)), hIndex.comp hjTop,
    (fun n => (hj n).trans (hqIndex (j n))),
    hNative', hRatio', Or.inr ⟨hPhysical', Or.inr hGrowth⟩⟩

end

end Euclidean
end Bridge
end PrimeTensor
