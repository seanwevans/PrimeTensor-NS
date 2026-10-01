import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Physical.Separate.Rates
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Transport.Excess.Exact.Decomposition

/-!
# Adverse transport on the endpoint frequency branch

At positive-growth times, the exact H³ balance identifies adverse
transport divided by energy with one-copy transport excess plus
normalized dissipation. This transfers the frequency branch's
superpolynomial physical growth to the adverse transport rate itself.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- At nonnegative energy-growth times, adverse transport divided by
energy is exactly the one-copy excess plus normalized dissipation. -/
theorem h3PathTransportExcessRate_add_dissipation_div_eq_neg_transport_div
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hDerivative : 0 ≤ deriv (velocityH3EnergyAt u) t) :
    h3PathTransportExcessRate u t +
        velocityH3DissipationAt u t / velocityH3EnergyAt u t =
      (-velocityH3TransportDerivativeAt u t) /
        velocityH3EnergyAt u t := by
  have hBalance :=
    deriv_velocityH3EnergyAt_add_two_dissipation_eq_neg_transport
      hH3 hClass ht
  have hExcess :=
    h3PathTransportExcessRate_eq_deriv_div_energy_add_dissipation_div_energy_of_nonnegative_deriv
      hH3 hClass ht hDerivative
  calc
    h3PathTransportExcessRate u t +
        velocityH3DissipationAt u t / velocityH3EnergyAt u t =
      deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t +
        velocityH3DissipationAt u t / velocityH3EnergyAt u t +
        velocityH3DissipationAt u t / velocityH3EnergyAt u t := by
          rw [hExcess]
    _ = (-velocityH3TransportDerivativeAt u t) /
        velocityH3EnergyAt u t := by
      rw [← hBalance]
      ring

/-- The frequency branch also makes adverse transport per H³ energy
superpolynomial in the original index, alongside dissipation and the
one-copy excess. -/
theorem endpointFactor_relativeRefinedWitness_BKMAdverseTransportRate
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
    ∃ l q : ℕ → ℕ,
      Tendsto (fun n : ℕ => k (l (q n))) atTop atTop ∧
      (∀ n : ℕ, n ≤ q n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l (q n)))) (fun n => y (k (l (q n)))) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l (q n))) ∧
      (Tendsto
          (fun n : ℕ =>
            (1 + |g (τ (k (l (q n))))|) ^ 2 /
              ((k (l (q n)) : ℝ) + 1))
          atTop atTop ∨
        (∀ degree : ℕ,
          Tendsto
            (fun n : ℕ =>
              (velocityH3DissipationAt u (τ (k (l (q n)))) /
                velocityH3EnergyAt u (τ (k (l (q n))))) /
                (((k (l (q n)) : ℝ) + 1) ^ degree))
            atTop atTop ∧
          Tendsto
            (fun n : ℕ =>
              h3PathTransportExcessRate u (τ (k (l (q n)))) /
                (((k (l (q n)) : ℝ) + 1) ^ degree))
            atTop atTop ∧
          Tendsto
            (fun n : ℕ =>
              ((-velocityH3TransportDerivativeAt u (τ (k (l (q n))))) /
                velocityH3EnergyAt u (τ (k (l (q n))))) /
                (((k (l (q n)) : ℝ) + 1) ^ degree))
            atTop atTop)) := by
  obtain ⟨l, q, hIndex, hqIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMPhysicalSeparateRates
      hH3 hNoExtension hClass hb hg hWitness
  refine ⟨l, q, hIndex, hqIndex, hNative, hRatio, ?_⟩
  rcases hBranches with hVorticity | hPhysical
  · exact Or.inl hVorticity
  right
  obtain ⟨hAt, _, _, _, _, _, _, _, _⟩ := hNative
  have hPoint : ∀ n : ℕ,
      h3PathTransportExcessRate u (τ (k (l (q n)))) ≤
        (-velocityH3TransportDerivativeAt u (τ (k (l (q n))))) /
          velocityH3EnergyAt u (τ (k (l (q n)))) := by
    intro n
    have ht : τ (k (l (q n))) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (hAt n).1.1, (hAt n).1.2⟩
    have hDerivative :
        0 ≤ deriv (velocityH3EnergyAt u) (τ (k (l (q n)))) :=
      (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n).trans
        (le_of_lt (hAt n).2.2.1)
    have hDNonneg :
        0 ≤ velocityH3DissipationAt u (τ (k (l (q n)))) /
          velocityH3EnergyAt u (τ (k (l (q n)))) :=
      div_nonneg
        (velocityH3DissipationAt_nonneg _ _)
        (le_trans (by norm_num) (one_le_velocityH3EnergyAt _ _))
    calc
      h3PathTransportExcessRate u (τ (k (l (q n)))) ≤
          h3PathTransportExcessRate u (τ (k (l (q n)))) +
            velocityH3DissipationAt u (τ (k (l (q n)))) /
              velocityH3EnergyAt u (τ (k (l (q n)))) := by
            linarith
      _ = _ :=
        h3PathTransportExcessRate_add_dissipation_div_eq_neg_transport_div
          hH3 hClass ht hDerivative
  intro degree
  obtain ⟨hDissipation, hExcess⟩ := hPhysical degree
  refine ⟨hDissipation, hExcess, ?_⟩
  refine tendsto_atTop.2 ?_
  intro C
  filter_upwards [hExcess.eventually (eventually_ge_atTop C)] with n hn
  have hDen : 0 < ((k (l (q n)) : ℝ) + 1) ^ degree := by
    positivity
  have hMul :
      C * (((k (l (q n)) : ℝ) + 1) ^ degree) ≤
        h3PathTransportExcessRate u (τ (k (l (q n)))) :=
    (le_div_iff₀ hDen).1 hn
  exact (le_div_iff₀ hDen).2 (hMul.trans (hPoint n))

end

end Euclidean
end Bridge
end PrimeTensor
