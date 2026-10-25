import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralSignedCanonicalSequence244
import Mathlib.Tactic

/-!
# The physical signed cubic barrier: high H³ energy or a negative canonical channel

The fixed cofinal no-kinetic-L²-trace witness has either arbitrarily steep
negative full H³ energy slopes or an adverse signed-transport terminal sequence.
In the latter case the exact lower-order allowance prevents immediate
inference of a negative 972+3*243 canonical cubic.

The obstruction can nevertheless be made sign-definite WITHOUT assuming a
bound on that allowance: at each chosen time, either the full physical H³
energy is at least quadratic in the requested frequency rate, or the canonical
full-third cubic is strictly negative by a specified multiple of H³ energy.
In the latter case at least one of the exact gradient or interpolation
components is itself strictly negative. The branch may vary with time.

No claim is made that hypothetical nonextension implies failure of a strong
kinetic L² terminal trace, or that the high-energy corridor can be excluded.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The precise algebraic frontier: either the lower-order coefficient is
at least half the chosen normalized rate, or the signed cubic must be
negative by at least one-half that rate times the positive energy. -/
theorem h3Path_signedThirdDeficit_largeAllowance_or_negativeCubic244
    (E A C R : ℝ) (hE : 0 < E)
    (hDeficit : (R - A) * E < -C) :
    R ≤ 2 * A ∨ R * E < -(2 * C) := by
  by_cases hLarge : R ≤ 2 * A
  · exact Or.inl hLarge
  · right
    have hA : 2 * A < R := lt_of_not_ge hLarge
    have hScale : (2 * A) * E < R * E :=
      mul_lt_mul_of_pos_right hA hE
    nlinarith only [hDeficit, hScale]

/-- A genuinely negative *complete* canonical cubic has a genuinely
negative gradient or signed-interpolation constituent, retaining the exact
factor three of the physical cyclic symmetrization. -/
theorem h3Path_negativeCanonicalThird_gradient_or_interpolation244
    (G : H3SpectralVelocityState) (E R : ℝ)
    (hNegative : R * E <
      -(2 * weightedH3CanonicalFullThirdCommutator244 G)) :
    4 * weightedH3CanonicalGradientTransport244 G < -(R * E) ∨
      4 * (3 * weightedH3CanonicalSignedFirstMonomial244 G) < -(R * E) := by
  unfold weightedH3CanonicalFullThirdCommutator244 at hNegative
  by_contra hNone
  push_neg at hNone
  nlinarith only [hNegative, hNone.1, hNone.2]

/-- The adverse FULL physical transport rate forces either an explicit
high-energy corridor or a sign-definite adverse contribution in one of
THE TWO actual choice-independent weighted third-order spectral channels.
No inequality between the Fourier state and an unrelated Schwartz sample
is introduced. -/
theorem h3Path_adverseFullTransport_highEnergy_or_negativeCanonicalChannel244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) (R : ℝ)
    (hAdverse : R * velocityH3EnergyAt u t <
      -velocityH3TransportDerivativeAt u t) :
    R ≤ 48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t) ∨
    4 * weightedH3CanonicalGradientTransport244
        (h3PathWeightedSpectralState244 u T hH3 t) <
      -(R * velocityH3EnergyAt u t) ∨
    4 * (3 * weightedH3CanonicalSignedFirstMonomial244
        (h3PathWeightedSpectralState244 u T hH3 t)) <
      -(R * velocityH3EnergyAt u t) := by
  let E : ℝ := velocityH3EnergyAt u t
  let A : ℝ := 24 * (h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
    Real.sqrt E)
  let C : ℝ := weightedH3CanonicalFullThirdCommutator244
    (h3PathWeightedSpectralState244 u T hH3 t)
  have hE : 0 < E := by
    dsimp only [E]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_velocityH3EnergyAt u t)
  have hDeficit : (R - A) * E < -C := by
    dsimp only [E, A, C]
    exact h3Path_adverseFullTransport_forces_weightedThirdDeficit244
      hH3 hClass ht R hAdverse
  rcases h3Path_signedThirdDeficit_largeAllowance_or_negativeCubic244
      E A C R hE hDeficit with hHigh | hNegative
  · left
    dsimp only [A, E] at hHigh
    nlinarith only [hHigh]
  · right
    exact h3Path_negativeCanonicalThird_gradient_or_interpolation244
      (h3PathWeightedSpectralState244 u T hH3 t) E R hNegative

/-- The high-energy arm is quantitatively at least quadratic in the
normalized terminal frequency threshold. This is a physical energy bound,
not a bound on a spectral point value. -/
theorem h3Path_highAllowance_forces_quadraticPhysicalEnergy244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    (t R : ℝ) (hR : 0 ≤ R)
    (hHigh : R ≤
      48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
        Real.sqrt (velocityH3EnergyAt u t)) :
    R ^ 2 ≤
      (48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2 *
        velocityH3EnergyAt u t := by
  let A : ℝ := 48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  let E : ℝ := velocityH3EnergyAt u t
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (by norm_num)
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (one_le_velocityH3EnergyAt u t)
  have hSqrt : 0 ≤ A * Real.sqrt E :=
    mul_nonneg hA (Real.sqrt_nonneg E)
  have hSquare : R ^ 2 ≤ (A * Real.sqrt E) ^ 2 :=
    (sq_le_sq₀ hR hSqrt).mpr (by simpa only [A, E, mul_assoc] using hHigh)
  calc
    R ^ 2 ≤ (A * Real.sqrt E) ^ 2 := hSquare
    _ = A ^ 2 * E := by
      rw [mul_pow, Real.sq_sqrt hE]
    _ = _ := rfl

/-- One fixed physical signed channel yields one terminal sequence. If
it is the adverse-transport channel, every snapshot obeys the explicit
high-physical-energy / negative-gradient / negative-interpolation
trichotomy, with its same times, spectral state, and physical energy. -/
theorem h3Path_physicalNoL2Trace_forces_signedCubicBarrierSequence244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hL : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    (∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) * velocityH3EnergyAt u (τ n) <
          -deriv (velocityH3EnergyAt u) (τ n))) ∨
    (∃ τ : ℕ → ℝ,
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ n : ℕ, dist (τ n) T < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      Tendsto τ atTop (𝓝 T) ∧
      (∀ n : ℕ,
        ((n : ℝ) + 1) * velocityH3EnergyAt u (τ n) <
          -velocityH3TransportDerivativeAt u (τ n) ∧
        (((n : ℝ) + 1) ^ 2 ≤
          (48 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2 *
            velocityH3EnergyAt u (τ n) ∨
        4 * weightedH3CanonicalGradientTransport244
          (h3PathWeightedSpectralState244 u T hH3 (τ n)) <
            -(((n : ℝ) + 1) * velocityH3EnergyAt u (τ n)) ∨
        4 * (3 * weightedH3CanonicalSignedFirstMonomial244
          (h3PathWeightedSpectralState244 u T hH3 (τ n))) <
            -(((n : ℝ) + 1) * velocityH3EnergyAt u (τ n))))) := by
  rcases h3Path_physicalNoL2Trace_forces_fixedSignedCanonicalSequence244
      hH3 hClass hL hNoTrace with hFast | hTransport
  · exact Or.inl hFast
  · obtain ⟨τ, hτ, hNear, hTendsto, hRate⟩ := hTransport
    refine Or.inr ⟨τ, hτ, hNear, hTendsto, ?_⟩
    intro n
    have hClassTime : τ n ∈ Set.Ioo a T := hτ n
    have hTrip :=
      h3Path_adverseFullTransport_highEnergy_or_negativeCanonicalChannel244
        hH3 hClass hClassTime ((n : ℝ) + 1) (hRate n).1
    refine ⟨(hRate n).1, ?_⟩
    rcases hTrip with hHigh | hSigned
    · left
      exact h3Path_highAllowance_forces_quadraticPhysicalEnergy244
        (τ n) ((n : ℝ) + 1) (by positivity) hHigh
    · exact Or.inr hSigned

end
end PrimeTensor.FirstMonomialTriad
