import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalCancellationShareRates

/-!
# Physical H³ energy and slope forced on the common direct spectral clock

The earlier exact direct terminal witness has both actual normalized full-
dissipation transport excess q₀ and spectral commutator shortfall S larger
than every prescribed index. The physical PDE balance and nonnegative full
H³ dissipation turn those separate normalized statements, *at the same
physical time*, into the unnormalized bounds

    n < 4422 C₁ sqrt(E(t)),
    n² < (4422 C₁)² E(t),
    n E(t) < E'(t).

The strict inequalities persist after extracting the pre-existing compact
cancellation-share cluster. The terminal clock, exact direct selection,
actual q₀ divergence and spectral S divergence all remain synchronized.
These are conditional necessary consequences of hypothetical nonextension,
not independently established nonlinear PDE estimates.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- The baseline-free spectral shortfall cannot exceed the square-root H³
commutator term: the subtracted full normalized dissipation is nonnegative. -/
theorem h3PathCanonical_sqrtEnergy_gt_of_spectralShortfall
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (M t : ℝ)
    (hShort : M < h3PathCanonicalNonlinearDissipationShortfall u t) :
    M < 4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient *
      Real.sqrt (velocityH3EnergyAt u t) := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hDNonneg : 0 ≤ velocityH3DissipationAt u t :=
    velocityH3DissipationAt_nonneg u t
  have hNormalizedD :
      0 ≤ 2 * velocityH3DissipationAt u t / velocityH3EnergyAt u t :=
    div_nonneg (mul_nonneg (by norm_num) hDNonneg) hEPos.le
  unfold h3PathCanonicalNonlinearDissipationShortfall at hShort
  linarith only [hShort, hNormalizedD]

/-- A quantitative spectral shortfall above a nonnegative threshold forces
a quadratic lower bound on the *physical* canonical H³ energy. -/
theorem h3PathCanonical_energySquareLower_of_spectralShortfall
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (M t : ℝ)
    (hM : 0 ≤ M)
    (hShort : M < h3PathCanonicalNonlinearDissipationShortfall u t) :
    M ^ 2 <
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2 *
        velocityH3EnergyAt u t := by
  let K : ℝ := 4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hKPos : 0 < K := by
    dsimp only [K]
    exact mul_pos (by norm_num) h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos
  have hSqrtPos : 0 < Real.sqrt (velocityH3EnergyAt u t) :=
    Real.sqrt_pos.2 hEPos
  have hRoot : M < K * Real.sqrt (velocityH3EnergyAt u t) :=
    h3PathCanonical_sqrtEnergy_gt_of_spectralShortfall u M t hShort
  have hKRootPos : 0 < K * Real.sqrt (velocityH3EnergyAt u t) :=
    mul_pos hKPos hSqrtPos
  have hAddPos : 0 < K * Real.sqrt (velocityH3EnergyAt u t) + M := by
    linarith only [hKRootPos, hM]
  have hProd :
      0 < (K * Real.sqrt (velocityH3EnergyAt u t) - M) *
        (K * Real.sqrt (velocityH3EnergyAt u t) + M) :=
    mul_pos (sub_pos.2 hRoot) hAddPos
  have hSq :
      M ^ 2 < (K * Real.sqrt (velocityH3EnergyAt u t)) ^ 2 := by
    nlinarith only [hProd]
  calc
    M ^ 2 < (K * Real.sqrt (velocityH3EnergyAt u t)) ^ 2 := hSq
    _ = K ^ 2 * velocityH3EnergyAt u t := by
      rw [mul_pow, Real.sq_sqrt hEPos.le]

/-- Positive exact full-dissipation excess above a nonnegative threshold
forces the *physical* H³ energy derivative above that threshold times energy. -/
theorem h3PathCanonical_energyDerivative_gt_of_actualExcess
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hM : 0 ≤ M)
    (hActual : M < h3PathCanonicalMarginExcessRate u 0 t) :
    M * velocityH3EnergyAt u t < deriv (velocityH3EnergyAt u) t := by
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hFull : M < h3PathFullDissipationTransportExcessRate u t := by
    simpa only [h3PathCanonicalMarginExcessRate,
      h3PathFullDissipationTransportExcessRate, sub_zero] using hActual
  rw [h3PathFullDissipationTransportExcessRate_eq_positiveEnergyGrowthRate
    hH3 hClass ht] at hFull
  unfold h3PathPositiveEnergyGrowthRate at hFull
  have hRatio :
      M < deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t := by
    by_cases hNonneg :
        0 ≤ deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t
    · simpa only [max_eq_right hNonneg] using hFull
    · have hNonpos :
          deriv (velocityH3EnergyAt u) t / velocityH3EnergyAt u t ≤ 0 :=
        le_of_not_ge hNonneg
      rw [max_eq_left hNonpos] at hFull
      linarith only [hFull, hM]
  exact (lt_div_iff₀ hEPos).1 hRatio

/-- Under hypothetical nonextension, on every later direct-selected interval
one time simultaneously has a physical square-root energy lower bound and
an unnormalized H³ energy-derivative lower bound. -/
theorem h3PathCanonical_direct_physicalEnergySlope_witness
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b d : ℝ} (M : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b)
    (hd : d ∈ Set.Ioo a T)
    (hM : 0 ≤ M) :
    ∃ t : ℝ, t ∈ Set.Ioo d T ∧
      h3ExactAdaptiveSelectedDirectCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t =
          h3PathCanonicalKineticTransportCoefficient u t ∧
      h3ExactAdaptiveSelectedAbsorbedCoefficient u
        (h3PathCanonicalKineticTransportCoefficient u) b t = 0 ∧
      M < h3PathCanonicalMarginExcessRate u 0 t ∧
      M < h3PathCanonicalNonlinearDissipationShortfall u t ∧
      M ^ 2 <
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2 *
          velocityH3EnergyAt u t ∧
      M * velocityH3EnergyAt u t < deriv (velocityH3EnergyAt u) t := by
  obtain ⟨t, ht, hDirect, hAbsorbed, hActual, hSpectral⟩ :=
    h3PathCanonical_actualAndSpectralExcess_simultaneously_large_in_directRegime
      M hH3 hNoExtension hClass hMass hd
  have htClass : t ∈ Set.Ioo a T :=
    ⟨lt_trans hd.1 ht.1, ht.2⟩
  have hEnergy :=
    h3PathCanonical_energySquareLower_of_spectralShortfall u M t hM hSpectral
  have hSlope :=
    h3PathCanonical_energyDerivative_gt_of_actualExcess
      hH3 hClass htClass hM hActual
  exact ⟨t, ht, hDirect, hAbsorbed, hActual, hSpectral, hEnergy, hSlope⟩

/-- The *same* compact cancellation-share subsequence carries quadratic
physical energy and linear-times-energy derivative lower bounds. In particular
this does not require saturation of the commutator bound. -/
theorem h3PathCanonical_exists_direct_physicalEnergySlope_cluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < velocityH3Energy0At u b) :
    ∃ σ : ℕ → ℝ, ∃ k : ℕ → ℕ, ∃ θ : ℝ,
      StrictMono k ∧ θ ∈ Set.Icc (0 : ℝ) 1 ∧
      Tendsto (fun n : ℕ => σ (k n)) atTop (𝓝 T) ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalMarginExcessRate u 0 (σ (k n))) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalNonlinearDissipationShortfall u (σ (k n))) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3PathCanonicalCancellationBudgetShare u (σ (k n))) atTop (𝓝 θ) ∧
      (∀ n : ℕ,
        σ (k n) ∈ Set.Ioo a T ∧
        h3ExactAdaptiveSelectedDirectCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ (k n)) =
            h3PathCanonicalKineticTransportCoefficient u (σ (k n)) ∧
        h3ExactAdaptiveSelectedAbsorbedCoefficient u
          (h3PathCanonicalKineticTransportCoefficient u) b (σ (k n)) = 0 ∧
        ((k n : ℕ) : ℝ) ^ 2 <
          (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2 *
            velocityH3EnergyAt u (σ (k n)) ∧
        ((k n : ℕ) : ℝ) * velocityH3EnergyAt u (σ (k n)) <
          deriv (velocityH3EnergyAt u) (σ (k n))) := by
  obtain ⟨σ, k, θ, hkMono, hθ, hSamples, hClock, hActualTop,
    hSpectralTop, hShareTop, _hGrowthTop⟩ :=
    h3PathCanonical_exists_direct_cancellationShare_cluster
      hH3 hNoExtension hClass hMass
  refine ⟨σ, k, θ, hkMono, hθ, hClock, hActualTop,
    hSpectralTop, hShareTop, ?_⟩
  intro n
  obtain ⟨ht, _hNear, hDirect, hAbsorbed, hActual, hSpectral,
    _hCancel⟩ := hSamples (k n)
  have hIndexNonneg : (0 : ℝ) ≤ ((k n : ℕ) : ℝ) := by positivity
  have hEnergy := h3PathCanonical_energySquareLower_of_spectralShortfall
    u ((k n : ℕ) : ℝ) (σ (k n)) hIndexNonneg hSpectral
  have hSlope := h3PathCanonical_energyDerivative_gt_of_actualExcess
    hH3 hClass ht hIndexNonneg hActual
  exact ⟨ht, hDirect, hAbsorbed, hEnergy, hSlope⟩

/-- Neutral terminal alternative: continuation or the common direct-selected
physical clock has simultaneously superquadratic indexed energy and large
positive physical H³-energy derivatives, even after share-cluster extraction. -/
theorem h3PathCanonical_extension_or_direct_physicalEnergySlope_cluster
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ b : ℝ, 0 < velocityH3Energy0At u b →
      ∃ σ : ℕ → ℝ, ∃ k : ℕ → ℕ, ∃ θ : ℝ,
        StrictMono k ∧ θ ∈ Set.Icc (0 : ℝ) 1 ∧
        Tendsto (fun n : ℕ => σ (k n)) atTop (𝓝 T) ∧
        Tendsto (fun n : ℕ =>
          h3PathCanonicalCancellationBudgetShare u (σ (k n))) atTop (𝓝 θ) ∧
        (∀ n : ℕ,
          h3ExactAdaptiveSelectedDirectCoefficient u
            (h3PathCanonicalKineticTransportCoefficient u) b (σ (k n)) =
              h3PathCanonicalKineticTransportCoefficient u (σ (k n)) ∧
          ((k n : ℕ) : ℝ) ^ 2 <
            (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 2 *
              velocityH3EnergyAt u (σ (k n)) ∧
          ((k n : ℕ) : ℝ) * velocityH3EnergyAt u (σ (k n)) <
            deriv (velocityH3EnergyAt u) (σ (k n))) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro b hMass
    obtain ⟨σ, k, θ, hkMono, hθ, hClock, _hActualTop,
      _hSpectralTop, hShareTop, hSamples⟩ :=
      h3PathCanonical_exists_direct_physicalEnergySlope_cluster
        hH3 hExt hClass hMass
    refine ⟨σ, k, θ, hkMono, hθ, hClock, hShareTop, ?_⟩
    intro n
    obtain ⟨_ht, hDirect, _hAbsorbed, hEnergy, hSlope⟩ := hSamples n
    exact ⟨hDirect, hEnergy, hSlope⟩

end Euclidean
end Bridge
end PrimeTensor
