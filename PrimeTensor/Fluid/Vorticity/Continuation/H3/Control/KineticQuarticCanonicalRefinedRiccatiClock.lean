import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalRiccatiDefect

/-!
# Asymptotically refined intrinsic H3 terminal Riccati clock

The previous exact Riccati defect isolates the baseline `4422` and proves,
under hypothetical nonextension, an entire late tail with

  E'(t) ≤ (4422 C1 + η) sqrt(E(t)) E(t)

for every η>0.  This module carries that improvement through the existing
inverse-square-root terminal argument.  The resulting physical-clock floor

  2 ≤ (4422 C1 + η) (T-t) sqrt(E(t))

holds at **every** sufficiently late strict energy-class time.  The terminal
tail depends on η.  No claim is made that η can be set to zero at a fixed
preterminal time, or that the hypothesis of nonextension occurs.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- A pointwise Riccati-scale growth estimate with an arbitrary scalar
coefficient gives the corresponding lower derivative bound for inverse-root
energy.  This exports the derivative conversion implicit in the original
intrinsic Riccati proof. -/
theorem h3PathCanonical_refinedInverseSqrt_deriv_lower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t c : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T)
    (hGrowth : deriv (velocityH3EnergyAt u) t ≤
      c * Real.sqrt (velocityH3EnergyAt u t) *
        velocityH3EnergyAt u t) :
    -(c / 2) ≤ deriv (h3PathInverseSqrtEnergy u) t := by
  have hInv := hasDerivAt_h3PathInverseSqrtEnergy hH3 hClass ht
  rw [hInv.deriv]
  let E : ℝ := velocityH3EnergyAt u t
  let z : ℝ := Real.sqrt E
  have hEPos : 0 < E := by
    dsimp only [E]
    exact lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hzPos : 0 < z := by
    dsimp only [z]
    exact Real.sqrt_pos.2 hEPos
  have hGrowthCubic : deriv (velocityH3EnergyAt u) t ≤ c * z ^ 3 := by
    calc
      _ ≤ c * z * E := by simpa only [z, E] using hGrowth
      _ = c * z ^ 3 := by
        rw [← Real.sq_sqrt hEPos.le]
        dsimp only [z]
        ring
  have hDen : 0 < 2 * z ^ 3 := by positivity
  have hDiv : deriv (velocityH3EnergyAt u) t / (2 * z ^ 3) ≤ c / 2 := by
    apply (div_le_iff₀ hDen).2
    calc
      _ ≤ c * z ^ 3 := hGrowthCubic
      _ = (c / 2) * (2 * z ^ 3) := by ring
  have hNormalize :
      -(deriv (velocityH3EnergyAt u) t / (2 * z)) / z ^ 2 =
        -(deriv (velocityH3EnergyAt u) t / (2 * z ^ 3)) := by
    field_simp [ne_of_gt hzPos]
    <;> ring
  change -(c / 2) ≤
    -(deriv (velocityH3EnergyAt u) t / (2 * z)) / z ^ 2
  rw [hNormalize]
  exact neg_le_neg hDiv

/-- The inverse-root energy shifted by an arbitrary Riccati coefficient. -/
noncomputable def h3PathCanonicalRefinedInverseSqrtShift
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (c : ℝ) : ℝ → ℝ :=
  fun t => h3PathInverseSqrtEnergy u t + (c / 2) * t

/-- Uniform Riccati growth control on a strict tail makes the generalized
inverse-root shift monotone on that tail. -/
theorem h3PathCanonical_refinedInverseSqrtShift_monotone
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a c : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hGrowth : ∀ t : ℝ, t ∈ Set.Ioo a T →
      deriv (velocityH3EnergyAt u) t ≤
        c * Real.sqrt (velocityH3EnergyAt u t) *
          velocityH3EnergyAt u t) :
    MonotoneOn (h3PathCanonicalRefinedInverseSqrtShift u c)
      (Set.Ioo a T) := by
  have hDiff : DifferentiableOn ℝ
      (h3PathCanonicalRefinedInverseSqrtShift u c) (Set.Ioo a T) := by
    intro t ht
    have hInv := hasDerivAt_h3PathInverseSqrtEnergy hH3 hClass ht
    have hLinear : HasDerivAt (fun s : ℝ => (c / 2) * s) (c / 2) t := by
      simpa using (hasDerivAt_id t).const_mul (c / 2)
    change DifferentiableWithinAt ℝ
      (h3PathInverseSqrtEnergy u + fun s : ℝ => (c / 2) * s)
      (Set.Ioo a T) t
    exact (hInv.add hLinear).differentiableAt.differentiableWithinAt
  refine monotoneOn_of_deriv_nonneg
    (convex_Ioo a T) hDiff.continuousOn
    (hDiff.mono interior_subset) ?_
  intro t htInterior
  have ht : t ∈ Set.Ioo a T := interior_subset htInterior
  have hInv := hasDerivAt_h3PathInverseSqrtEnergy hH3 hClass ht
  have hLinear : HasDerivAt (fun s : ℝ => (c / 2) * s) (c / 2) t := by
    simpa using (hasDerivAt_id t).const_mul (c / 2)
  have hShift : deriv (h3PathCanonicalRefinedInverseSqrtShift u c) t =
      deriv (h3PathInverseSqrtEnergy u) t + c / 2 := by
    have hSum := hInv.add hLinear
    rw [show deriv (h3PathCanonicalRefinedInverseSqrtShift u c) t =
      -(deriv (velocityH3EnergyAt u) t /
        (2 * Real.sqrt (velocityH3EnergyAt u t))) /
        (Real.sqrt (velocityH3EnergyAt u t)) ^ 2 + c / 2 from by
          exact hSum.deriv]
    rw [hInv.deriv]
  rw [hShift]
  have hBound := h3PathCanonical_refinedInverseSqrt_deriv_lower
    hH3 hClass ht (hGrowth t ht)
  linarith only [hBound]

/-- Terminal comparison for any constant Riccati coefficient controlling a
full strict energy-class tail.  Hypothetical nonextension supplies the
terminal energy-divergence sequence, not an assumption on a chosen sample. -/
theorem h3PathCanonical_inverseSqrt_terminalUpper_of_refinedGrowth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a c t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hGrowth : ∀ s : ℝ, s ∈ Set.Ioo a T →
      deriv (velocityH3EnergyAt u) s ≤
        c * Real.sqrt (velocityH3EnergyAt u s) *
          velocityH3EnergyAt u s)
    (ht : t ∈ Set.Ioo a T) :
    h3PathInverseSqrtEnergy u t ≤ (c / 2) * (T - t) := by
  obtain ⟨τ, hτ, hτTop, hEnergyTop⟩ :=
    exists_velocityH3EnergyAt_blowupSequence_of_noH3PathExtension
      hH3 hNoExtension
  have hMono := h3PathCanonical_refinedInverseSqrtShift_monotone
    hH3 hClass hGrowth
  have hAbove : ∀ᶠ n : ℕ in atTop, t < τ n :=
    (tendsto_order.1 hτTop).1 t ht.2
  have hCompare : ∀ᶠ n : ℕ in atTop,
      h3PathCanonicalRefinedInverseSqrtShift u c t ≤
        h3PathCanonicalRefinedInverseSqrtShift u c (τ n) := by
    filter_upwards [hAbove] with n hn
    have hτMem : τ n ∈ Set.Ioo a T :=
      ⟨lt_trans ht.1 hn, (hτ n).1.2⟩
    exact hMono ht hτMem hn.le
  have hSqrtTop : Tendsto (fun n : ℕ =>
      Real.sqrt (velocityH3EnergyAt u (τ n))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hEnergyTop
  have hInvZero : Tendsto (fun n : ℕ =>
      (Real.sqrt (velocityH3EnergyAt u (τ n)))⁻¹) atTop (𝓝 0) :=
    hSqrtTop.inv_tendsto_atTop
  have hLinearTop : Tendsto (fun n : ℕ => (c / 2) * τ n)
      atTop (𝓝 ((c / 2) * T)) :=
    tendsto_const_nhds.mul hτTop
  have hShiftTop : Tendsto (fun n : ℕ =>
      h3PathCanonicalRefinedInverseSqrtShift u c (τ n))
      atTop (𝓝 ((c / 2) * T)) := by
    have hSum := hInvZero.add hLinearTop
    simpa only [h3PathCanonicalRefinedInverseSqrtShift,
      h3PathInverseSqrtEnergy, zero_add] using hSum
  have hBound : h3PathCanonicalRefinedInverseSqrtShift u c t ≤
      (c / 2) * T := ge_of_tendsto hShiftTop hCompare
  unfold h3PathCanonicalRefinedInverseSqrtShift at hBound
  linarith only [hBound]

/-- The original `4422*(C1+1)` clock improves to an arbitrary coefficient
`4422*C1+η` on a sufficiently late **entire** terminal tail. -/
theorem h3PathCanonical_eventual_refinedIntrinsicInverseSqrtFloor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (η : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hη : 0 < η) :
    ∃ d : ℝ, d ∈ Set.Ioo a T ∧
      ∀ t : ℝ, t ∈ Set.Ioo d T →
        h3PathInverseSqrtEnergy u t ≤
          ((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient + η) / 2) *
            (T - t) := by
  obtain ⟨d, hd, hGrowth⟩ :=
    h3PathCanonical_eventual_refinedRiccatiGrowth_of_noExtension
      hH3 hNoExtension hClass hη
  have hClassD : PreterminalH3EnergyClass u d T :=
    preterminalH3EnergyClass_restrict_left hClass (le_of_lt hd.1) hd.2
  refine ⟨d, hd, ?_⟩
  intro t ht
  exact h3PathCanonical_inverseSqrt_terminalUpper_of_refinedGrowth
    hH3 hNoExtension hClassD hGrowth ht

/-- Sharpened intrinsic terminal Riccati lower bound with arbitrary positive
tolerance on the *leading* coefficient.  All late physical times are covered. -/
theorem h3PathCanonical_eventual_refinedIntrinsicRiccatiFloor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (η : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hη : 0 < η) :
    ∃ d : ℝ, d ∈ Set.Ioo a T ∧
      ∀ t : ℝ, t ∈ Set.Ioo d T →
        (2 : ℝ) ≤
          (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient + η) *
            (T - t) * Real.sqrt (velocityH3EnergyAt u t) := by
  obtain ⟨d, hd, hInv⟩ :=
    h3PathCanonical_eventual_refinedIntrinsicInverseSqrtFloor
      η hH3 hNoExtension hClass hη
  refine ⟨d, hd, ?_⟩
  intro t ht
  have hSqrtPos : 0 < Real.sqrt (velocityH3EnergyAt u t) :=
    Real.sqrt_pos.2
      (lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t))
  have hScaled := mul_le_mul_of_nonneg_right (hInv t ht) hSqrtPos.le
  have hOne : h3PathInverseSqrtEnergy u t *
      Real.sqrt (velocityH3EnergyAt u t) = 1 := by
    unfold h3PathInverseSqrtEnergy
    exact inv_mul_cancel₀ (ne_of_gt hSqrtPos)
  rw [hOne] at hScaled
  have hTwice := mul_le_mul_of_nonneg_left hScaled
    (by norm_num : (0 : ℝ) ≤ 2)
  calc
    (2 : ℝ) = 2 * 1 := by ring
    _ ≤ 2 *
        (((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient + η) / 2) *
          (T - t) * Real.sqrt (velocityH3EnergyAt u t)) := hTwice
    _ = (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient + η) *
          (T - t) * Real.sqrt (velocityH3EnergyAt u t) := by ring

/-- Quadratic physical-time energy floor with the improved asymptotic
coefficient; the bound holds simultaneously at every point of a sufficiently
late tail and is independent of the fast-selected clock. -/
theorem h3PathCanonical_eventual_refinedIntrinsicEnergyFloor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (η : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hη : 0 < η) :
    ∃ d : ℝ, d ∈ Set.Ioo a T ∧
      ∀ t : ℝ, t ∈ Set.Ioo d T →
        (4 : ℝ) ≤
          (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient + η) ^ 2 *
            (T - t) ^ 2 * velocityH3EnergyAt u t := by
  obtain ⟨d, hd, hFloor⟩ :=
    h3PathCanonical_eventual_refinedIntrinsicRiccatiFloor
      η hH3 hNoExtension hClass hη
  refine ⟨d, hd, ?_⟩
  intro t ht
  have hRate := hFloor t ht
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  have hSquare : (4 : ℝ) ≤
      ((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient + η) *
        (T - t) * Real.sqrt (velocityH3EnergyAt u t)) ^ 2 := by
    nlinarith only [hRate,
      sq_nonneg
        ((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient + η) *
          (T - t) * Real.sqrt (velocityH3EnergyAt u t) - 2)]
  calc
    (4 : ℝ) ≤
        ((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient + η) *
          (T - t) * Real.sqrt (velocityH3EnergyAt u t)) ^ 2 := hSquare
    _ = (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient + η) ^ 2 *
          (T - t) ^ 2 * velocityH3EnergyAt u t := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hE]

/-- Contrapositive terminal test: if for a positive tolerance its sharpened
Riccati clock is violated arbitrarily near T, smooth continuation follows. -/
theorem h3PathCanonical_extension_of_recurrent_refinedRiccatiDeficit
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} (η : ℝ)
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hη : 0 < η)
    (hFailure : ∀ d : ℝ, d ∈ Set.Ioo a T →
      ∃ t : ℝ, t ∈ Set.Ioo d T ∧
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient + η) *
          (T - t) * Real.sqrt (velocityH3EnergyAt u t) < 2) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  obtain ⟨d, hd, hFloor⟩ :=
    h3PathCanonical_eventual_refinedIntrinsicRiccatiFloor
      η hH3 hNoExtension hClass hη
  obtain ⟨t, ht, hSmall⟩ := hFailure d hd
  exact (not_lt_of_ge (hFloor t ht)) hSmall

/-- Neutral formulation: extension or the asymptotically refined Riccati
lower bound on an entire η-dependent physical terminal tail, for every η>0. -/
theorem h3PathCanonical_extension_or_eventual_refinedIntrinsicRiccatiFloor
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    ∀ η : ℝ, 0 < η →
      ∃ d : ℝ, d ∈ Set.Ioo a T ∧
        ∀ t : ℝ, t ∈ Set.Ioo d T →
          (2 : ℝ) ≤
            (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient + η) *
              (T - t) * Real.sqrt (velocityH3EnergyAt u t) := by
  by_cases hExt : ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T
  · exact Or.inl hExt
  · right
    intro η hη
    exact h3PathCanonical_eventual_refinedIntrinsicRiccatiFloor
      η hH3 hExt hClass hη

end Euclidean
end Bridge
end PrimeTensor
