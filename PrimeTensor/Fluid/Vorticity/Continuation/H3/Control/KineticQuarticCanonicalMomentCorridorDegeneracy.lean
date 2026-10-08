import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.KineticQuarticCanonicalMomentCorridor
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Full.Energy.Normalized.Cascade

/-!
# The anchored cubic moment corridor becomes automatic at high H3 energy

The previous module proved that high unabsorbed growth must satisfy

    8 E₃(t)^4 < (E₀(b)+1) B_M(t)^3,

where `B_M = A sqrt(E) E - M E` and `A = 4422*C1 > 0`.
This new module examines whether the *reverse* inequality can follow from
Fourier interpolation. At `M = 0`, the exact algebraic identity is

    B_0(t)^3 = A^3 sqrt(E(t)) E(t)^4.

Since `0 <= E₃(t) <= E(t)` and `E₀(b) >= 0`, the strict corridor is AUTOMATIC
whenever `8 < A^3 sqrt(E(t))`, regardless of dissipation. The reverse
moment barrier from the previous module is consequently impossible at
all such times.

On a hypothetical nonextendible H3 path, E(t) tends to infinity on the
entire left terminal neighborhood. The strict zero-threshold corridor
therefore holds eventually at every physical time, not only on selected
high-growth witnesses. This proves that the reverse zero-threshold
moment condition is not a viable general high-energy closure mechanism.

No unconditional continuation or singularity existence is inferred.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped Topology

/-- The zero-threshold cubic budget grows like `E^(9/2)` rather than `E^4`.
The equality is an exact algebraic consequence of `sqrt(E)^2 = E`. -/
theorem h3PathCanonical_zeroCubicBudget_cube_eq_energyFactor
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) (t : ℝ) :
    (h3PathCanonicalCubicDissipationBudget u 0 t) ^ 3 =
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
        Real.sqrt (velocityH3EnergyAt u t) * velocityH3EnergyAt u t ^ 4 := by
  have hE : 0 ≤ velocityH3EnergyAt u t :=
    le_trans zero_le_one (one_le_velocityH3EnergyAt u t)
  have hSqrtCube :
      Real.sqrt (velocityH3EnergyAt u t) ^ 3 =
        Real.sqrt (velocityH3EnergyAt u t) * velocityH3EnergyAt u t := by
    calc
      _ = Real.sqrt (velocityH3EnergyAt u t) *
            Real.sqrt (velocityH3EnergyAt u t) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hE]
  unfold h3PathCanonicalCubicDissipationBudget
  simp only [zero_mul, sub_zero]
  calc
    (((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) *
        Real.sqrt (velocityH3EnergyAt u t)) * velocityH3EnergyAt u t) ^ 3 =
        (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
          Real.sqrt (velocityH3EnergyAt u t) ^ 3 *
            velocityH3EnergyAt u t ^ 3 := by ring
    _ = (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
        Real.sqrt (velocityH3EnergyAt u t) * velocityH3EnergyAt u t ^ 4 := by
      rw [hSqrtCube]
      ring

/-- An exact negative result about the *reverse* moment barrier:
when `A^3 sqrt(E)>8`, the strict zero-threshold moment corridor is true
for elementary energy-order reasons alone, independently of the Navier--Stokes
energy balance, the magnitude of viscous dissipation, or nonextension. -/
theorem h3PathCanonical_zeroMomentCorridor_automatic_of_highEnergy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b t : ℝ)
    (hLarge : 8 <
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
        Real.sqrt (velocityH3EnergyAt u t)) :
    8 * velocityH3Energy3At u t ^ 4 <
      (velocityH3Energy0At u b + 1) *
        (h3PathCanonicalCubicDissipationBudget u 0 t) ^ 3 := by
  have hTop : velocityH3Energy3At u t ≤ velocityH3EnergyAt u t :=
    velocityH3Energy3At_le_velocityH3EnergyAt u t
  have hTopNonneg : 0 ≤ velocityH3Energy3At u t :=
    velocityH3Energy3At_nonneg u t
  have hTopPower : velocityH3Energy3At u t ^ 4 ≤
      velocityH3EnergyAt u t ^ 4 :=
    pow_le_pow_left₀ hTopNonneg hTop 4
  have hEPos : 0 < velocityH3EnergyAt u t :=
    lt_of_lt_of_le zero_lt_one (one_le_velocityH3EnergyAt u t)
  have hMass : 1 ≤ velocityH3Energy0At u b + 1 := by
    have h0 : 0 ≤ velocityH3Energy0At u b :=
      velocityH3Energy0At_nonneg u b
    linarith only [h0]
  have hCoeffNonneg : 0 ≤
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
        Real.sqrt (velocityH3EnergyAt u t) := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 8) (le_of_lt hLarge)
  have hMassScaled :
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
          Real.sqrt (velocityH3EnergyAt u t) ≤
        (velocityH3Energy0At u b + 1) *
          ((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
            Real.sqrt (velocityH3EnergyAt u t)) := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hMass hCoeffNonneg)
  have hMassLarge : 8 <
      (velocityH3Energy0At u b + 1) *
        ((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
          Real.sqrt (velocityH3EnergyAt u t)) :=
    lt_of_lt_of_le hLarge hMassScaled
  have hScaled := mul_lt_mul_of_pos_right hMassLarge (pow_pos hEPos 4)
  calc
    8 * velocityH3Energy3At u t ^ 4 ≤
        8 * velocityH3EnergyAt u t ^ 4 :=
      mul_le_mul_of_nonneg_left hTopPower (by norm_num)
    _ < ((velocityH3Energy0At u b + 1) *
          ((4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
            Real.sqrt (velocityH3EnergyAt u t))) *
          velocityH3EnergyAt u t ^ 4 := hScaled
    _ = (velocityH3Energy0At u b + 1) *
          (h3PathCanonicalCubicDissipationBudget u 0 t) ^ 3 := by
      rw [h3PathCanonical_zeroCubicBudget_cube_eq_energyFactor]
      ring

/-- The reverse zero-threshold moment barrier from the preceding module is
impossible whenever the H3 energy is large enough. No PDE assumptions. -/
theorem h3PathCanonical_zeroMomentBarrier_impossible_of_highEnergy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b t : ℝ)
    (hLarge : 8 <
      (4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient) ^ 3 *
        Real.sqrt (velocityH3EnergyAt u t)) :
    ¬ ((velocityH3Energy0At u b + 1) *
          (h3PathCanonicalCubicDissipationBudget u 0 t) ^ 3 ≤
        8 * velocityH3Energy3At u t ^ 4) := by
  exact not_le_of_gt
    (h3PathCanonical_zeroMomentCorridor_automatic_of_highEnergy u b t hLarge)

/-- Under hypothetical nonextension the zero-threshold Fourier corridor is
*eventually automatic at every left-terminal time*. This does not select a
high-growth instant: no transport or dissipation information is used after
the existing full-tail H3 energy divergence theorem. -/
theorem h3PathCanonical_zeroMomentCorridor_eventually_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      t ∈ Set.Ioo b T ∧
        8 * velocityH3Energy3At u t ^ 4 <
          (velocityH3Energy0At u b + 1) *
            (h3PathCanonicalCubicDissipationBudget u 0 t) ^ 3 := by
  let A : ℝ := 4422 * h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (by norm_num)
      h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_pos
  have hA3 : 0 < A ^ 3 := pow_pos hA 3
  let R : ℝ := 8 / A ^ 3 + 1
  have hRNonneg : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hEnergyTendsto :=
    velocityH3EnergyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass
  have hHighEnergy : ∀ᶠ t : ℝ in 𝓝[<] T,
      R ^ 2 ≤ velocityH3EnergyAt u t :=
    (tendsto_atTop.1 hEnergyTendsto) (R ^ 2)
  have hTail : Set.Ioo b T ∈ 𝓝[<] T := Ioo_mem_nhdsLT hb.2
  filter_upwards [hHighEnergy, hTail] with t hEnergy ht
  have hRoot : R ≤ Real.sqrt (velocityH3EnergyAt u t) := by
    calc
      R = Real.sqrt (R ^ 2) := (Real.sqrt_sq hRNonneg).symm
      _ ≤ Real.sqrt (velocityH3EnergyAt u t) := Real.sqrt_le_sqrt hEnergy
  have hScaled := mul_le_mul_of_nonneg_left hRoot hA3.le
  have hBase : A ^ 3 * R = 8 + A ^ 3 := by
    dsimp only [R]
    field_simp [ne_of_gt hA3]
    <;> ring
  have hLarge : 8 < A ^ 3 * Real.sqrt (velocityH3EnergyAt u t) := by
    linarith only [hScaled, hBase, hA3]
  refine ⟨ht, ?_⟩
  exact h3PathCanonical_zeroMomentCorridor_automatic_of_highEnergy
    u b t (by simpa only [A] using hLarge)

/-- On the same hypothetical nonextension branch, the reverse weak moment
barrier is eventually false at *every* physical time on the terminal tail.
Thus this barrier cannot be deduced from interpolation at high energy. -/
theorem h3PathCanonical_zeroMomentBarrier_eventually_impossible_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension : ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∀ᶠ t : ℝ in 𝓝[<] T,
      ¬ ((velocityH3Energy0At u b + 1) *
            (h3PathCanonicalCubicDissipationBudget u 0 t) ^ 3 ≤
          8 * velocityH3Energy3At u t ^ 4) := by
  have hCorridor :=
    h3PathCanonical_zeroMomentCorridor_eventually_of_noExtension
      hH3 hNoExtension hClass hb
  filter_upwards [hCorridor] with t ht
  exact not_le_of_gt ht.2

end Euclidean
end Bridge
end PrimeTensor
