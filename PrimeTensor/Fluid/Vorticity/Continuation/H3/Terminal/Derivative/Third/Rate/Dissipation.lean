import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Polynomial
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Diffusion.Interpolation.Fourier.MomentCauchy

/-!
# Conditional terminal rate for the top H³ dissipation block

The terminal third-order rate gives, under the nonextension hypothesis and
the existing late-time kinetic-anchor condition,

    1 ≤ 3 K² (T - t)² E₃(t).

The Fourier interpolation theorem gives

    E₃(t)⁴ ≤ E₀(t) D₃(t)³.

Since the zeroth-order kinetic energy is antitone on the H³ energy-class tail,

    E₀(t) ≤ E₀(b)    for b < t < T.

Raising the first inequality to the fourth power and combining these facts
therefore yields the fully polynomial, division-free condition

    1 ≤ 81 K⁸ (T - t)⁸ E₀(b) D₃(t)³.

This identifies the conditional inverse-8/3 scale of the top dissipation
without taking cube roots or dividing by quantities that may vanish.

As with the preceding terminal-rate results, this theorem is only a necessary
consequence of hypothetical nonextension.  It neither asserts that a singular
path exists nor rules one out.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/--
Under hypothetical nonextension, once the fixed kinetic-anchor contribution
is in the late-time regime used by the third-order terminal estimate, the top
H³ dissipation satisfies the division-free terminal condition

    1 ≤ 81 K⁸ (T - t)⁸ E₀(b) D₃(t)³.
-/
theorem one_le_eightyOne_mul_riccatiCoefficient_pow_eight_mul_terminalDistance_pow_eight_mul_energy0Anchor_mul_dissipation3_pow_three_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T)
    (hLate :
      h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        (T - t) ^ 2
          *
        (1 + 3 * velocityH3Energy0At u b)
        ≤
      3) :
    1
      ≤
    81
      *
    h3PathSqrtEnergyRiccatiCoefficient ^ 8
      *
    (T - t) ^ 8
      *
    velocityH3Energy0At u b
      *
    velocityH3Dissipation3At u t ^ 3 := by

  have htTail :
      t ∈ Set.Ioo a T :=
    ⟨
      lt_trans hb.1 ht.1,
      ht.2
    ⟩

  have hRate :
      1
        ≤
      3
        *
      h3PathSqrtEnergyRiccatiCoefficient ^ 2
        *
      (T - t) ^ 2
        *
      velocityH3Energy3At u t :=
    one_le_three_riccatiCoefficient_sq_mul_terminalDistance_sq_mul_energy3_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb
      ht
      hLate

  let A : ℝ :=
    3
      *
    h3PathSqrtEnergyRiccatiCoefficient ^ 2
      *
    (T - t) ^ 2
      *
    velocityH3Energy3At u t

  have hA :
      1 ≤ A := by
    simpa only [A] using hRate

  have hA0 :
      0 ≤ A :=
    le_trans zero_le_one hA

  have hA2raw :
      (1 : ℝ) * 1
        ≤
      A * A :=
    mul_le_mul
      hA
      hA
      (by norm_num)
      hA0

  have hA2 :
      1 ≤ A * A := by
    simpa using hA2raw

  have hA2nonneg :
      0 ≤ A * A :=
    mul_nonneg hA0 hA0

  have hA4raw :
      (1 : ℝ) * 1
        ≤
      (A * A) * (A * A) :=
    mul_le_mul
      hA2
      hA2
      (by norm_num)
      hA2nonneg

  have hA4 :
      1 ≤ A ^ 4 := by
    calc
      1 = (1 : ℝ) * 1 := by norm_num
      _ ≤ (A * A) * (A * A) := hA4raw
      _ = A ^ 4 := by ring

  let C : ℝ :=
    81
      *
    h3PathSqrtEnergyRiccatiCoefficient ^ 8
      *
    (T - t) ^ 8

  have hExpanded :
      1
        ≤
      C * velocityH3Energy3At u t ^ 4 := by

    calc
      1 ≤ A ^ 4 := hA4
      _ =
        C * velocityH3Energy3At u t ^ 4 := by
          dsimp only [A, C]
          ring

  have hC :
      0 ≤ C := by
    dsimp only [C]
    positivity

  have hInterpolation :
      velocityH3Energy3At u t ^ 4
        ≤
      velocityH3Energy0At u t
        *
      velocityH3Dissipation3At u t ^ 3 :=
    velocityH3Energy3At_pow_four_le_energy0_mul_dissipation3_pow_three
      hH3
      hClass
      htTail

  have hScaledInterpolation :
      C * velocityH3Energy3At u t ^ 4
        ≤
      C
        *
      (
        velocityH3Energy0At u t
          *
        velocityH3Dissipation3At u t ^ 3
      ) :=
    mul_le_mul_of_nonneg_left
      hInterpolation
      hC

  have hKineticAnti :
      AntitoneOn
        (velocityH3Energy0At u)
        (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3
      hClass

  have hKinetic :
      velocityH3Energy0At u t
        ≤
      velocityH3Energy0At u b :=
    hKineticAnti
      hb
      htTail
      (le_of_lt ht.1)

  have hDissipationNonneg :
      0 ≤ velocityH3Dissipation3At u t :=
    velocityH3Dissipation3At_nonneg
      u t

  have hDissipationCubeNonneg :
      0 ≤ velocityH3Dissipation3At u t ^ 3 :=
    pow_nonneg
      hDissipationNonneg
      3

  have hAnchor :
      velocityH3Energy0At u t
          *
        velocityH3Dissipation3At u t ^ 3
        ≤
      velocityH3Energy0At u b
          *
        velocityH3Dissipation3At u t ^ 3 :=
    mul_le_mul_of_nonneg_right
      hKinetic
      hDissipationCubeNonneg

  have hScaledAnchor :
      C
          *
        (
          velocityH3Energy0At u t
            *
          velocityH3Dissipation3At u t ^ 3
        )
        ≤
      C
          *
        (
          velocityH3Energy0At u b
            *
          velocityH3Dissipation3At u t ^ 3
        ) :=
    mul_le_mul_of_nonneg_left
      hAnchor
      hC

  calc
    1
        ≤
      C * velocityH3Energy3At u t ^ 4 :=
      hExpanded

    _ ≤
      C
        *
      (
        velocityH3Energy0At u t
          *
        velocityH3Dissipation3At u t ^ 3
      ) :=
      hScaledInterpolation

    _ ≤
      C
        *
      (
        velocityH3Energy0At u b
          *
        velocityH3Dissipation3At u t ^ 3
      ) :=
      hScaledAnchor

    _ =
      81
        *
      h3PathSqrtEnergyRiccatiCoefficient ^ 8
        *
      (T - t) ^ 8
        *
      velocityH3Energy0At u b
        *
      velocityH3Dissipation3At u t ^ 3 := by
      dsimp only [C]
      ring

/--
Canonical midpoint specialization of the conditional top-dissipation terminal
rate.
-/
theorem one_le_eightyOne_mul_riccatiCoefficient_pow_eight_mul_terminalDistance_pow_eight_mul_midpointEnergy0_mul_dissipation3_pow_three_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht :
      t ∈
        Set.Ioo
          (h3BKMKineticTailMidpoint a T)
          T)
    (hLate :
      h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        (T - t) ^ 2
          *
        (
          1
            +
          3
            *
          velocityH3Energy0At
            u
            (h3BKMKineticTailMidpoint a T)
        )
        ≤
      3) :
    1
      ≤
    81
      *
    h3PathSqrtEnergyRiccatiCoefficient ^ 8
      *
    (T - t) ^ 8
      *
    velocityH3Energy0At
        u
        (h3BKMKineticTailMidpoint a T)
      *
    velocityH3Dissipation3At u t ^ 3 := by

  exact
    one_le_eightyOne_mul_riccatiCoefficient_pow_eight_mul_terminalDistance_pow_eight_mul_energy0Anchor_mul_dissipation3_pow_three_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)
      ht
      hLate

end

end Euclidean
end Bridge
end PrimeTensor
