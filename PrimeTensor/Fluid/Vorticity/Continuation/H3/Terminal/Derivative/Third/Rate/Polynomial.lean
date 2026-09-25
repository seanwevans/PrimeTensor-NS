import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate

/-!
# Polynomial form of the pointwise terminal third-order H³ rate

`Terminal.Derivative.Third.Rate` proves, on every sufficiently late strict
H³ energy-class time of a hypothetical nonextendible path,

    2 ≤ K (T - t) sqrt(1 + 3 (E₀(b) + E₃(t))).

The square root obscures the algebraic scale needed by the next coercive
frontier.  This file squares that inequality and isolates the genuine
third-order contribution:

    4 ≤ K² (T - t)² (1 + 3 (E₀(b) + E₃(t)))

and hence

    4 - K² (T - t)² (1 + 3 E₀(b))
      ≤ 3 K² (T - t)² E₃(t).

In particular, whenever the fixed lower-order anchor contributes at most `3`,

    1 ≤ 3 K² (T - t)² E₃(t).

This exposes the inverse-square terminal scale of the top-order block without
introducing division.  It is still only a necessary consequence of the
nonextension hypothesis; no singular path is asserted to exist.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Squared polynomial form of the pointwise terminal third-order rate. -/
theorem four_le_riccatiCoefficient_sq_mul_terminalDistance_sq_mul_one_add_three_energy0Anchor_add_energy3_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    4
      ≤
    h3PathSqrtEnergyRiccatiCoefficient ^ 2
      *
    (T - t) ^ 2
      *
    (
      1
        +
      3 *
        (
          velocityH3Energy0At u b
            +
          velocityH3Energy3At u t
        )
    ) := by

  let X : ℝ :=
    1
      +
    3 *
      (
        velocityH3Energy0At u b
          +
        velocityH3Energy3At u t
      )

  have hRate :
      2
        ≤
      h3PathSqrtEnergyRiccatiCoefficient
        *
      (T - t)
        *
      Real.sqrt X := by
    dsimp only [X]
    exact
      two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrt_one_add_three_energy0Anchor_add_energy3_of_noH3PathExtension
        hH3
        hNoExtension
        hClass
        hb
        ht

  have hXNonneg :
      0 ≤ X := by
    dsimp only [X]
    have h0 := velocityH3Energy0At_nonneg u b
    have h3 := velocityH3Energy3At_nonneg u t
    nlinarith

  have hSqrtSq :
      (Real.sqrt X) ^ 2 = X :=
    Real.sq_sqrt hXNonneg

  let P : ℝ :=
    h3PathSqrtEnergyRiccatiCoefficient
      *
    (T - t)
      *
    Real.sqrt X

  have hP :
      2 ≤ P := by
    simpa only [P] using hRate

  have hSquare :
      4 ≤ P ^ 2 := by
    nlinarith [sq_nonneg P]

  calc
    4 ≤ P ^ 2 := hSquare
    _ =
      h3PathSqrtEnergyRiccatiCoefficient ^ 2
        *
      (T - t) ^ 2
        *
      (Real.sqrt X) ^ 2 := by
        dsimp only [P]
        ring
    _ =
      h3PathSqrtEnergyRiccatiCoefficient ^ 2
        *
      (T - t) ^ 2
        *
      X := by
        rw [hSqrtSq]
    _ =
      h3PathSqrtEnergyRiccatiCoefficient ^ 2
        *
      (T - t) ^ 2
        *
      (
        1
          +
        3 *
          (
            velocityH3Energy0At u b
              +
            velocityH3Energy3At u t
          )
      ) := by
        rfl

/-- The same terminal rate with the fixed kinetic anchor separated from the
third-order term. -/
theorem four_sub_kineticAnchorTerm_le_three_riccatiCoefficient_sq_mul_terminalDistance_sq_mul_energy3_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T) :
    4
        -
      h3PathSqrtEnergyRiccatiCoefficient ^ 2
        *
      (T - t) ^ 2
        *
      (1 + 3 * velocityH3Energy0At u b)
      ≤
    3
      *
    h3PathSqrtEnergyRiccatiCoefficient ^ 2
      *
    (T - t) ^ 2
      *
    velocityH3Energy3At u t := by

  have hRate :=
    four_le_riccatiCoefficient_sq_mul_terminalDistance_sq_mul_one_add_three_energy0Anchor_add_energy3_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb
      ht

  nlinarith

/-- Once the fixed kinetic-anchor contribution has fallen below `3`, the
third-order block alone carries a uniform inverse-square terminal rate in a
division-free form. -/
theorem one_le_three_riccatiCoefficient_sq_mul_terminalDistance_sq_mul_energy3_of_noH3PathExtension
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
    3
      *
    h3PathSqrtEnergyRiccatiCoefficient ^ 2
      *
    (T - t) ^ 2
      *
    velocityH3Energy3At u t := by

  have hIsolated :=
    four_sub_kineticAnchorTerm_le_three_riccatiCoefficient_sq_mul_terminalDistance_sq_mul_energy3_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb
      ht

  linarith

end

end Euclidean
end Bridge
end PrimeTensor
