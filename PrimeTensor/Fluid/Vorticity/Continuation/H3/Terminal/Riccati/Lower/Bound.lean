import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Growth.Sqrt
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Sequence.Alternative
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Dynamics.Frontier
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Terminal Riccati lower bound

The closed autonomous H³ estimate gives, on every strict energy-class time,

    E'(t) ≤ K sqrt(E(t)) E(t),

where

    K = h3PathSqrtEnergyRiccatiCoefficient.

The terminal sequence alternative says that a hypothetical nonextendible path
admits `τ n -> T` with `E(τ n) -> +∞`.

The correct variable for combining these facts is

    F(t) = 1 / sqrt(E(t)).

Since `E(t) ≥ 1`, `F` is differentiable and

    F'(t) ≥ -K/2.

Thus

    F(t) + (K/2)t

is monotone on every H³ energy-class tail.  Passing to the terminal blow-up
sequence makes `F(τ n) -> 0`, and yields

    1 / sqrt(E(t)) ≤ (K/2)(T-t).

Equivalently,

    2 ≤ K (T-t) sqrt(E(t)).

Hence any nonextendible admissible H³ path must have at least the Riccati-scale
terminal growth `E(t) ≳ (T-t)^(-2)` on every strict energy-class tail.

This is still a necessary-condition theorem.  It does not assert that a
nonextendible path exists.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Inverse square root of the normalized canonical H³ energy. -/
noncomputable def h3PathInverseSqrtEnergy
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → ℝ :=
  fun t =>
    (Real.sqrt (velocityH3EnergyAt u t))⁻¹

/-- The autonomous Riccati coefficient is in fact strictly positive. -/
theorem h3PathSqrtEnergyRiccatiCoefficient_pos :
    0 < h3PathSqrtEnergyRiccatiCoefficient := by

  unfold h3PathSqrtEnergyRiccatiCoefficient

  have hC :
      0 ≤
        h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCoefficient_nonneg

  nlinarith

/-- Exact derivative of the inverse-square-root energy on a strict H³
energy-class slice. -/
theorem hasDerivAt_h3PathInverseSqrtEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    HasDerivAt
      (h3PathInverseSqrtEnergy u)
      (
        -
          (
            deriv (velocityH3EnergyAt u) t
              /
            (2 * Real.sqrt (velocityH3EnergyAt u t))
          )
          /
        (Real.sqrt (velocityH3EnergyAt u t)) ^ 2
      )
      t := by

  have hDifferentiable :
      HasDerivAt
        (velocityH3EnergyAt u)
        (deriv (velocityH3EnergyAt u) t)
        t :=
    h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_orderEnergyDerivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      u T hH3
      a hClass
      t ht

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hEPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  have hENe :
      velocityH3EnergyAt u t ≠ 0 :=
    ne_of_gt hEPos

  have hSqrtPos :
      0 < Real.sqrt (velocityH3EnergyAt u t) :=
    Real.sqrt_pos.2 hEPos

  have hSqrtNe :
      Real.sqrt (velocityH3EnergyAt u t) ≠ 0 :=
    ne_of_gt hSqrtPos

  have hRaw :=
    (hDifferentiable.sqrt hENe).inv hSqrtNe

  change
    HasDerivAt
      ((fun y : ℝ =>
        Real.sqrt (velocityH3EnergyAt u y))⁻¹)
      (
        -
          (
            deriv (velocityH3EnergyAt u) t
              /
            (2 * Real.sqrt (velocityH3EnergyAt u t))
          )
          /
        (Real.sqrt (velocityH3EnergyAt u t)) ^ 2
      )
      t

  exact hRaw

/-- Differential form of the Riccati estimate after the
inverse-square-root change of variables. -/
theorem neg_half_riccatiCoefficient_le_deriv_h3PathInverseSqrtEnergy
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    -
        (
          h3PathSqrtEnergyRiccatiCoefficient / 2
        )
      ≤
    deriv (h3PathInverseSqrtEnergy u) t := by

  have hInv :=
    hasDerivAt_h3PathInverseSqrtEnergy
      hH3 hClass ht

  rw [hInv.deriv]

  let E : ℝ :=
    velocityH3EnergyAt u t

  let z : ℝ :=
    Real.sqrt E

  let K : ℝ :=
    h3PathSqrtEnergyRiccatiCoefficient

  have hEOne :
      1 ≤ E := by
    dsimp only [E]
    exact one_le_velocityH3EnergyAt u t

  have hENonneg :
      0 ≤ E := by
    linarith

  have hEPos :
      0 < E := by
    linarith

  have hzPos :
      0 < z := by
    dsimp only [z]
    exact Real.sqrt_pos.2 hEPos

  have hGrowth :
      deriv (velocityH3EnergyAt u) t
        ≤
      K * z ^ 3 := by

    have hRaw :=
      deriv_velocityH3EnergyAt_le_sqrtEnergy_mul_energy
        hH3 hClass ht

    calc
      deriv (velocityH3EnergyAt u) t
          ≤
        K * z * E := by
          simpa only [K, z, E] using hRaw

      _ =
        K * z ^ 3 := by
          rw [← Real.sq_sqrt hENonneg]
          dsimp only [z]
          ring

  have hDen :
      0 < 2 * z ^ 3 := by
    positivity

  have hDiv :
      deriv (velocityH3EnergyAt u) t
          /
        (2 * z ^ 3)
        ≤
      K / 2 := by

    apply
      (div_le_iff₀ hDen).2

    calc
      deriv (velocityH3EnergyAt u) t
          ≤
        K * z ^ 3 :=
        hGrowth

      _ =
        (K / 2) * (2 * z ^ 3) := by
        ring

  have hNormalize :
      -
          (
            deriv (velocityH3EnergyAt u) t
              /
            (2 * z)
          )
          /
        z ^ 2
        =
      -
        (
          deriv (velocityH3EnergyAt u) t
            /
          (2 * z ^ 3)
        ) := by

    field_simp [ne_of_gt hzPos]
    <;> ring

  change
    -(K / 2)
      ≤
    -
        (
          deriv (velocityH3EnergyAt u) t
            /
          (2 * z)
        )
        /
      z ^ 2

  rw [hNormalize]

  exact neg_le_neg hDiv

/-- Riccati-shifted inverse-square-root energy. -/
noncomputable def h3PathInverseSqrtEnergyRiccatiShift
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three) :
    ℝ → ℝ :=
  fun t =>
    h3PathInverseSqrtEnergy u t
      +
    (h3PathSqrtEnergyRiccatiCoefficient / 2) * t

/-- The shifted inverse-square-root energy is monotone on every H³
energy-class tail. -/
theorem monotoneOn_h3PathInverseSqrtEnergyRiccatiShift
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    MonotoneOn
      (h3PathInverseSqrtEnergyRiccatiShift u)
      (Set.Ioo a T) := by

  have hDifferentiable :
      DifferentiableOn ℝ
        (h3PathInverseSqrtEnergyRiccatiShift u)
        (Set.Ioo a T) := by

    intro t ht

    have hInv :=
      hasDerivAt_h3PathInverseSqrtEnergy
        hH3 hClass ht

    have hLinear :
        HasDerivAt
          (
            fun s : ℝ =>
              (h3PathSqrtEnergyRiccatiCoefficient / 2) * s
          )
          (h3PathSqrtEnergyRiccatiCoefficient / 2)
          t := by

      simpa using
        (hasDerivAt_id t).const_mul
          (h3PathSqrtEnergyRiccatiCoefficient / 2)

    have hSum :=
      hInv.add hLinear

    change
      DifferentiableWithinAt ℝ
        (
          h3PathInverseSqrtEnergy u
            +
          fun s : ℝ =>
            (h3PathSqrtEnergyRiccatiCoefficient / 2) * s
        )
        (Set.Ioo a T)
        t

    exact
      hSum.differentiableAt.differentiableWithinAt

  refine
    monotoneOn_of_deriv_nonneg
      (convex_Ioo a T)
      hDifferentiable.continuousOn
      (hDifferentiable.mono interior_subset)
      ?_

  intro t htInterior

  have ht :
      t ∈ Set.Ioo a T :=
    interior_subset htInterior

  have hInv :=
    hasDerivAt_h3PathInverseSqrtEnergy
      hH3 hClass ht

  have hLinear :
      HasDerivAt
        (
          fun s : ℝ =>
            (h3PathSqrtEnergyRiccatiCoefficient / 2) * s
        )
        (h3PathSqrtEnergyRiccatiCoefficient / 2)
        t := by

    simpa using
      (hasDerivAt_id t).const_mul
        (h3PathSqrtEnergyRiccatiCoefficient / 2)

  have hShiftHas :
      HasDerivAt
        (h3PathInverseSqrtEnergyRiccatiShift u)
        (
          -
              (
                deriv (velocityH3EnergyAt u) t
                  /
                (2 * Real.sqrt (velocityH3EnergyAt u t))
              )
              /
            (Real.sqrt (velocityH3EnergyAt u t)) ^ 2
            +
          h3PathSqrtEnergyRiccatiCoefficient / 2
        )
        t := by

    change
      HasDerivAt
        (
          fun s : ℝ =>
            h3PathInverseSqrtEnergy u s
              +
            (h3PathSqrtEnergyRiccatiCoefficient / 2) * s
        )
        (
          -
              (
                deriv (velocityH3EnergyAt u) t
                  /
                (2 * Real.sqrt (velocityH3EnergyAt u t))
              )
              /
            (Real.sqrt (velocityH3EnergyAt u t)) ^ 2
            +
          h3PathSqrtEnergyRiccatiCoefficient / 2
        )
        t

    exact
      hInv.add hLinear

  have hShift :
      deriv
          (h3PathInverseSqrtEnergyRiccatiShift u)
          t
        =
      deriv (h3PathInverseSqrtEnergy u) t
        +
      h3PathSqrtEnergyRiccatiCoefficient / 2 := by

    rw [hShiftHas.deriv, hInv.deriv]

  rw [hShift]

  have hLower :=
    neg_half_riccatiCoefficient_le_deriv_h3PathInverseSqrtEnergy
      hH3 hClass ht

  linarith

/--
Riccati lower blow-up rate forced by nonextension.

For every strict time in every H³ energy-class tail,

    2 ≤ K (T-t) sqrt(E_H3(t)).

In particular, a hypothetical nonextendible path cannot approach the terminal
time more slowly than the usual Riccati `E(t) ~ (T-t)^(-2)` scale.
-/
theorem two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrtEnergy_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    2
      ≤
    h3PathSqrtEnergyRiccatiCoefficient
      *
    (T - t)
      *
    Real.sqrt (velocityH3EnergyAt u t) := by

  obtain
    ⟨τ, hτ, hτTendsto, hEnergyTendsto⟩ :=
    exists_velocityH3EnergyAt_blowupSequence_of_noH3PathExtension
      hH3
      hNoExtension

  have hMonotone :
      MonotoneOn
        (h3PathInverseSqrtEnergyRiccatiShift u)
        (Set.Ioo a T) :=
    monotoneOn_h3PathInverseSqrtEnergyRiccatiShift
      hH3 hClass

  have hTauAbove :
      ∀ᶠ n : ℕ in atTop,
        t < τ n :=
    (tendsto_order.1 hτTendsto).1
      t ht.2

  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        h3PathInverseSqrtEnergyRiccatiShift u t
          ≤
        h3PathInverseSqrtEnergyRiccatiShift u (τ n) := by

    filter_upwards [hTauAbove] with n htn

    have hτMem :
        τ n ∈ Set.Ioo a T := by
      exact
        ⟨
          lt_trans ht.1 htn,
          (hτ n).1.2
        ⟩

    exact
      hMonotone
        ht
        hτMem
        (le_of_lt htn)

  have hSqrtTop :
      Tendsto
        (
          fun n : ℕ =>
            Real.sqrt
              (velocityH3EnergyAt u (τ n))
        )
        atTop
        atTop :=
    Real.tendsto_sqrt_atTop.comp
      hEnergyTendsto

  have hInverseZero :
      Tendsto
        (
          fun n : ℕ =>
            (Real.sqrt
              (velocityH3EnergyAt u (τ n)))⁻¹
        )
        atTop
        (𝓝 0) :=
    hSqrtTop.inv_tendsto_atTop

  have hLinearLimit :
      Tendsto
        (
          fun n : ℕ =>
            (h3PathSqrtEnergyRiccatiCoefficient / 2)
              * τ n
        )
        atTop
        (
          𝓝
            (
              (h3PathSqrtEnergyRiccatiCoefficient / 2)
                * T
            )
        ) :=
    tendsto_const_nhds.mul
      hτTendsto

  have hShiftLimit :
      Tendsto
        (
          fun n : ℕ =>
            h3PathInverseSqrtEnergyRiccatiShift u (τ n)
        )
        atTop
        (
          𝓝
            (
              (h3PathSqrtEnergyRiccatiCoefficient / 2)
                * T
            )
        ) := by

    have hSum :=
      hInverseZero.add hLinearLimit

    simpa only [
      h3PathInverseSqrtEnergyRiccatiShift,
      h3PathInverseSqrtEnergy,
      zero_add
    ] using hSum

  have hTerminalBound :
      h3PathInverseSqrtEnergyRiccatiShift u t
        ≤
      (h3PathSqrtEnergyRiccatiCoefficient / 2) * T :=
    ge_of_tendsto
      hShiftLimit
      hEventually

  have hInvBound :
      h3PathInverseSqrtEnergy u t
        ≤
      (h3PathSqrtEnergyRiccatiCoefficient / 2)
        * (T - t) := by

    unfold h3PathInverseSqrtEnergyRiccatiShift at hTerminalBound

    linarith

  have hEOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hEPos :
      0 < velocityH3EnergyAt u t := by
    linarith

  have hSqrtPos :
      0 < Real.sqrt (velocityH3EnergyAt u t) :=
    Real.sqrt_pos.2 hEPos

  have hScaled :=
    mul_le_mul_of_nonneg_right
      hInvBound
      (le_of_lt hSqrtPos)

  have hOne :
      h3PathInverseSqrtEnergy u t
          *
        Real.sqrt (velocityH3EnergyAt u t)
        =
      1 := by

    unfold h3PathInverseSqrtEnergy

    exact
      inv_mul_cancel₀
        (ne_of_gt hSqrtPos)

  rw [hOne] at hScaled

  have hTwice :=
    mul_le_mul_of_nonneg_left
      hScaled
      (by norm_num : (0 : ℝ) ≤ 2)

  calc
    2 = 2 * 1 := by ring
    _ ≤
      2
        *
      (
        (h3PathSqrtEnergyRiccatiCoefficient / 2)
          *
        (T - t)
          *
        Real.sqrt (velocityH3EnergyAt u t)
      ) :=
      hTwice
    _ =
      h3PathSqrtEnergyRiccatiCoefficient
        *
      (T - t)
        *
      Real.sqrt (velocityH3EnergyAt u t) := by
      ring

end

end Euclidean
end Bridge
end PrimeTensor
