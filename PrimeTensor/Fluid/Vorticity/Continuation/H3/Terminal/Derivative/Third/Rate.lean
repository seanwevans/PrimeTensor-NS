import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Riccati.LowerBound

/-!
# Pointwise terminal rate in the top H³ derivative block

`Terminal.Derivative.Third` proves the fixed-time endpoint inequality

    E_H3(t) ≤ 1 + 3 (E₀(t) + E₃(t)),

and also proves that a hypothetical nonextendible path has a sequence tending
to the terminal time along which `E₃ -> +∞`.

The Riccati lower-bound module gives more:

    2 ≤ K (T - t) sqrt(E_H3(t))

at every strict H³ energy-class time of a nonextendible path.

The zeroth-order kinetic energy is antitone on the energy-class tail.  Thus,
after fixing one later anchor `b`, every `t ∈ (b,T)` satisfies

    E₀(t) ≤ E₀(b).

Combining these facts yields the pointwise top-order terminal rate

    2
      ≤
    K (T - t)
      sqrt(1 + 3 (E₀(b) + E₃(t))).

This is stronger than the previously extracted blowup sequence: the top-order
sector must remain large enough at every sufficiently late time to support the
Riccati-scale lower growth of the full H³ energy.

The result is still conditional on nonextension and does not assert existence
of a singular path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/--
On every later tail `(b,T)`, a hypothetical nonextendible H³ path satisfies
the Riccati terminal lower rate with the full H³ energy replaced by the fixed
kinetic anchor plus the third-order energy.
-/
theorem two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrt_one_add_three_energy0Anchor_add_energy3_of_noH3PathExtension
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
    2
      ≤
    h3PathSqrtEnergyRiccatiCoefficient
      *
    (T - t)
      *
    Real.sqrt
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

  have htTail :
      t ∈ Set.Ioo a T :=
    ⟨
      lt_trans hb.1 ht.1,
      ht.2
    ⟩

  have hRate :
      2
        ≤
      h3PathSqrtEnergyRiccatiCoefficient
        *
      (T - t)
        *
      Real.sqrt (velocityH3EnergyAt u t) :=
    two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrtEnergy_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      htTail

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

  have hEndpoint :
      velocityH3EnergyAt u t
        ≤
      1
        +
      3 *
        (
          velocityH3Energy0At u t
            +
          velocityH3Energy3At u t
        ) :=
    velocityH3EnergyAt_le_one_add_three_mul_energy0_add_energy3_on_h3Path
      hH3
      hClass
      htTail

  have hEndpointAnchor :
      velocityH3EnergyAt u t
        ≤
      1
        +
      3 *
        (
          velocityH3Energy0At u b
            +
          velocityH3Energy3At u t
        ) := by
    linarith

  have hSqrt :
      Real.sqrt (velocityH3EnergyAt u t)
        ≤
      Real.sqrt
        (
          1
            +
          3 *
            (
              velocityH3Energy0At u b
                +
              velocityH3Energy3At u t
            )
        ) :=
    Real.sqrt_le_sqrt hEndpointAnchor

  have hKNonneg :
      0 ≤ h3PathSqrtEnergyRiccatiCoefficient :=
    h3PathSqrtEnergyRiccatiCoefficient_nonneg

  have hDistanceNonneg :
      0 ≤ T - t := by
    linarith [ht.2]

  have hFactorNonneg :
      0
        ≤
      h3PathSqrtEnergyRiccatiCoefficient
        *
      (T - t) :=
    mul_nonneg
      hKNonneg
      hDistanceNonneg

  have hScaled :
      h3PathSqrtEnergyRiccatiCoefficient
          *
        (T - t)
          *
        Real.sqrt (velocityH3EnergyAt u t)
        ≤
      h3PathSqrtEnergyRiccatiCoefficient
          *
        (T - t)
          *
        Real.sqrt
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

    exact
      mul_le_mul_of_nonneg_left
        hSqrt
        hFactorNonneg

  exact
    le_trans
      hRate
      hScaled

/--
Canonical midpoint specialization.  This is the form intended for terminal
arguments: the kinetic anchor is fixed once for the energy-class tail.
-/
theorem two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrt_midpointEnergy0_add_energy3_of_noH3PathExtension
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
          T) :
    2
      ≤
    h3PathSqrtEnergyRiccatiCoefficient
      *
    (T - t)
      *
    Real.sqrt
      (
        1
          +
        3 *
          (
            velocityH3Energy0At
                u
                (h3BKMKineticTailMidpoint a T)
              +
            velocityH3Energy3At u t
          )
      ) := by

  exact
    two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrt_one_add_three_energy0Anchor_add_energy3_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)
      ht

end

end Euclidean
end Bridge
end PrimeTensor
