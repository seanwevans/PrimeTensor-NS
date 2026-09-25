import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Riccati.LowerBound
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Terminal square-root-energy nonintegrability from the Riccati lower rate

`Terminal.Riccati.LowerBound` proves that a hypothetical nonextendible
preterminal H³ path satisfies, on every strict H³ energy-class time,

    2 ≤ K (T - t) sqrt(E_H3(t)),

with the fixed positive coefficient

    K = h3PathSqrtEnergyRiccatiCoefficient.

This file rewrites that estimate in its natural harmonic form

    1 / (T - t)
      ≤
    (K / 2) sqrt(E_H3(t)).

The terminal harmonic profile is not integrable on any nontrivial interval
ending at `T`.  Therefore `sqrt(E_H3)` cannot be integrable on any H³
energy-class terminal tail of a nonextendible path.

This localizes the previously proved whole-preterminal square-root-energy
pathology exactly at the candidate singular time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Pointwise harmonic form of the terminal Riccati lower bound. -/
theorem one_div_terminalDistance_le_half_riccatiCoefficient_mul_sqrtEnergy_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    1 / (T - t)
      ≤
    (h3PathSqrtEnergyRiccatiCoefficient / 2)
      *
    Real.sqrt (velocityH3EnergyAt u t) := by

  have hRate :=
    two_le_riccatiCoefficient_mul_terminalDistance_mul_sqrtEnergy_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      ht

  have hDist :
      0 < T - t := by
    linarith [ht.2]

  apply
    (div_le_iff₀ hDist).2

  have hHalf :=
    mul_le_mul_of_nonneg_left
      hRate
      (by norm_num : (0 : ℝ) ≤ 1 / 2)

  calc
    1
        =
      (1 / 2 : ℝ) * 2 := by
        norm_num

    _ ≤
      (1 / 2)
        *
      (
        h3PathSqrtEnergyRiccatiCoefficient
          *
        (T - t)
          *
        Real.sqrt (velocityH3EnergyAt u t)
      ) :=
      hHalf

    _ =
      (
        (h3PathSqrtEnergyRiccatiCoefficient / 2)
          *
        Real.sqrt (velocityH3EnergyAt u t)
      )
        *
      (T - t) := by
      ring

/-- The reciprocal terminal-distance profile is not integrable on any
nontrivial open interval ending at `T`. -/
theorem not_integrableOn_one_div_terminalDistance
    {a T : ℝ}
    (haT : a < T) :
    ¬ MeasureTheory.IntegrableOn
        (fun t : ℝ => 1 / (T - t))
        (Set.Ioo a T) := by

  intro hIntegrable

  have hInterval :
      IntervalIntegrable
        (fun t : ℝ => 1 / (T - t))
        MeasureTheory.volume
        a T := by

    exact
      (intervalIntegrable_iff_integrableOn_Ioo_of_le
        (le_of_lt haT)).2
        hIntegrable

  have hSubInv :
      IntervalIntegrable
        (fun t : ℝ => (t - T)⁻¹)
        MeasureTheory.volume
        a T := by

    have hNeg :=
      hInterval.neg

    refine
      hNeg.congr
        ?_

    intro t ht

    simp only [
      Pi.neg_apply,
      one_div
    ]

    rw [
      show T - t = -(t - T) by ring,
      inv_neg,
      neg_neg
    ]

  have hCharacterization :=
    (intervalIntegrable_sub_inv_iff).1
      hSubInv

  rcases hCharacterization with hEq | hNotMem

  · exact
      (ne_of_lt haT)
        hEq

  · apply hNotMem

    rw [Set.uIcc_of_le (le_of_lt haT)]

    exact
      ⟨
        le_of_lt haT,
        le_rfl
      ⟩

/--
A hypothetical nonextendible H³ path has nonintegrable square-root H³ energy
on every terminal tail carrying a `PreterminalH3EnergyClass`.
-/
theorem not_integrableOn_sqrt_velocityH3EnergyAt_on_energyClassTail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ¬ MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          Real.sqrt (velocityH3EnergyAt u t))
        (Set.Ioo a T) := by

  intro hSqrtIntegrable

  have hKNonneg :
      0 ≤ h3PathSqrtEnergyRiccatiCoefficient / 2 := by

    have hK :=
      h3PathSqrtEnergyRiccatiCoefficient_nonneg

    positivity

  have hScaled :
      MeasureTheory.IntegrableOn
        (
          fun t : ℝ =>
            (h3PathSqrtEnergyRiccatiCoefficient / 2)
              *
            Real.sqrt (velocityH3EnergyAt u t)
        )
        (Set.Ioo a T) := by

    change
      MeasureTheory.Integrable
        (
          fun t : ℝ =>
            (h3PathSqrtEnergyRiccatiCoefficient / 2)
              *
            Real.sqrt (velocityH3EnergyAt u t)
        )
        ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo a T))

    exact
      hSqrtIntegrable.const_mul
        (h3PathSqrtEnergyRiccatiCoefficient / 2)

  have hReciprocal :
      MeasureTheory.IntegrableOn
        (fun t : ℝ => 1 / (T - t))
        (Set.Ioo a T) := by

    apply
      Integrable.mono'
        hScaled

    · exact
        (
          show
            Measurable
              (fun t : ℝ => 1 / (T - t))
          by
            fun_prop
        ).aestronglyMeasurable

    · filter_upwards
        [
          ae_restrict_mem
            measurableSet_Ioo
        ]
        with t ht

      have hDist :
          0 < T - t := by
        linarith [ht.2]

      have hBound :=
        one_div_terminalDistance_le_half_riccatiCoefficient_mul_sqrtEnergy_of_noH3PathExtension
          hH3
          hNoExtension
          hClass
          ht

      rw [
        Real.norm_eq_abs,
        abs_of_pos
          (one_div_pos.mpr hDist)
      ]

      exact hBound

  exact
    not_integrableOn_one_div_terminalDistance
      hClass.terminal_start.2
      hReciprocal

end

end Euclidean
end Bridge
end PrimeTensor
