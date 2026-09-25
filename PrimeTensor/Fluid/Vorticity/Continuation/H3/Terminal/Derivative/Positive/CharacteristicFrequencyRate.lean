import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.CharacteristicFrequencyCascade

/-!
# Quantitative terminal rate for the characteristic top-order frequency

The intrinsic characteristic frequency is

    Λ₃(t) = sqrt(D₃(t) / E₃(t)).

On every strict H³ energy-class slice the top-order Fourier interpolation
inequality gives

    E₃(t)^4 ≤ E₀(t) D₃(t)^3.

If `b < t < T`, kinetic antitonicity gives `E₀(t) ≤ E₀(b)`.  Once `E₃(t)` is
strictly positive, division by `E₃(t)^3` therefore yields

    E₃(t)
      ≤
    (E₀(b) + 1) (D₃(t) / E₃(t))^3
      =
    (E₀(b) + 1) Λ₃(t)^6.

Hypothetical nonextension also forces, on a sufficiently late terminal tail,

    1 ≤ 3 K^2 (T-t)^2 E₃(t).

Combining the two estimates gives

    1
      ≤
    3 K^2 (E₀(b)+1) (T-t)^2 Λ₃(t)^6.

Thus the characteristic top-order frequency cannot grow more slowly than the
inverse one-third terminal-distance scale.  The theorem is kept in a
division-free sixth-power form.

This remains a necessary consequence of hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Intrinsic interpolation through the characteristic frequency -/

/--
At a strict tail time with positive third-order energy, Fourier interpolation
and kinetic antitonicity imply

    E₃(t) ≤ (E₀(b)+1) Λ₃(t)^6.
-/
theorem velocityH3Energy3At_le_energy0Anchor_add_one_mul_characteristicFrequency_pow_six
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (ht : t ∈ Set.Ioo b T)
    (hE3Pos : 0 < velocityH3Energy3At u t) :
    velocityH3Energy3At u t
      ≤
    (
      velocityH3Energy0At u b
        +
      1
    )
      *
    h3TopCharacteristicFrequencyAt u t ^ 6 := by

  have htClass :
      t ∈ Set.Ioo a T :=
    ⟨
      lt_trans hb.1 ht.1,
      ht.2
    ⟩

  have hKineticAnti :
      AntitoneOn
        (velocityH3Energy0At u)
        (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3
      hClass

  have hE0Bound :
      velocityH3Energy0At u t
        ≤
      velocityH3Energy0At u b :=
    hKineticAnti
      hb
      htClass
      (le_of_lt ht.1)

  have hInterpolation :=
    velocityH3Energy3At_pow_four_le_energy0_mul_dissipation3_pow_three
      hH3
      hClass
      htClass

  have hD3Nonneg :
      0 ≤ velocityH3Dissipation3At u t :=
    velocityH3Dissipation3At_nonneg
      u t

  have hD3CubeNonneg :
      0 ≤ velocityH3Dissipation3At u t ^ 3 :=
    pow_nonneg
      hD3Nonneg
      3

  have hInterpolationAnchor :
      velocityH3Energy3At u t ^ 4
        ≤
      (
        velocityH3Energy0At u b
          +
        1
      )
        *
      velocityH3Dissipation3At u t ^ 3 := by

    calc
      velocityH3Energy3At u t ^ 4
          ≤
        velocityH3Energy0At u t
          *
        velocityH3Dissipation3At u t ^ 3 :=
        hInterpolation

      _ ≤
        velocityH3Energy0At u b
          *
        velocityH3Dissipation3At u t ^ 3 :=
        mul_le_mul_of_nonneg_right
          hE0Bound
          hD3CubeNonneg

      _ ≤
        (
          velocityH3Energy0At u b
            +
          1
        )
          *
        velocityH3Dissipation3At u t ^ 3 := by

        apply
          mul_le_mul_of_nonneg_right
            ?_
            hD3CubeNonneg

        linarith

  have hE3CubePos :
      0 < velocityH3Energy3At u t ^ 3 :=
    pow_pos
      hE3Pos
      3

  have hRatioBound :
      velocityH3Energy3At u t
        ≤
      (
        velocityH3Energy0At u b
          +
        1
      )
        *
      (
        velocityH3Dissipation3At u t
          /
        velocityH3Energy3At u t
      ) ^ 3 := by

    rw [div_pow]

    have hDivTarget :
        velocityH3Energy3At u t
          ≤
        (
          (
            velocityH3Energy0At u b
              +
            1
          )
            *
          velocityH3Dissipation3At u t ^ 3
        )
          /
        velocityH3Energy3At u t ^ 3 := by

      apply
        (le_div_iff₀ hE3CubePos).2

      calc
        velocityH3Energy3At u t
            *
          velocityH3Energy3At u t ^ 3
            =
          velocityH3Energy3At u t ^ 4 := by
            ring

        _ ≤
          (
            velocityH3Energy0At u b
              +
            1
          )
            *
          velocityH3Dissipation3At u t ^ 3 :=
          hInterpolationAnchor

    simpa only [mul_div_assoc] using
      hDivTarget

  have hFrequencySq :=
    h3TopCharacteristicFrequencyAt_sq
      u t

  calc
    velocityH3Energy3At u t
        ≤
      (
        velocityH3Energy0At u b
          +
        1
      )
        *
      (
        velocityH3Dissipation3At u t
          /
        velocityH3Energy3At u t
      ) ^ 3 :=
      hRatioBound

    _ =
      (
        velocityH3Energy0At u b
          +
        1
      )
        *
      h3TopCharacteristicFrequencyAt u t ^ 6 := by

      rw [← hFrequencySq]

      ring

/-! ## Eventual inverse-one-third terminal frequency rate -/

/--
On a sufficiently late terminal interval, hypothetical nonextension forces

    1 ≤ 3 K² (E₀(b)+1) (T-t)² Λ₃(t)^6.
-/
theorem exists_terminalTail_characteristicFrequency_pow_six_rate_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ∃ c : ℝ,
      c ∈ Set.Ioo b T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        1
          ≤
        3
          *
        h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        (
          velocityH3Energy0At u b
            +
          1
        )
          *
        (T - t) ^ 2
          *
        h3TopCharacteristicFrequencyAt u t ^ 6 := by

  obtain
    ⟨c, hc, hLate⟩ :=
    exists_terminalTail_kineticAnchorTerm_le_three
      u
      T
      b
      hb.2

  refine
    ⟨
      c,
      hc,
      ?_
    ⟩

  intro t ht

  have htAnchor :
      t ∈ Set.Ioo b T :=
    ⟨
      lt_trans hc.1 ht.1,
      ht.2
    ⟩

  have htClass :
      t ∈ Set.Ioo a T :=
    ⟨
      lt_trans hb.1 htAnchor.1,
      htAnchor.2
    ⟩

  have hThirdRate :
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
      htAnchor
      (hLate t ht)

  have hE3Nonneg :
      0 ≤ velocityH3Energy3At u t :=
    velocityH3Energy3At_nonneg
      u t

  have hE3Ne :
      velocityH3Energy3At u t ≠ 0 := by

    intro hZero

    rw [hZero, mul_zero] at hThirdRate

    norm_num at hThirdRate

  have hE3Pos :
      0 < velocityH3Energy3At u t :=
    lt_of_le_of_ne
      hE3Nonneg
      (Ne.symm hE3Ne)

  have hIntrinsic :
      velocityH3Energy3At u t
        ≤
      (
        velocityH3Energy0At u b
          +
        1
      )
        *
      h3TopCharacteristicFrequencyAt u t ^ 6 :=
    velocityH3Energy3At_le_energy0Anchor_add_one_mul_characteristicFrequency_pow_six
      hH3
      hClass
      hb
      htAnchor
      hE3Pos

  have hCoeffNonneg :
      0
        ≤
      3
        *
      h3PathSqrtEnergyRiccatiCoefficient ^ 2
        *
      (T - t) ^ 2 := by
    positivity

  have hScaled :
      3
          *
        h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        (T - t) ^ 2
          *
        velocityH3Energy3At u t
        ≤
      3
          *
        h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        (T - t) ^ 2
          *
        (
          (
            velocityH3Energy0At u b
              +
            1
          )
            *
          h3TopCharacteristicFrequencyAt u t ^ 6
        ) :=
    mul_le_mul_of_nonneg_left
      hIntrinsic
      hCoeffNonneg

  calc
    1
        ≤
      3
        *
      h3PathSqrtEnergyRiccatiCoefficient ^ 2
        *
      (T - t) ^ 2
        *
      velocityH3Energy3At u t :=
      hThirdRate

    _ ≤
      3
        *
      h3PathSqrtEnergyRiccatiCoefficient ^ 2
        *
      (T - t) ^ 2
        *
      (
        (
          velocityH3Energy0At u b
            +
          1
        )
          *
        h3TopCharacteristicFrequencyAt u t ^ 6
      ) :=
      hScaled

    _ =
      3
        *
      h3PathSqrtEnergyRiccatiCoefficient ^ 2
        *
      (
        velocityH3Energy0At u b
          +
        1
      )
        *
      (T - t) ^ 2
        *
      h3TopCharacteristicFrequencyAt u t ^ 6 := by
      ring

/--
Canonical midpoint-anchor specialization of the quantitative characteristic
frequency rate.
-/
theorem exists_terminalTail_characteristicFrequency_pow_six_rate_midpoint_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ c : ℝ,
      c ∈
        Set.Ioo
          (h3BKMKineticTailMidpoint a T)
          T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        1
          ≤
        3
          *
        h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        (
          velocityH3Energy0At
              u
              (h3BKMKineticTailMidpoint a T)
            +
          1
        )
          *
        (T - t) ^ 2
          *
        h3TopCharacteristicFrequencyAt u t ^ 6 := by

  exact
    exists_terminalTail_characteristicFrequency_pow_six_rate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor
