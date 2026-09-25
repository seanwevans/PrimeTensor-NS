import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.CharacteristicFrequencyFullLimit

/-!
# Full terminal H³ top-energy and dissipation cascade

The full characteristic-frequency limit already shows, under hypothetical
nonextension,

    Λ₃(t) -> +∞  as t ↑ T.

The third-order terminal polynomial rate gives independently, on a sufficiently
late tail,

    1 ≤ 3 K² (T-t)² E₃(t).

This forces the full one-sided top-energy divergence

    E₃(t) -> +∞  as t ↑ T.

The exact identity

    Λ₃(t)^2 = D₃(t) / E₃(t)

then upgrades the characteristic-frequency limit to

    D₃(t) / E₃(t) -> +∞.

Since `E₃(t)` is eventually at least one, the ratio divergence implies

    D₃(t) -> +∞.

Finally, because `D₃(t) ≤ D(t)` pointwise,

    D(t) / E₃(t) -> +∞
    and
    D(t) -> +∞.

No transport sign is used.  In particular, the adverse-transport ratio remains
a sequence-level statement unless an additional sign condition on the H³
energy derivative is supplied.

Every assertion in this file remains a necessary consequence of hypothetical
nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Full left-terminal divergence of E₃ -/

/--
Hypothetical nonextension forces the top H³ energy block to diverge along the
entire left terminal neighborhood.
-/
theorem velocityH3Energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (velocityH3Energy3At u)
      (𝓝[<] T)
      atTop := by

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hb :
      b ∈ Set.Ioo a T := by

    dsimp only [b]

    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  obtain
    ⟨cRate, hcRate, hLate⟩ :=
    exists_terminalTail_kineticAnchorTerm_le_three
      u
      T
      b
      hb.2

  refine
    tendsto_atTop.2
      ?_

  intro M

  by_cases hM :
      M ≤ 0

  · exact
      Eventually.of_forall
        (
          fun t =>
            le_trans
              hM
              (velocityH3Energy3At_nonneg
                u t)
        )

  · have hMPos :
        0 < M :=
      lt_of_not_ge
        hM

    let B : ℝ :=
      6
        *
      h3PathSqrtEnergyRiccatiCoefficient ^ 2
        *
      M

    obtain
      ⟨cSmall, hcSmall, hSmall⟩ :=
      exists_terminalTail_const_mul_terminalDistance_sq_le_one
        B
        T
        cRate
        hcRate.2

    show
      {t : ℝ |
        M ≤ velocityH3Energy3At u t}
        ∈
      𝓝[<] T

    rw [
      mem_nhdsLT_iff_exists_Ioo_subset
    ]

    refine
      ⟨
        cSmall,
        hcSmall.2,
        ?_
      ⟩

    intro t ht

    have htRate :
        t ∈ Set.Ioo cRate T :=
      ⟨
        lt_trans hcSmall.1 ht.1,
        ht.2
      ⟩

    have htAnchor :
        t ∈ Set.Ioo b T :=
      ⟨
        lt_trans hcRate.1 htRate.1,
        htRate.2
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
        htAnchor
        (hLate t htRate)

    have hSmallT :
        B * (T - t) ^ 2
          ≤
        1 :=
      hSmall
        t
        ht

    have hDistPos :
        0 < T - t := by
      linarith [ht.2]

    by_contra hNot

    have hE3Lt :
        velocityH3Energy3At u t
          <
        M :=
      lt_of_not_ge
        hNot

    have hPrefactorPos :
        0
          <
        3
            *
          h3PathSqrtEnergyRiccatiCoefficient ^ 2
            *
          (T - t) ^ 2 := by

      exact
        mul_pos
          (
            mul_pos
              (by norm_num : (0 : ℝ) < 3)
              (
                pow_pos
                  h3PathSqrtEnergyRiccatiCoefficient_pos
                  2
              )
          )
          (
            pow_pos
              hDistPos
              2
          )

    have hScaledLt :
        3
            *
          h3PathSqrtEnergyRiccatiCoefficient ^ 2
            *
          (T - t) ^ 2
            *
          velocityH3Energy3At u t
          <
        3
            *
          h3PathSqrtEnergyRiccatiCoefficient ^ 2
            *
          (T - t) ^ 2
            *
          M :=
      mul_lt_mul_of_pos_left
        hE3Lt
        hPrefactorPos

    have hOneLt :
        1
          <
        3
            *
          h3PathSqrtEnergyRiccatiCoefficient ^ 2
            *
          (T - t) ^ 2
            *
          M :=
      lt_of_le_of_lt
        hRate
        hScaledLt

    have hDouble :
        2
            *
          (
            3
                *
              h3PathSqrtEnergyRiccatiCoefficient ^ 2
                *
              (T - t) ^ 2
                *
              M
          )
          ≤
        1 := by

      calc
        2
            *
          (
            3
                *
              h3PathSqrtEnergyRiccatiCoefficient ^ 2
                *
              (T - t) ^ 2
                *
              M
          )
            =
          B * (T - t) ^ 2 := by

            dsimp only [B]

            ring

        _ ≤
          1 :=
          hSmallT

    linarith

/-! ## Full left-terminal divergence of D₃/E₃ -/

/--
The exact squared-frequency identity promotes the full characteristic-frequency
limit to divergence of the intrinsic dissipation-to-energy ratio.
-/
theorem velocityH3Dissipation3At_div_energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (
        fun t : ℝ =>
          velocityH3Dissipation3At u t
            /
          velocityH3Energy3At u t
      )
      (𝓝[<] T)
      atTop := by

  have hFrequency :=
    h3TopCharacteristicFrequencyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hPow :
      Tendsto
        (fun x : ℝ => x ^ 2)
        atTop
        atTop :=
    tendsto_pow_atTop
      (by norm_num : (2 : ℕ) ≠ 0)

  have hSquare :
      Tendsto
        (
          fun t : ℝ =>
            h3TopCharacteristicFrequencyAt u t ^ 2
        )
        (𝓝[<] T)
        atTop :=
    hPow.comp
      hFrequency

  have hFunction :
      (
        fun t : ℝ =>
          velocityH3Dissipation3At u t
            /
          velocityH3Energy3At u t
      )
        =
      (
        fun t : ℝ =>
          h3TopCharacteristicFrequencyAt u t ^ 2
      ) := by

    funext t

    exact
      (
        h3TopCharacteristicFrequencyAt_sq
          u t
      ).symm

  rw [hFunction]

  exact
    hSquare

/-! ## Full dissipation ratio -/

/--
Since the top dissipation is bounded above by the full H³ dissipation, the
full dissipation-to-top-energy ratio also diverges along the full terminal
tail.
-/
theorem velocityH3DissipationAt_div_energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (
        fun t : ℝ =>
          velocityH3DissipationAt u t
            /
          velocityH3Energy3At u t
      )
      (𝓝[<] T)
      atTop := by

  have hTopRatio :=
    velocityH3Dissipation3At_div_energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  refine
    tendsto_atTop.2
      ?_

  intro M

  have hEventually :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        M
          ≤
        velocityH3Dissipation3At u t
          /
        velocityH3Energy3At u t :=
    hTopRatio.eventually
      (eventually_ge_atTop M)

  filter_upwards
    [hEventually]
    with t ht

  have hE3 :
      0 ≤ velocityH3Energy3At u t :=
    velocityH3Energy3At_nonneg
      u t

  have hTop :
      velocityH3Dissipation3At u t
        ≤
      velocityH3DissipationAt u t :=
    velocityH3Dissipation3At_le_dissipationAt
      u t

  have hRatio :
      velocityH3Dissipation3At u t
          /
        velocityH3Energy3At u t
        ≤
      velocityH3DissipationAt u t
          /
        velocityH3Energy3At u t :=
    div_le_div_of_nonneg_right
      hTop
      hE3

  exact
    le_trans
      ht
      hRatio

/-! ## Full divergence of D₃ and D -/

/--
The simultaneous full-tail divergence of `E₃` and `D₃/E₃` forces the top H³
dissipation itself to diverge.
-/
theorem velocityH3Dissipation3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (velocityH3Dissipation3At u)
      (𝓝[<] T)
      atTop := by

  have hE3Tendsto :=
    velocityH3Energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  have hRatioTendsto :=
    velocityH3Dissipation3At_div_energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  refine
    tendsto_atTop.2
      ?_

  intro M

  by_cases hM :
      M ≤ 0

  · exact
      Eventually.of_forall
        (
          fun t =>
            le_trans
              hM
              (velocityH3Dissipation3At_nonneg
                u t)
        )

  · have hMPos :
        0 < M :=
      lt_of_not_ge
        hM

    have hRatioEventually :
        ∀ᶠ t : ℝ in 𝓝[<] T,
          M
            ≤
          velocityH3Dissipation3At u t
            /
          velocityH3Energy3At u t :=
      hRatioTendsto.eventually
        (eventually_ge_atTop M)

    have hEnergyEventually :
        ∀ᶠ t : ℝ in 𝓝[<] T,
          1
            ≤
          velocityH3Energy3At u t :=
      hE3Tendsto.eventually
        (eventually_ge_atTop 1)

    filter_upwards
      [
        hRatioEventually,
        hEnergyEventually
      ]
      with t hRatio hEnergy

    have hEnergyPos :
        0 < velocityH3Energy3At u t := by
      linarith

    have hProduct :
        M * velocityH3Energy3At u t
          ≤
        velocityH3Dissipation3At u t :=
      (le_div_iff₀ hEnergyPos).1
        hRatio

    have hMLeProduct :
        M
          ≤
        M * velocityH3Energy3At u t := by

      nlinarith

    exact
      le_trans
        hMLeProduct
        hProduct

/--
The full H³ dissipation also diverges because it dominates the top-order
dissipation pointwise.
-/
theorem velocityH3DissipationAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (velocityH3DissipationAt u)
      (𝓝[<] T)
      atTop := by

  have hTopTendsto :=
    velocityH3Dissipation3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3
      hNoExtension
      hClass

  refine
    tendsto_atTop.2
      ?_

  intro M

  have hEventually :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        M
          ≤
        velocityH3Dissipation3At u t :=
    hTopTendsto.eventually
      (eventually_ge_atTop M)

  filter_upwards
    [hEventually]
    with t ht

  exact
    le_trans
      ht
      (
        velocityH3Dissipation3At_le_dissipationAt
          u t
      )

/-! ## Full intrinsic cascade package -/

/--
Neutral full-tail terminal package.

Either a smooth continuation exists across `T`, or every one of the following
holds along the entire left terminal neighborhood:

* `E₃ -> +∞`;
* `Λ₃ -> +∞`;
* `D₃/E₃ -> +∞`;
* `D/E₃ -> +∞`;
* `D₃ -> +∞`;
* `D -> +∞`;
* `ℓ₃ -> 0`.

No branch is selected a priori.
-/
theorem smoothContinuationExtension_or_full_h3_energy_dissipation_frequency_cascade
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      Tendsto
        (velocityH3Energy3At u)
        (𝓝[<] T)
        atTop
        ∧
      Tendsto
        (h3TopCharacteristicFrequencyAt u)
        (𝓝[<] T)
        atTop
        ∧
      Tendsto
        (
          fun t : ℝ =>
            velocityH3Dissipation3At u t
              /
            velocityH3Energy3At u t
        )
        (𝓝[<] T)
        atTop
        ∧
      Tendsto
        (
          fun t : ℝ =>
            velocityH3DissipationAt u t
              /
            velocityH3Energy3At u t
        )
        (𝓝[<] T)
        atTop
        ∧
      Tendsto
        (velocityH3Dissipation3At u)
        (𝓝[<] T)
        atTop
        ∧
      Tendsto
        (velocityH3DissipationAt u)
        (𝓝[<] T)
        atTop
        ∧
      Tendsto
        (h3TopCharacteristicLengthAt u)
        (𝓝[<] T)
        (𝓝 0)
    ) := by

  classical

  by_cases hExtension :
      ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact
      Or.inl
        hExtension

  · exact
      Or.inr
        ⟨
          velocityH3Energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3
            hExtension
            hClass,
          h3TopCharacteristicFrequencyAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3
            hExtension
            hClass,
          velocityH3Dissipation3At_div_energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3
            hExtension
            hClass,
          velocityH3DissipationAt_div_energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3
            hExtension
            hClass,
          velocityH3Dissipation3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3
            hExtension
            hClass,
          velocityH3DissipationAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3
            hExtension
            hClass,
          h3TopCharacteristicLengthAt_tendsto_zero_nhdsLT_of_noH3PathExtension
            hH3
            hExtension
            hClass
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
