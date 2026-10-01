import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Energy.Clock.Top.Order.Physical.Clock

/-!
# Top-order frequency and dissipation clocks on the physical-energy sequence

The physical-energy-clock sequence from the preceding file already satisfies

`(T - σ n) * E₃(σ n) -> +∞`

on exactly the same terminal times that carry the full physical energy clock.
The Fourier moment interpolation inequality

`E₃(t)^4 ≤ E₀(t) * D₃(t)^3`

together with the tail bound on `E₀` then forces

`D₃(σ n) / E₃(σ n) -> +∞`.

Since both factors are eventually nonnegative and `E₃` is eventually positive,
we can multiply the two asymptotic statements without changing sequence:

`(T - σ n) * D₃(σ n) -> +∞`.

Thus the same physical-energy-clock witness carries an intrinsic top-order
frequency cascade and a divergent top-order physical dissipation clock.
These remain necessary consequences conditional on hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- On the same divergent physical-energy-clock sequence, top-order
dissipation grows without bound relative to top-order energy, and its physical
terminal clock also diverges. -/
theorem exists_h3EnergyPhysicalClock_with_topFrequencyDissipationClockSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ σ : ℕ → ℝ, ∃ C : ℝ,
      0 ≤ C ∧
      (∀ n : ℕ,
        σ n ∈ Set.Ioo a T ∧
        σ n ∈ Set.Ioo
          (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
        (n : ℝ) <
          (T - σ n) * velocityH3EnergyAt u (σ n) ∧
        (n : ℝ) * ((n : ℝ) + 1) <
          velocityH3EnergyAt u (σ n)) ∧
      Tendsto σ atTop (𝓝 T) ∧
      (∀ᶠ n : ℕ in atTop,
        ((n : ℝ) + 1) ^ 2 ≤
          3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2 *
            velocityH3Energy3At u (σ n)) ∧
      (∀ᶠ n : ℕ in atTop,
        ((n : ℝ) - C) / 3 <
          (T - σ n) * velocityH3Energy3At u (σ n)) ∧
      Tendsto
        (fun n : ℕ =>
          (T - σ n) * velocityH3Energy3At u (σ n))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          velocityH3Dissipation3At u (σ n) /
            velocityH3Energy3At u (σ n))
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          (T - σ n) * velocityH3Dissipation3At u (σ n))
        atTop atTop := by
  obtain
    ⟨
      σ,
      C,
      hCNonneg,
      hσ,
      hSigmaTendsto,
      hIndexedE3,
      hPhysicalE3Rate,
      hPhysicalE3Top
    ⟩ :=
    exists_h3EnergyPhysicalClock_with_energy3PhysicalClockDivergenceSequence_of_noH3PathExtension
      hH3 hNoExtension hClass

  let b : ℝ := h3BKMKineticTailMidpoint a T

  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  have hKineticAnti :
      AntitoneOn
        (velocityH3Energy0At u)
        (Set.Ioo a T) :=
    antitoneOn_velocityH3Energy0At_of_h3Path_derivativeIdentities
      h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed
      hH3
      hClass

  have hSigmaAboveB :
      ∀ᶠ n : ℕ in atTop, b < σ n :=
    (tendsto_order.1 hSigmaTendsto).1 b hb.2

  let A : ℝ := 3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2

  have hAPos : 0 < A := by
    dsimp only [A]
    exact
      mul_pos
        (by norm_num : (0 : ℝ) < 3)
        (pow_pos h3PathSqrtEnergyRiccatiCoefficient_pos 2)

  have hE3Top :
      Tendsto
        (fun n : ℕ => velocityH3Energy3At u (σ n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M

    by_cases hM : M ≤ 0
    · filter_upwards [] with n
      exact
        le_trans
          hM
          (velocityH3Energy3At_nonneg u (σ n))

    · have hMPos : 0 < M := lt_of_not_ge hM
      obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (A * M)

      filter_upwards
        [hIndexedE3, eventually_ge_atTop N]
        with n hRateN hn

      have hCast : (N : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hn

      have hAMltN : A * M < (n : ℝ) :=
        lt_of_lt_of_le hN hCast

      have hnNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n

      have hnLeSq :
          (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
        nlinarith [sq_nonneg (n : ℝ)]

      have hAMltSq :
          A * M < ((n : ℝ) + 1) ^ 2 :=
        lt_of_lt_of_le hAMltN hnLeSq

      have hAME3 :
          A * M < A * velocityH3Energy3At u (σ n) :=
        lt_of_lt_of_le
          hAMltSq
          (by simpa only [A] using hRateN)

      exact
        le_of_lt
          (lt_of_mul_lt_mul_left hAME3 (le_of_lt hAPos))

  have hD3RatioTop :
      Tendsto
        (fun n : ℕ =>
          velocityH3Dissipation3At u (σ n) /
            velocityH3Energy3At u (σ n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M

    by_cases hM : M ≤ 0
    · filter_upwards [] with n

      have hD3 :
          0 ≤ velocityH3Dissipation3At u (σ n) :=
        velocityH3Dissipation3At_nonneg u (σ n)

      have hE3 :
          0 ≤ velocityH3Energy3At u (σ n) :=
        velocityH3Energy3At_nonneg u (σ n)

      exact
        le_trans
          hM
          (div_nonneg hD3 hE3)

    · have hMPos : 0 < M := lt_of_not_ge hM

      let Q : ℝ :=
        (velocityH3Energy0At u b + 1) * M ^ 3

      have hQPos : 0 < Q := by
        have hE0 : 0 ≤ velocityH3Energy0At u b :=
          velocityH3Energy0At_nonneg u b
        dsimp only [Q]
        positivity

      have hE3Large :
          ∀ᶠ n : ℕ in atTop,
            Q < velocityH3Energy3At u (σ n) :=
        hE3Top.eventually
          (eventually_gt_atTop Q)

      filter_upwards
        [hE3Large, hSigmaAboveB]
        with n hLarge hbn

      have hClassN : σ n ∈ Set.Ioo a T :=
        (hσ n).1

      have hE0Bound :
          velocityH3Energy0At u (σ n) ≤
            velocityH3Energy0At u b :=
        hKineticAnti
          hb
          hClassN
          (le_of_lt hbn)

      have hInterpolation :=
        velocityH3Energy3At_pow_four_le_energy0_mul_dissipation3_pow_three
          hH3
          hClass
          hClassN

      have hE3Nonneg :
          0 ≤ velocityH3Energy3At u (σ n) :=
        velocityH3Energy3At_nonneg u (σ n)

      have hE3Pos :
          0 < velocityH3Energy3At u (σ n) :=
        lt_trans hQPos hLarge

      have hD3Nonneg :
          0 ≤ velocityH3Dissipation3At u (σ n) :=
        velocityH3Dissipation3At_nonneg u (σ n)

      have hE0PlusPos :
          0 < velocityH3Energy0At u b + 1 := by
        have hE0 : 0 ≤ velocityH3Energy0At u b :=
          velocityH3Energy0At_nonneg u b
        linarith

      have hD3CubeNonneg :
          0 ≤ velocityH3Dissipation3At u (σ n) ^ 3 :=
        pow_nonneg hD3Nonneg 3

      have hInterpolationAnchor :
          velocityH3Energy3At u (σ n) ^ 4 ≤
            (velocityH3Energy0At u b + 1) *
              velocityH3Dissipation3At u (σ n) ^ 3 := by
        calc
          velocityH3Energy3At u (σ n) ^ 4 ≤
              velocityH3Energy0At u (σ n) *
                velocityH3Dissipation3At u (σ n) ^ 3 :=
            hInterpolation
          _ ≤
              velocityH3Energy0At u b *
                velocityH3Dissipation3At u (σ n) ^ 3 :=
            mul_le_mul_of_nonneg_right
              hE0Bound
              hD3CubeNonneg
          _ ≤
              (velocityH3Energy0At u b + 1) *
                velocityH3Dissipation3At u (σ n) ^ 3 := by
            apply
              mul_le_mul_of_nonneg_right
                ?_
                hD3CubeNonneg
            linarith

      have hThreshold :
          (velocityH3Energy0At u b + 1) * M ^ 3 <
            velocityH3Energy3At u (σ n) := by
        simpa only [Q] using hLarge

      have hE3CubePos :
          0 < velocityH3Energy3At u (σ n) ^ 3 := by
        positivity

      have hThresholdScaled :
          ((velocityH3Energy0At u b + 1) * M ^ 3) *
              velocityH3Energy3At u (σ n) ^ 3 <
            velocityH3Energy3At u (σ n) *
              velocityH3Energy3At u (σ n) ^ 3 :=
        mul_lt_mul_of_pos_right
          hThreshold
          hE3CubePos

      have hLeftRearranged :
          (velocityH3Energy0At u b + 1) *
              (M * velocityH3Energy3At u (σ n)) ^ 3 <
            velocityH3Energy3At u (σ n) ^ 4 := by
        calc
          (velocityH3Energy0At u b + 1) *
              (M * velocityH3Energy3At u (σ n)) ^ 3 =
            ((velocityH3Energy0At u b + 1) * M ^ 3) *
              velocityH3Energy3At u (σ n) ^ 3 := by
                ring
          _ <
              velocityH3Energy3At u (σ n) *
                velocityH3Energy3At u (σ n) ^ 3 :=
            hThresholdScaled
          _ = velocityH3Energy3At u (σ n) ^ 4 := by
            ring

      have hWeightedCube :
          (velocityH3Energy0At u b + 1) *
              (M * velocityH3Energy3At u (σ n)) ^ 3 <
            (velocityH3Energy0At u b + 1) *
              velocityH3Dissipation3At u (σ n) ^ 3 :=
        lt_of_lt_of_le
          hLeftRearranged
          hInterpolationAnchor

      have hCube :
          (M * velocityH3Energy3At u (σ n)) ^ 3 <
            velocityH3Dissipation3At u (σ n) ^ 3 :=
        lt_of_mul_lt_mul_left
          hWeightedCube
          (le_of_lt hE0PlusPos)

      have hLinear :
          M * velocityH3Energy3At u (σ n) <
            velocityH3Dissipation3At u (σ n) :=
        lt_of_pow_lt_pow_left₀
          3
          hD3Nonneg
          hCube

      exact
        le_of_lt
          ((lt_div_iff₀ hE3Pos).2 hLinear)

  have hPhysicalD3Top :
      Tendsto
        (fun n : ℕ =>
          (T - σ n) * velocityH3Dissipation3At u (σ n))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M

    by_cases hM : M ≤ 0
    · filter_upwards [] with n
      have hGapNonneg : 0 ≤ T - σ n := by
        linarith [(hσ n).1.2]
      have hD3Nonneg :
          0 ≤ velocityH3Dissipation3At u (σ n) :=
        velocityH3Dissipation3At_nonneg u (σ n)
      exact
        le_trans
          hM
          (mul_nonneg hGapNonneg hD3Nonneg)

    · have hMPos : 0 < M := lt_of_not_ge hM

      have hClockLarge :
          ∀ᶠ n : ℕ in atTop,
            M ≤ (T - σ n) * velocityH3Energy3At u (σ n) :=
        hPhysicalE3Top.eventually
          (eventually_ge_atTop M)

      have hRatioOne :
          ∀ᶠ n : ℕ in atTop,
            1 ≤
              velocityH3Dissipation3At u (σ n) /
                velocityH3Energy3At u (σ n) :=
        hD3RatioTop.eventually
          (eventually_ge_atTop 1)

      filter_upwards
        [hClockLarge, hRatioOne]
        with n hClockN hRatioN

      have hGapPos : 0 < T - σ n := by
        linarith [(hσ n).1.2]

      have hE3Nonneg :
          0 ≤ velocityH3Energy3At u (σ n) :=
        velocityH3Energy3At_nonneg u (σ n)

      have hClockPos :
          0 < (T - σ n) * velocityH3Energy3At u (σ n) :=
        lt_of_lt_of_le hMPos hClockN

      have hE3Pos :
          0 < velocityH3Energy3At u (σ n) := by
        rcases (mul_pos_iff.mp hClockPos) with h | h
        · exact h.2
        · exfalso
          linarith [hGapPos, h.1]

      have hClockNonneg :
          0 ≤ (T - σ n) * velocityH3Energy3At u (σ n) :=
        mul_nonneg (le_of_lt hGapPos) hE3Nonneg

      have hScale :
          (T - σ n) * velocityH3Energy3At u (σ n) ≤
            ((T - σ n) * velocityH3Energy3At u (σ n)) *
              (velocityH3Dissipation3At u (σ n) /
                velocityH3Energy3At u (σ n)) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left
            hRatioN
            hClockNonneg

      have hFactor :
          ((T - σ n) * velocityH3Energy3At u (σ n)) *
              (velocityH3Dissipation3At u (σ n) /
                velocityH3Energy3At u (σ n)) =
            (T - σ n) * velocityH3Dissipation3At u (σ n) := by
        field_simp [ne_of_gt hE3Pos]

      exact
        le_trans
          hClockN
          (le_trans hScale (le_of_eq hFactor))

  exact
    ⟨
      σ,
      C,
      hCNonneg,
      hσ,
      hSigmaTendsto,
      hIndexedE3,
      hPhysicalE3Rate,
      hPhysicalE3Top,
      hD3RatioTop,
      hPhysicalD3Top
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
