import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeEnergyClockNormalizedBalanceChannelSubsequence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.FullEnergyDissipationCascade

/-!
# Full-tail physical H³ energy and dissipation clocks

The earlier physical-clock construction selected terminal sequences.  The
pointwise third-order Riccati rate is stronger: after fixing the kinetic anchor
and moving sufficiently far into the terminal tail,

`1 ≤ 3 K² (T - t)² E₃(t)`

holds at every time.  Since the coefficient is fixed and `T - t -> 0`, this
forces the physical top-energy clock itself to diverge on the entire left
terminal neighborhood:

`(T - t) E₃(t) -> +∞`.

The full energy dominates `E₃`.  Moreover the already-proved full-tail
frequency cascade gives `D₃/E₃ -> +∞`, hence eventually `E₃ ≤ D₃`; and the
full dissipation dominates `D₃`.  Therefore the corresponding full-energy,
top-dissipation, and full-dissipation physical clocks all diverge on the full
left terminal neighborhood as well.

These remain necessary consequences conditional on hypothetical nonextension.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Hypothetical nonextension forces the third-order H³ physical energy clock
`(T-t) E₃(t)` to tend to `+∞` on the entire left terminal neighborhood. -/
theorem velocityH3Energy3PhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (fun t : ℝ =>
        (T - t) * velocityH3Energy3At u t)
      (𝓝[<] T)
      atTop := by
  let b : ℝ := h3BKMKineticTailMidpoint a T

  have hb : b ∈ Set.Ioo a T := by
    dsimp only [b]
    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  obtain ⟨cRate, hcRate, hLate⟩ :=
    exists_terminalTail_kineticAnchorTerm_le_three
      u T b hb.2

  let A : ℝ :=
    3 * h3PathSqrtEnergyRiccatiCoefficient ^ 2

  have hAPos : 0 < A := by
    dsimp only [A]
    exact
      mul_pos
        (by norm_num : (0 : ℝ) < 3)
        (pow_pos h3PathSqrtEnergyRiccatiCoefficient_pos 2)

  refine tendsto_atTop.2 ?_
  intro M

  by_cases hM : M ≤ 0
  · show
      {t : ℝ |
        M ≤ (T - t) * velocityH3Energy3At u t}
        ∈ 𝓝[<] T

    rw [mem_nhdsLT_iff_exists_Ioo_subset]

    refine ⟨cRate, hcRate.2, ?_⟩
    intro t ht

    have hGapNonneg : 0 ≤ T - t := by
      linarith [ht.2]

    have hE3Nonneg :
        0 ≤ velocityH3Energy3At u t :=
      velocityH3Energy3At_nonneg u t

    exact
      le_trans
        hM
        (mul_nonneg hGapNonneg hE3Nonneg)

  · have hMPos : 0 < M := lt_of_not_ge hM

    let B : ℝ := (A * M) ^ 2

    obtain ⟨cSmall, hcSmall, hSmall⟩ :=
      exists_terminalTail_const_mul_terminalDistance_sq_le_one
        B T cRate hcRate.2

    show
      {t : ℝ |
        M ≤ (T - t) * velocityH3Energy3At u t}
        ∈ 𝓝[<] T

    rw [mem_nhdsLT_iff_exists_Ioo_subset]

    refine ⟨cSmall, hcSmall.2, ?_⟩
    intro t ht

    have htRate : t ∈ Set.Ioo cRate T :=
      ⟨lt_trans hcSmall.1 ht.1, ht.2⟩

    have htAnchor : t ∈ Set.Ioo b T :=
      ⟨lt_trans hcRate.1 htRate.1, htRate.2⟩

    have hRate :
        1 ≤
          A * (T - t) ^ 2 *
            velocityH3Energy3At u t := by
      dsimp only [A]
      exact
        one_le_three_riccatiCoefficient_sq_mul_terminalDistance_sq_mul_energy3_of_noH3PathExtension
          hH3
          hNoExtension
          hClass
          hb
          htAnchor
          (hLate t htRate)

    have hGapPos : 0 < T - t := by
      linarith [ht.2]

    have hSmallT :
        B * (T - t) ^ 2 ≤ 1 :=
      hSmall t ht

    have hAMGapNonneg :
        0 ≤ A * M * (T - t) := by
      positivity

    have hAMGapSq :
        (A * M * (T - t)) ^ 2 ≤ 1 := by
      calc
        (A * M * (T - t)) ^ 2 =
            B * (T - t) ^ 2 := by
          dsimp only [B]
          ring
        _ ≤ 1 := hSmallT

    have hAMGapLeOne :
        A * M * (T - t) ≤ 1 := by
      nlinarith [sq_nonneg (A * M * (T - t))]

    by_contra hNot

    have hClockLt :
        (T - t) * velocityH3Energy3At u t < M :=
      lt_of_not_ge hNot

    have hScalePos : 0 < A * (T - t) :=
      mul_pos hAPos hGapPos

    have hScaledLt :
        A * (T - t) *
              ((T - t) * velocityH3Energy3At u t) <
            A * (T - t) * M :=
      mul_lt_mul_of_pos_left hClockLt hScalePos

    have hRateReassociated :
        1 ≤
          A * (T - t) *
            ((T - t) * velocityH3Energy3At u t) := by
      calc
        1 ≤ A * (T - t) ^ 2 *
              velocityH3Energy3At u t := hRate
        _ = A * (T - t) *
              ((T - t) * velocityH3Energy3At u t) := by
          ring

    have hScaledUpper :
        A * (T - t) * M ≤ 1 := by
      calc
        A * (T - t) * M = A * M * (T - t) := by ring
        _ ≤ 1 := hAMGapLeOne

    linarith

/-- The full H³ physical energy clock also diverges, since `E₃ ≤ E`. -/
theorem velocityH3EnergyPhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (fun t : ℝ =>
        (T - t) * velocityH3EnergyAt u t)
      (𝓝[<] T)
      atTop := by
  have hTopClock :=
    velocityH3Energy3PhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass

  refine tendsto_atTop.2 ?_
  intro M

  have hEventually :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        M ≤ (T - t) * velocityH3Energy3At u t :=
    hTopClock.eventually
      (eventually_ge_atTop M)

  have hTail :
      Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT hClass.terminal_start.2

  filter_upwards [hEventually, hTail] with t hM ht

  have hGapNonneg : 0 ≤ T - t := by
    linarith [ht.2]

  have hTop :
      velocityH3Energy3At u t ≤ velocityH3EnergyAt u t :=
    velocityH3Energy3At_le_velocityH3EnergyAt u t

  exact
    le_trans
      hM
      (mul_le_mul_of_nonneg_left hTop hGapNonneg)

/-- The top H³ dissipation physical clock diverges throughout the full left
terminal neighborhood. -/
theorem velocityH3Dissipation3PhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (fun t : ℝ =>
        (T - t) * velocityH3Dissipation3At u t)
      (𝓝[<] T)
      atTop := by
  have hEnergyClock :=
    velocityH3Energy3PhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass

  have hRatio :=
    velocityH3Dissipation3At_div_energy3At_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass

  refine tendsto_atTop.2 ?_
  intro M

  by_cases hM : M ≤ 0
  · have hTail :
        Set.Ioo a T ∈ 𝓝[<] T :=
      Ioo_mem_nhdsLT hClass.terminal_start.2

    filter_upwards [hTail] with t ht

    have hGapNonneg : 0 ≤ T - t := by
      linarith [ht.2]

    have hD3Nonneg :
        0 ≤ velocityH3Dissipation3At u t :=
      velocityH3Dissipation3At_nonneg u t

    exact
      le_trans
        hM
        (mul_nonneg hGapNonneg hD3Nonneg)

  · have hMPos : 0 < M := lt_of_not_ge hM

    have hClockEventually :
        ∀ᶠ t : ℝ in 𝓝[<] T,
          M ≤ (T - t) * velocityH3Energy3At u t :=
      hEnergyClock.eventually
        (eventually_ge_atTop M)

    have hRatioEventually :
        ∀ᶠ t : ℝ in 𝓝[<] T,
          1 ≤
            velocityH3Dissipation3At u t /
              velocityH3Energy3At u t :=
      hRatio.eventually
        (eventually_ge_atTop 1)

    have hTail :
        Set.Ioo a T ∈ 𝓝[<] T :=
      Ioo_mem_nhdsLT hClass.terminal_start.2

    filter_upwards
      [hClockEventually, hRatioEventually, hTail]
      with t hClock hRatioT ht

    have hGapPos : 0 < T - t := by
      linarith [ht.2]

    have hClockPos :
        0 < (T - t) * velocityH3Energy3At u t :=
      lt_of_lt_of_le hMPos hClock

    have hE3Nonneg :
        0 ≤ velocityH3Energy3At u t :=
      velocityH3Energy3At_nonneg u t

    have hE3Pos :
        0 < velocityH3Energy3At u t := by
      by_contra hNot
      have hE3Le : velocityH3Energy3At u t ≤ 0 :=
        le_of_not_gt hNot
      have hE3Zero : velocityH3Energy3At u t = 0 :=
        le_antisymm hE3Le hE3Nonneg
      rw [hE3Zero, mul_zero] at hClockPos
      linarith

    have hTop :
        velocityH3Energy3At u t ≤
          velocityH3Dissipation3At u t := by
      have hLinear :=
        (le_div_iff₀ hE3Pos).1 hRatioT
      simpa using hLinear

    have hScaled :
        (T - t) * velocityH3Energy3At u t ≤
          (T - t) * velocityH3Dissipation3At u t :=
      mul_le_mul_of_nonneg_left
        hTop
        (le_of_lt hGapPos)

    exact le_trans hClock hScaled

/-- The full H³ dissipation physical clock diverges throughout the full left
terminal neighborhood. -/
theorem velocityH3DissipationPhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    Tendsto
      (fun t : ℝ =>
        (T - t) * velocityH3DissipationAt u t)
      (𝓝[<] T)
      atTop := by
  have hTopClock :=
    velocityH3Dissipation3PhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass

  refine tendsto_atTop.2 ?_
  intro M

  have hEventually :
      ∀ᶠ t : ℝ in 𝓝[<] T,
        M ≤ (T - t) * velocityH3Dissipation3At u t :=
    hTopClock.eventually
      (eventually_ge_atTop M)

  have hTail :
      Set.Ioo a T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT hClass.terminal_start.2

  filter_upwards [hEventually, hTail] with t hM ht

  have hGapNonneg : 0 ≤ T - t := by
    linarith [ht.2]

  have hTop :
      velocityH3Dissipation3At u t ≤
        velocityH3DissipationAt u t :=
    velocityH3Dissipation3At_le_dissipationAt u t

  exact
    le_trans
      hM
      (mul_le_mul_of_nonneg_left hTop hGapNonneg)

/-- Neutral package: either the H³ path continues smoothly, or all canonical
physical energy and dissipation clocks diverge along the full left terminal
neighborhood. -/
theorem smoothContinuationExtension_or_fullTailPhysicalEnergyDissipationClocks
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    (
      Tendsto
        (fun t : ℝ =>
          (T - t) * velocityH3Energy3At u t)
        (𝓝[<] T) atTop
      ∧
      Tendsto
        (fun t : ℝ =>
          (T - t) * velocityH3EnergyAt u t)
        (𝓝[<] T) atTop
      ∧
      Tendsto
        (fun t : ℝ =>
          (T - t) * velocityH3Dissipation3At u t)
        (𝓝[<] T) atTop
      ∧
      Tendsto
        (fun t : ℝ =>
          (T - t) * velocityH3DissipationAt u t)
        (𝓝[<] T) atTop
    ) := by
  classical

  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T

  · exact Or.inl hExtension

  · exact
      Or.inr
        ⟨
          velocityH3Energy3PhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3 hExtension hClass,
          velocityH3EnergyPhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3 hExtension hClass,
          velocityH3Dissipation3PhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3 hExtension hClass,
          velocityH3DissipationPhysicalClock_tendsto_atTop_nhdsLT_of_noH3PathExtension
            hH3 hExtension hClass
        ⟩

end

end Euclidean
end Bridge
end PrimeTensor
