import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation

/-!
# Eventual terminal top-dissipation rate

`Rate.Dissipation` proves the top H³ dissipation rate under the late-time
condition

    K² (T - t)² (1 + 3 E₀(b)) ≤ 3.

For fixed `b`, the left-hand side is a continuous function of `t` and tends
to zero as `t → T`.  Hence that condition is automatic on some terminal
subinterval.

This file extracts such an interval and removes the explicit `hLate`
hypothesis from the terminal dissipation theorem.  Under hypothetical
nonextension, for every kinetic anchor `b ∈ (a,T)` there exists `c ∈ (b,T)`
such that every `t ∈ (c,T)` satisfies

    1 ≤ 81 K⁸ (T - t)⁸ E₀(b) D₃(t)³.

Thus the conditional inverse-8/3 top-dissipation scale is genuinely eventual
on the terminal tail.

The statement remains neutral: it is a necessary consequence of hypothetical
nonextension, not an assertion that a singular path exists.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## The late kinetic-anchor condition is automatic near T -/

/--
For every fixed anchor `b < T`, the kinetic-anchor term appearing in the
polynomial third-order terminal rate is at most `3` throughout some smaller
terminal interval `(c,T)`.
-/
theorem exists_terminalTail_kineticAnchorTerm_le_three
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T b : ℝ)
    (hbT : b < T) :
    ∃ c : ℝ,
      c ∈ Set.Ioo b T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        h3PathSqrtEnergyRiccatiCoefficient ^ 2
            *
          (T - t) ^ 2
            *
          (1 + 3 * velocityH3Energy0At u b)
          ≤
        3 := by

  let C : ℝ :=
    h3PathSqrtEnergyRiccatiCoefficient ^ 2
      *
    (1 + 3 * velocityH3Energy0At u b)

  let F : ℝ → ℝ :=
    fun t =>
      C * (T - t) ^ 2

  have hConst :
      Tendsto
        (fun _ : ℝ => T)
        (𝓝 T)
        (𝓝 T) :=
    tendsto_const_nhds

  have hId :
      Tendsto
        (fun t : ℝ => t)
        (𝓝 T)
        (𝓝 T) :=
    tendsto_id

  have hDistanceRaw :
      Tendsto
        (fun t : ℝ => T - t)
        (𝓝 T)
        (𝓝 (T - T)) :=
    hConst.sub hId

  have hDistance :
      Tendsto
        (fun t : ℝ => T - t)
        (𝓝 T)
        (𝓝 0) := by
    simpa only [sub_self] using hDistanceRaw

  have hCConst :
      Tendsto
        (fun _ : ℝ => C)
        (𝓝 T)
        (𝓝 C) :=
    tendsto_const_nhds

  have hDistanceSqRaw :
      Tendsto
        (fun t : ℝ =>
          (T - t) * (T - t))
        (𝓝 T)
        (𝓝 ((0 : ℝ) * 0)) :=
    hDistance.mul hDistance

  have hDistanceSq :
      Tendsto
        (fun t : ℝ => (T - t) ^ 2)
        (𝓝 T)
        (𝓝 (0 : ℝ)) := by
    simpa only [pow_two, zero_mul] using
      hDistanceSqRaw

  have hProduct :
      Tendsto
        (fun t : ℝ => C * (T - t) ^ 2)
        (𝓝 T)
        (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (hCConst.mul hDistanceSq)

  have hF :
      Tendsto
        F
        (𝓝 T)
        (𝓝 (0 : ℝ)) := by
    simpa only [F] using hProduct

  have hEventually :
      ∀ᶠ t : ℝ in 𝓝 T,
        F t < 3 :=
    (tendsto_order.1 hF).2
      3
      (by norm_num)

  obtain
    ⟨l, r, hT, hSubset⟩ :=
    hEventually.exists_Ioo_subset

  have hMax :
      max b l < T :=
    max_lt
      hbT
      hT.1

  let c : ℝ :=
    h3BKMKineticTailMidpoint
      (max b l)
      T

  have hcMid :
      c ∈ Set.Ioo (max b l) T := by
    dsimp only [c]
    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hMax

  have hc :
      c ∈ Set.Ioo b T := by
    constructor
    · exact
        lt_of_le_of_lt
          (le_max_left b l)
          hcMid.1
    · exact hcMid.2

  refine
    ⟨
      c,
      hc,
      ?_
    ⟩

  intro t ht

  have htl :
      l < t :=
    lt_of_le_of_lt
      (le_max_right b l)
      (lt_trans hcMid.1 ht.1)

  have htr :
      t < r :=
    lt_trans
      ht.2
      hT.2

  have htNeighborhood :
      t ∈ Set.Ioo l r :=
    ⟨htl, htr⟩

  have hLateStrict :
      F t < 3 :=
    hSubset
      htNeighborhood

  have hLate :
      F t ≤ 3 :=
    le_of_lt hLateStrict

  dsimp only [F, C] at hLate

  calc
    h3PathSqrtEnergyRiccatiCoefficient ^ 2
        *
      (T - t) ^ 2
        *
      (1 + 3 * velocityH3Energy0At u b)
        =
      (
        h3PathSqrtEnergyRiccatiCoefficient ^ 2
          *
        (1 + 3 * velocityH3Energy0At u b)
      )
        *
      (T - t) ^ 2 := by
      ring

    _ ≤ 3 :=
      hLate

/-! ## Eventual top-dissipation rate under nonextension -/

/--
The `hLate` hypothesis in the top-dissipation rate is automatic after one
further restart: every hypothetical nonextendible H³ path has a terminal
subinterval on which

    1 ≤ 81 K⁸ (T - t)⁸ E₀(b) D₃(t)³.
-/
theorem exists_terminalTail_topH3DissipationRate_of_noH3PathExtension
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
        81
          *
        h3PathSqrtEnergyRiccatiCoefficient ^ 8
          *
        (T - t) ^ 8
          *
        velocityH3Energy0At u b
          *
        velocityH3Dissipation3At u t ^ 3 := by

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

  exact
    one_le_eightyOne_mul_riccatiCoefficient_pow_eight_mul_terminalDistance_pow_eight_mul_energy0Anchor_mul_dissipation3_pow_three_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb
      htAnchor
      (hLate t ht)

/--
Canonical midpoint-anchor form.  The only remaining existential is the
automatic terminal restart `c`.
-/
theorem exists_terminalTail_topH3DissipationRate_midpoint_of_noH3PathExtension
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
    exists_terminalTail_topH3DissipationRate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      (h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2)

end

end Euclidean
end Bridge
end PrimeTensor
