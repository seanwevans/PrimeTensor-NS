import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Third.Rate.Dissipation.Eventual
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Riccati.Integrability

/-!
# Terminal nonintegrability of the top H³ dissipation

The eventual top-dissipation theorem gives, under hypothetical nonextension,

    1 ≤ 81 K⁸ (T - t)⁸ E₀(b) D₃(t)³

on a sufficiently late terminal interval.

Taking an explicit cube root would prove the sharp lower scale

    D₃(t) ≳ (T - t)^(-8/3),

but that introduces unnecessary fractional-power bookkeeping.

For integrability it is enough to lose some exponent.  Since the fixed
coefficient

    B = 81 K⁸ E₀(b)

satisfies

    B (T - t)² ≤ 1

on a still shorter terminal interval, the cubic estimate forces

    1 ≤ (T - t)² D₃(t).

After also shortening so that `T - t ≤ 1`, this gives the harmonic lower bound

    1 / (T - t) ≤ D₃(t).

The reciprocal terminal-distance profile is already known to be nonintegrable
on every nontrivial interval ending at `T`.  Hence the top H³ dissipation
itself cannot be integrable on a terminal H³ energy-class tail of a
hypothetical nonextendible path.

This remains a necessary condition on the nonextension branch; it does not
assert that such a branch exists.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-! ## Fixed coefficients become small after multiplication by (T-t)^2 -/

/--
Any fixed real coefficient times `(T-t)^2` is at most `1` on some sufficiently
late terminal interval.
-/
theorem exists_terminalTail_const_mul_terminalDistance_sq_le_one
    (C T b : ℝ)
    (hbT : b < T) :
    ∃ c : ℝ,
      c ∈ Set.Ioo b T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo c T →
        C * (T - t) ^ 2 ≤ 1 := by

  let F : ℝ → ℝ :=
    fun t =>
      C * (T - t) ^ 2

  have hConstT :
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
    hConstT.sub hId

  have hDistance :
      Tendsto
        (fun t : ℝ => T - t)
        (𝓝 T)
        (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using hDistanceRaw

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

  have hConstC :
      Tendsto
        (fun _ : ℝ => C)
        (𝓝 T)
        (𝓝 C) :=
    tendsto_const_nhds

  have hProduct :
      Tendsto
        (fun t : ℝ => C * (T - t) ^ 2)
        (𝓝 T)
        (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (hConstC.mul hDistanceSq)

  have hF :
      Tendsto
        F
        (𝓝 T)
        (𝓝 (0 : ℝ)) := by
    simpa only [F] using hProduct

  have hEventually :
      ∀ᶠ t : ℝ in 𝓝 T,
        F t < 1 :=
    (tendsto_order.1 hF).2
      1
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

  have hStrict :
      F t < 1 :=
    hSubset
      htNeighborhood

  dsimp only [F] at hStrict

  exact le_of_lt hStrict

/-! ## Eventual harmonic lower bound for D₃ -/

/--
A hypothetical nonextendible path has a still-shorter terminal interval on
which the top H³ dissipation dominates the reciprocal terminal distance:

    1 / (T - t) ≤ D₃(t).

This deliberately weakens the sharp inverse-8/3 scale to avoid cube roots.
-/
theorem exists_terminalTail_one_div_terminalDistance_le_dissipation3_of_noH3PathExtension
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
        1 / (T - t)
          ≤
        velocityH3Dissipation3At u t := by

  obtain
    ⟨cRate, hcRate, hRate⟩ :=
    exists_terminalTail_topH3DissipationRate_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  let B : ℝ :=
    81
      *
    h3PathSqrtEnergyRiccatiCoefficient ^ 8
      *
    velocityH3Energy0At u b

  let M : ℝ :=
    max B 1

  obtain
    ⟨cSmall, hcSmall, hSmall⟩ :=
    exists_terminalTail_const_mul_terminalDistance_sq_le_one
      M
      T
      b
      hb.2

  let c : ℝ :=
    max cRate cSmall

  have hc :
      c ∈ Set.Ioo b T := by
    constructor
    · dsimp only [c]
      exact
        lt_of_lt_of_le
          hcRate.1
          (le_max_left cRate cSmall)
    · dsimp only [c]
      exact
        max_lt
          hcRate.2
          hcSmall.2

  refine
    ⟨
      c,
      hc,
      ?_
    ⟩

  intro t ht

  have htRate :
      t ∈ Set.Ioo cRate T := by
    constructor
    · exact
        lt_of_le_of_lt
          (show cRate ≤ c by
            dsimp only [c]
            exact le_max_left _ _)
          ht.1
    · exact ht.2

  have htSmall :
      t ∈ Set.Ioo cSmall T := by
    constructor
    · exact
        lt_of_le_of_lt
          (show cSmall ≤ c by
            dsimp only [c]
            exact le_max_right _ _)
          ht.1
    · exact ht.2

  let d : ℝ :=
    T - t

  let D : ℝ :=
    velocityH3Dissipation3At u t

  have hdPos :
      0 < d := by
    dsimp only [d]
    linarith [ht.2]

  have hdNonneg :
      0 ≤ d :=
    le_of_lt hdPos

  have hDNonneg :
      0 ≤ D := by
    dsimp only [D]
    exact
      velocityH3Dissipation3At_nonneg
        u t

  have hdSqNonneg :
      0 ≤ d ^ 2 :=
    sq_nonneg d

  have hBLeM :
      B ≤ M := by
    dsimp only [M]
    exact le_max_left _ _

  have hOneLeM :
      1 ≤ M := by
    dsimp only [M]
    exact le_max_right _ _

  have hSmallM :
      M * d ^ 2 ≤ 1 := by
    dsimp only [d]
    exact
      hSmall
        t
        htSmall

  have hSmallB :
      B * d ^ 2 ≤ 1 := by
    exact
      le_trans
        (mul_le_mul_of_nonneg_right
          hBLeM
          hdSqNonneg)
        hSmallM

  have hdSqLeOne :
      d ^ 2 ≤ 1 := by
    calc
      d ^ 2
          =
        1 * d ^ 2 := by
          ring

      _ ≤
        M * d ^ 2 :=
        mul_le_mul_of_nonneg_right
          hOneLeM
          hdSqNonneg

      _ ≤ 1 :=
        hSmallM

  have hRateB :
      1
        ≤
      B
        *
      d ^ 8
        *
      D ^ 3 := by

    calc
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
        velocityH3Dissipation3At u t ^ 3 :=
        hRate t htRate

      _ =
        B * d ^ 8 * D ^ 3 := by
        dsimp only [B, d, D]
        ring

  have hXNonneg :
      0 ≤ d ^ 2 * D :=
    mul_nonneg
      hdSqNonneg
      hDNonneg

  have hQuadratic :
      1 ≤ d ^ 2 * D := by

    by_contra hNot

    have hXLt :
        d ^ 2 * D < 1 :=
      lt_of_not_ge hNot

    have hCubeLtRaw :
        (d ^ 2 * D) ^ 3 < (1 : ℝ) ^ 3 :=
      pow_lt_pow_left₀
        hXLt
        hXNonneg
        (by norm_num)

    have hCubeLt :
        (d ^ 2 * D) ^ 3 < 1 := by
      simpa using hCubeLtRaw

    have hCubeNonneg :
        0 ≤ (d ^ 2 * D) ^ 3 :=
      pow_nonneg
        hXNonneg
        3

    have hProductLt :
        (B * d ^ 2)
            *
          (d ^ 2 * D) ^ 3
          <
        1 := by

      calc
        (B * d ^ 2)
              *
            (d ^ 2 * D) ^ 3
            ≤
          1 * (d ^ 2 * D) ^ 3 :=
          mul_le_mul_of_nonneg_right
            hSmallB
            hCubeNonneg

        _ <
          1 * 1 :=
          mul_lt_mul_of_pos_left
            hCubeLt
            (by norm_num)

        _ = 1 := by
          norm_num

    have hFactorization :
        B * d ^ 8 * D ^ 3
          =
        (B * d ^ 2)
          *
        (d ^ 2 * D) ^ 3 := by
      ring

    rw [hFactorization] at hRateB

    exact
      (not_lt_of_ge hRateB)
        hProductLt

  have hdLeOne :
      d ≤ 1 := by

    have hSq :
        d ^ 2 ≤ (1 : ℝ) ^ 2 := by
      simpa using hdSqLeOne

    exact
      (sq_le_sq₀
        hdNonneg
        (by norm_num : (0 : ℝ) ≤ 1)).mp
        hSq

  have hdSqLeD :
      d ^ 2 ≤ d := by

    calc
      d ^ 2
          =
        d * d := by
          ring

      _ ≤
        1 * d :=
        mul_le_mul_of_nonneg_right
          hdLeOne
          hdNonneg

      _ = d := by
        ring

  have hLinear :
      1 ≤ d * D := by

    exact
      le_trans
        hQuadratic
        (mul_le_mul_of_nonneg_right
          hdSqLeD
          hDNonneg)

  apply
    (div_le_iff₀ hdPos).2

  simpa only [one_mul, mul_comm] using
    hLinear

/-! ## Nonintegrability of the top dissipation -/

/--
On every strict subtail of an H³ energy-class tail, hypothetical nonextension
forces the top H³ dissipation to be nonintegrable.
-/
theorem not_integrableOn_velocityH3Dissipation3At_on_strictSubtail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ¬ MeasureTheory.IntegrableOn
        (velocityH3Dissipation3At u)
        (Set.Ioo b T) := by

  obtain
    ⟨c, hc, hHarmonic⟩ :=
    exists_terminalTail_one_div_terminalDistance_le_dissipation3_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  intro hDissipationIntegrable

  have hDissipationIntegrableTail :
      MeasureTheory.IntegrableOn
        (velocityH3Dissipation3At u)
        (Set.Ioo c T) := by

    apply hDissipationIntegrable.mono_set

    intro t ht

    exact
      ⟨
        lt_trans hc.1 ht.1,
        ht.2
      ⟩

  have hReciprocal :
      MeasureTheory.IntegrableOn
        (fun t : ℝ => 1 / (T - t))
        (Set.Ioo c T) := by

    apply
      Integrable.mono'
        hDissipationIntegrableTail

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

      rw [
        Real.norm_eq_abs,
        abs_of_pos
          (one_div_pos.mpr hDist)
      ]

      exact
        hHarmonic
          t
          ht

  exact
    not_integrableOn_one_div_terminalDistance
      hc.2
      hReciprocal

/--
In particular, the top H³ dissipation is nonintegrable on the original
energy-class tail itself under hypothetical nonextension.
-/
theorem not_integrableOn_velocityH3Dissipation3At_on_energyClassTail_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃
        v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ¬ MeasureTheory.IntegrableOn
        (velocityH3Dissipation3At u)
        (Set.Ioo a T) := by

  let b : ℝ :=
    h3BKMKineticTailMidpoint a T

  have hb :
      b ∈ Set.Ioo a T := by
    dsimp only [b]
    exact
      h3BKMKineticTailMidpoint_mem_Ioo
        hClass.terminal_start.2

  have hNotTail :=
    not_integrableOn_velocityH3Dissipation3At_on_strictSubtail_of_noH3PathExtension
      hH3
      hNoExtension
      hClass
      hb

  intro hIntegrable

  apply hNotTail

  apply hIntegrable.mono_set

  intro t ht

  exact
    ⟨
      lt_trans hb.1 ht.1,
      ht.2
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
