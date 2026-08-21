import PrimeTensor.Bridge.MulRealScalarDerivativeSemantics
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Nat.Find

/-!
# Dyadic logarithmic little-o implies ordinary little-o

The native derivative bridge currently lands in `RealLogScaleLittleO`, whose
quantifiers are expressed in the intrinsic dyadic scale hierarchy.

This file proves the direction needed for conventional analysis:

    RealLogScaleLittleO error base
    + base -> 0
    --------------------------------
    error =o[tailFilter] base

in Mathlib's standard `Asymptotics.IsLittleO` sense.

The key geometric fact is that every sufficiently small positive magnitude
lies between two consecutive native logarithmic radii.  Therefore one native
refinement gain gives a uniform multiplicative improvement relative to the
actual base magnitude, not merely relative to a fixed ambient radius.
-/

namespace PrimeTensor
namespace Bridge

/--
Advancing by a natural-depth gain performs exactly `n+1` radius halvings.
-/
theorem logScaleRadius_advance_depthFromNat
    (level : Depth) :
    ∀ n : ℕ,
      PrimeTensor.Bridge.logScaleRadius
          (
            Depth.advance
              level
              (PrimeTensor.Bridge.depthFromNat n)
          )
        =
      PrimeTensor.Bridge.logScaleRadius level /
        (2 : ℝ) ^ (n + 1)

  | 0 => by

      change
        PrimeTensor.Bridge.logScaleRadius
            (.succ level)
          =
        PrimeTensor.Bridge.logScaleRadius level /
          (2 : ℝ) ^ 1

      rw [
        PrimeTensor.Bridge.logScaleRadius_succ,
        pow_one
      ]

  | n + 1 => by

      change
        PrimeTensor.Bridge.logScaleRadius
            (
              .succ
                (
                  Depth.advance
                    level
                    (PrimeTensor.Bridge.depthFromNat n)
                )
            )
          =
        PrimeTensor.Bridge.logScaleRadius level /
          (2 : ℝ) ^ ((n + 1) + 1)

      rw [
        PrimeTensor.Bridge.logScaleRadius_succ,
        logScaleRadius_advance_depthFromNat level n,
        pow_succ
      ]

      ring

/--
Every nontrivial native gain strictly shrinks the logarithmic radius.
-/
theorem logScaleRadius_advance_lt
    (level gain : Depth) :
    PrimeTensor.Bridge.logScaleRadius
        (Depth.advance level gain)
      <
    PrimeTensor.Bridge.logScaleRadius level := by

  induction gain with

  | one =>

      change
        PrimeTensor.Bridge.logScaleRadius (.succ level)
          <
        PrimeTensor.Bridge.logScaleRadius level

      rw [
        PrimeTensor.Bridge.logScaleRadius_succ
      ]

      have hPos :
          0 <
            PrimeTensor.Bridge.logScaleRadius level :=
        PrimeTensor.Bridge.logScaleRadius_pos level

      linarith

  | succ gain ih =>

      change
        PrimeTensor.Bridge.logScaleRadius
            (.succ (Depth.advance level gain))
          <
        PrimeTensor.Bridge.logScaleRadius level

      exact
        lt_trans
          (
            by
              rw [
                PrimeTensor.Bridge.logScaleRadius_succ
              ]

              have hPos :
                  0 <
                    PrimeTensor.Bridge.logScaleRadius
                      (Depth.advance level gain) :=
                PrimeTensor.Bridge.logScaleRadius_pos
                  (Depth.advance level gain)

              linarith
          )
          ih

/--
Every positive magnitude below the largest native logarithmic radius lies
strictly below some radius which is at most twice that magnitude.

This is the dyadic bracketing lemma needed to turn scale-wise improvement into
an actual little-o ratio estimate.
-/
theorem exists_logScaleRadius_bracket
    {b : ℝ}
    (hb : 0 < b)
    (hbTop :
      b <
        PrimeTensor.Bridge.logScaleRadius .one) :
    ∃ level : Depth,
      b <
          PrimeTensor.Bridge.logScaleRadius level
        ∧
      PrimeTensor.Bridge.logScaleRadius level
          ≤
        2 * b := by

  let P : ℕ → Prop :=
    fun n =>
      PrimeTensor.Bridge.logScaleRadius
          (PrimeTensor.Bridge.depthFromNat n)
        ≤
      b

  have hExists :
      ∃ n : ℕ, P n := by

    obtain ⟨d, hd⟩ :=
      PrimeTensor.Bridge.exists_logScaleRadius_lt
        hb

    refine
      ⟨PrimeTensor.Bridge.depthIndex d, ?_⟩

    dsimp [P]

    rw [
      PrimeTensor.Bridge.depthFromNat_depthIndex
    ]

    exact le_of_lt hd

  have hNotZero :
      ¬ P 0 := by

    dsimp [P]

    rw [
      PrimeTensor.Bridge.depthFromNat_zero
    ]

    exact not_le_of_gt hbTop

  have hFindPos :
      0 < Nat.find hExists :=
    (
      Nat.find_pos hExists
    ).2 hNotZero

  obtain ⟨j, hj⟩ :
      ∃ j : ℕ,
        Nat.find hExists = j + 1 := by

    exact
      Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt hFindPos)

  have hSucc :
      P (j + 1) := by

    have hSpec :=
      Nat.find_spec hExists

    rw [hj] at hSpec

    exact hSpec

  have hPrevNot :
      ¬ P j := by

    apply Nat.find_min hExists

    rw [hj]

    omega

  refine
    ⟨
      PrimeTensor.Bridge.depthFromNat j,
      ?_,
      ?_
    ⟩

  · have hNotLe :
        ¬
          PrimeTensor.Bridge.logScaleRadius
              (PrimeTensor.Bridge.depthFromNat j)
            ≤
          b := by

      exact hPrevNot

    exact lt_of_not_ge hNotLe

  · dsimp [P] at hSucc

    rw [
      PrimeTensor.Bridge.depthFromNat_succ,
      PrimeTensor.Bridge.logScaleRadius_succ
    ] at hSucc

    linarith

/--
A real little-o constant can be dominated by sufficiently many native dyadic
refinements.
-/
theorem exists_dyadic_gain_factor_lt
    {c : ℝ}
    (hc : 0 < c) :
    ∃ k : ℕ,
      1 / (2 : ℝ) ^ k < c := by

  have hTwo :
      (1 : ℝ) < 2 := by
    norm_num

  obtain ⟨k, hk⟩ :=
    pow_unbounded_of_one_lt
      (1 / c)
      hTwo

  refine ⟨k, ?_⟩

  have hPowPos :
      0 < (2 : ℝ) ^ k :=
    pow_pos (by norm_num) k

  rw [div_lt_iff₀ hPowPos]

  rw [div_lt_iff₀ hc] at hk

  simpa only [mul_comm] using hk

/--
If a dyadic logarithmic little-o relation is evaluated along a base tending to
zero, then it is ordinary Mathlib little-o along the native tail filter.
-/
theorem realLogScaleLittleO_to_isLittleO
    {error base : Depth → ℝ}
    (hBase :
      Filter.Tendsto
        base
        PrimeTensor.Bridge.Depth.tailFilter
        (nhds 0))
    (hLittle :
      PrimeTensor.Bridge.RealLogScaleLittleO
        error base) :
    Asymptotics.IsLittleO
      PrimeTensor.Bridge.Depth.tailFilter
      error
      base := by

  apply Asymptotics.IsLittleO.of_bound

  intro c hc

  obtain ⟨k, hFactor⟩ :=
    exists_dyadic_gain_factor_lt hc

  obtain ⟨anchor, hDyadic⟩ :=
    hLittle
      (PrimeTensor.Bridge.depthFromNat k)

  have hDyadicEventually :
      ∀ᶠ n in PrimeTensor.Bridge.Depth.tailFilter,
        ∀ level : Depth,
          abs (base n) <
              PrimeTensor.Bridge.logScaleRadius level →
          abs (error n) <
              PrimeTensor.Bridge.logScaleRadius
                (
                  Depth.advance
                    level
                    (PrimeTensor.Bridge.depthFromNat k)
                ) := by

    rw [
      PrimeTensor.Bridge.Depth.eventually_tailFilter_iff
    ]

    exact ⟨anchor, hDyadic⟩

  have hBaseSmall :
      ∀ᶠ n in PrimeTensor.Bridge.Depth.tailFilter,
        abs (base n) <
          PrimeTensor.Bridge.logScaleRadius .one := by

    have hRadiusPos :
        0 <
          PrimeTensor.Bridge.logScaleRadius .one :=
      PrimeTensor.Bridge.logScaleRadius_pos .one

    have hMetric :=
      (
        Metric.tendsto_nhds.mp hBase
      )
        (PrimeTensor.Bridge.logScaleRadius .one)
        hRadiusPos

    simpa only [
      Real.dist_eq,
      sub_zero
    ] using hMetric

  filter_upwards [
    hDyadicEventually,
    hBaseSmall
  ] with n hDn hBn

  by_cases hBaseZero :
      base n = 0

  · have hErrorZero :
        error n = 0 := by

      have hAbsErrorZero :
          abs (error n) = 0 := by

        apply le_antisymm

        · by_contra hNotLe

          have hErrorPos :
              0 < abs (error n) :=
            lt_of_not_ge hNotLe

          obtain ⟨level, hLevel⟩ :=
            PrimeTensor.Bridge.exists_logScaleRadius_lt
              hErrorPos

          have hBaseAtLevel :
              abs (base n) <
                PrimeTensor.Bridge.logScaleRadius level := by

            rw [hBaseZero, abs_zero]

            exact
              PrimeTensor.Bridge.logScaleRadius_pos
                level

          have hErrorAtGain :=
            hDn level hBaseAtLevel

          have hGainLt :
              PrimeTensor.Bridge.logScaleRadius
                  (
                    Depth.advance
                      level
                      (PrimeTensor.Bridge.depthFromNat k)
                  )
                <
              PrimeTensor.Bridge.logScaleRadius level :=
            PrimeTensor.Bridge.logScaleRadius_advance_lt
              level
              (PrimeTensor.Bridge.depthFromNat k)

          have :
              abs (error n) <
                PrimeTensor.Bridge.logScaleRadius level :=
            lt_trans hErrorAtGain hGainLt

          exact
            (not_lt_of_ge (le_of_lt hLevel))
              this

        · exact abs_nonneg (error n)

      exact abs_eq_zero.mp hAbsErrorZero

    simp only [
      hBaseZero,
      hErrorZero,
      norm_zero,
      mul_zero,
      le_refl
    ]

  · have hBaseAbsPos :
        0 < abs (base n) :=
      abs_pos.mpr hBaseZero

    obtain
      ⟨level, hLower, hUpper⟩ :=
        PrimeTensor.Bridge.exists_logScaleRadius_bracket
          hBaseAbsPos
          hBn

    have hErrorRadius :
        abs (error n) <
          PrimeTensor.Bridge.logScaleRadius
            (
              Depth.advance
                level
                (PrimeTensor.Bridge.depthFromNat k)
            ) :=
      hDn level hLower

    rw [
      PrimeTensor.Bridge.logScaleRadius_advance_depthFromNat
        level
        k
    ] at hErrorRadius

    have hPowPos :
        0 < (2 : ℝ) ^ k :=
      pow_pos (by norm_num) k

    have hHalfUpper :
        PrimeTensor.Bridge.logScaleRadius level / 2
          ≤
        abs (base n) := by

      apply
        (
          div_le_iff₀
            (by norm_num : (0 : ℝ) < 2)
        ).2

      simpa only [mul_comm] using hUpper

    have hRadiusBound :
        PrimeTensor.Bridge.logScaleRadius level /
              (2 : ℝ) ^ (k + 1)
          ≤
        abs (base n) /
          (2 : ℝ) ^ k := by

      rw [pow_succ]

      calc
        PrimeTensor.Bridge.logScaleRadius level /
              ((2 : ℝ) ^ k * 2)
            =
          (
            PrimeTensor.Bridge.logScaleRadius level / 2
          ) /
            (2 : ℝ) ^ k := by
              ring

        _ ≤
          abs (base n) /
            (2 : ℝ) ^ k := by

              exact
                (
                  div_le_div_iff_of_pos_right
                    hPowPos
                ).2
                  hHalfUpper

    have hRatio :
        abs (base n) /
            (2 : ℝ) ^ k
          <
        c * abs (base n) := by

      calc
        abs (base n) /
              (2 : ℝ) ^ k
            =
          (
            1 / (2 : ℝ) ^ k
          ) *
            abs (base n) := by
              ring

        _ <
          c * abs (base n) :=
            mul_lt_mul_of_pos_right
              hFactor
              hBaseAbsPos

    have hFinal :
        abs (error n) <
          c * abs (base n) :=
      lt_of_lt_of_le hErrorRadius hRadiusBound
        |> fun h =>
          lt_trans h hRatio

    simpa only [
      Real.norm_eq_abs
    ] using
      (le_of_lt hFinal)

/--
The scalar native derivative expansion therefore has Mathlib's ordinary
little-o semantics.
-/
theorem hasMulDerivativeAt_scalar_isLittleO
    {f : PrimeTensor.MulReal → PrimeTensor.MulReal}
    {x : PrimeTensor.MulReal}
    {D : PrimeTensor.MulTangentMap}
    (hDeriv :
      PrimeTensor.MulDifferential.HasMulDerivativeAt
        f x D)
    (hControlled :
      PrimeTensor.MulTangentMap.ScaleControlled D) :
    ∀ h : PrimeTensor.MulReal.Seq,
      Filter.Tendsto
        (
          fun n : Depth =>
            PrimeTensor.Bridge.MulReal.logValue
              (h n)
        )
        PrimeTensor.Bridge.Depth.tailFilter
        (nhds 0) →
      Asymptotics.IsLittleO
        PrimeTensor.Bridge.Depth.tailFilter
        (
          fun n =>
            (
              PrimeTensor.Bridge.MulReal.logValue
                  (f (x * h n)) -
                PrimeTensor.Bridge.MulReal.logValue
                  (f x)
            ) -
            PrimeTensor.Bridge.MulDifferential.scalarCoefficient D *
              PrimeTensor.Bridge.MulReal.logValue
                (h n)
        )
        (
          fun n =>
            PrimeTensor.Bridge.MulReal.logValue
              (h n)
        ) := by

  intro h hLogZero

  apply
    PrimeTensor.Bridge.realLogScaleLittleO_to_isLittleO
      hLogZero

  exact
    PrimeTensor.Bridge.MulDifferential.hasMulDerivativeAt_scalar_log_expansion
      hDeriv
      hControlled
      h
      hLogZero

end Bridge
end PrimeTensor
