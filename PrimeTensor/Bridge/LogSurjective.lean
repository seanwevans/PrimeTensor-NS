import PrimeTensor.Bridge.LogTangentSpace
import PrimeTensor.Bridge.Cauchy
import PrimeTensor.Bridge.NormalizedTargetApprox

/-!
# Surjectivity of the completed logarithmic coordinate

The completed logarithmic coordinate

    MulReal.logValue : MulReal → ℝ

is already injective.  This file proves surjectivity.

For an arbitrary real `r`, we approximate the positive real target `exp r`
from above by dyadic positive rationals

    (floor (exp r * D) + 1) / D,

where `D` is the existing positive dyadic denominator attached to native
`Depth`.  Every such rational reverse-encodes into an actual finite `MulRat`.
The approximation error is at most `1 / D`, hence the terms form a native
multiplicative Cauchy stream.  Their ordinary real values converge to `exp r`,
so their logarithms converge to `r`.

Thus every real logarithmic coordinate is represented by a completed native
multiplicative real.
-/

namespace PrimeTensor
namespace Bridge

namespace RealLogEncode

/-- Positive conventional target corresponding to logarithmic coordinate `r`. -/
noncomputable def target
    (r : ℝ) : ℝ :=
  Real.exp r

theorem target_pos
    (r : ℝ) :
    0 < target r := by
  unfold target
  exact Real.exp_pos r

/--
Scaled positive target at one native precision depth.
-/
noncomputable def scaled
    (r : ℝ)
    (d : Depth) : ℝ :=
  target r *
    (
      PrimeTensor.Bridge.PrimePairApprox.denom d :
        ℝ
    )

/--
Strictly positive dyadic numerator.  The `+ 1` avoids a zero numerator even
when `exp r` is smaller than the first finite dyadic unit.
-/
noncomputable def numerator
    (r : ℝ)
    (d : Depth) : ℕ :=
  ⌊scaled r d⌋₊ + 1

theorem numerator_pos
    (r : ℝ)
    (d : Depth) :
    0 < numerator r d := by
  unfold numerator
  exact Nat.succ_pos _

theorem numerator_ne_zero
    (r : ℝ)
    (d : Depth) :
    numerator r d ≠ 0 :=
  Nat.ne_of_gt (numerator_pos r d)

/-- The scaled target is nonnegative. -/
theorem scaled_nonneg
    (r : ℝ)
    (d : Depth) :
    0 ≤ scaled r d := by

  unfold scaled

  exact
    mul_nonneg
      (le_of_lt (target_pos r))
      (
        le_of_lt
          (
            PrimeTensor.Bridge.PrimePairApprox.denom_real_pos
              d
          )
      )

/-- The floor lies below the scaled target. -/
theorem floor_le_scaled
    (r : ℝ)
    (d : Depth) :
    (
      ⌊scaled r d⌋₊ :
        ℝ
    )
      ≤
    scaled r d := by

  exact
    Nat.floor_le
      (scaled_nonneg r d)

/-- The scaled target lies strictly below our positive numerator. -/
theorem scaled_lt_numerator
    (r : ℝ)
    (d : Depth) :
    scaled r d <
      (numerator r d : ℝ) := by

  have h :=
    Nat.lt_floor_add_one
      (scaled r d)

  unfold numerator

  exact_mod_cast h

/-- The positive numerator is at most one dyadic unit above the scaled target. -/
theorem numerator_le_scaled_add_one
    (r : ℝ)
    (d : Depth) :
    (numerator r d : ℝ) ≤
      scaled r d + 1 := by

  have hFloor :=
    floor_le_scaled r d

  unfold numerator

  push_cast

  linarith

/-- Finite native barcode for one dyadic approximation to `exp r`. -/
noncomputable def term
    (r : ℝ)
    (d : Depth) :
    PrimeTensor.MulRat :=
  PrimeTensor.Bridge.Encode.ratio
    (numerator r d)
    (PrimeTensor.Bridge.PrimePairApprox.denom d)
    (numerator_ne_zero r d)
    (PrimeTensor.Bridge.PrimePairApprox.denom_ne_zero d)

/-- Conventional value of one finite native approximation. -/
theorem term_toReal
    (r : ℝ)
    (d : Depth) :
    PrimeTensor.Bridge.MulRat.toReal
        (term r d)
      =
    (numerator r d : ℝ) /
      (
        PrimeTensor.Bridge.PrimePairApprox.denom d :
          ℝ
      ) := by

  unfold term

  exact
    PrimeTensor.Bridge.Encode.ratio_toReal
      (numerator r d)
      (PrimeTensor.Bridge.PrimePairApprox.denom d)
      (numerator_ne_zero r d)
      (PrimeTensor.Bridge.PrimePairApprox.denom_ne_zero d)

/-- Every approximation lies strictly above its positive target. -/
theorem target_lt_term
    (r : ℝ)
    (d : Depth) :
    target r <
      PrimeTensor.Bridge.MulRat.toReal
        (term r d) := by

  rw [term_toReal]

  apply
    (
      lt_div_iff₀
        (
          PrimeTensor.Bridge.PrimePairApprox.denom_real_pos
            d
        )
    ).mpr

  change
    target r *
        (
          PrimeTensor.Bridge.PrimePairApprox.denom d :
            ℝ
        )
      <
    (numerator r d : ℝ)

  exact scaled_lt_numerator r d

/--
The upper approximation error is at most one dyadic unit.
-/
theorem term_sub_target_le_unit
    (r : ℝ)
    (d : Depth) :
    PrimeTensor.Bridge.MulRat.toReal
          (term r d) -
        target r
      ≤
    1 /
      (
        PrimeTensor.Bridge.PrimePairApprox.denom d :
          ℝ
      ) := by

  rw [term_toReal]

  let D : ℝ :=
    (
      PrimeTensor.Bridge.PrimePairApprox.denom d :
        ℝ
    )

  have hDpos :
      0 < D := by
    dsimp [D]
    exact
      PrimeTensor.Bridge.PrimePairApprox.denom_real_pos
        d

  have hDne :
      D ≠ 0 :=
    ne_of_gt hDpos

  have hNum :
      (numerator r d : ℝ) ≤
        target r * D + 1 := by

    have h :=
      numerator_le_scaled_add_one r d

    unfold scaled at h

    simpa [D] using h

  have hMain :
      (numerator r d : ℝ) / D
        ≤
      target r + 1 / D := by

    apply (div_le_iff₀ hDpos).mpr

    calc
      (numerator r d : ℝ)
          ≤
        target r * D + 1 :=
        hNum

      _ =
        (target r + 1 / D) * D := by
        field_simp [hDne]
        <;> ring

  dsimp [D] at hMain ⊢

  linarith

/--
Error budget sufficient to put any two late upper approximants within one
requested native multiplicative scale.
-/
noncomputable def errorBudget
    (r : ℝ)
    (level : Depth) : ℝ :=
  target r *
    (
      PrimeTensor.Bridge.scaleRadius level - 1
    )

theorem errorBudget_pos
    (r : ℝ)
    (level : Depth) :
    0 < errorBudget r level := by

  unfold errorBudget

  exact
    mul_pos
      (target_pos r)
      (
        sub_pos.mpr
          (
            PrimeTensor.Bridge.one_lt_scaleRadius
              level
          )
      )

/--
At every requested native scale, all sufficiently late approximation errors
are smaller than the scale budget.
-/
theorem eventually_unit_lt_errorBudget
    (r : ℝ)
    (level : Depth) :
    ∃ anchor : Depth,
      ∀ n : Depth,
        Depth.AtOrAfter anchor n →
        1 /
            (
              PrimeTensor.Bridge.PrimePairApprox.denom n :
                ℝ
            )
          <
        errorBudget r level := by

  exact
    PrimeTensor.Bridge.PrimePairApprox.eventually_unit_lt
      (errorBudget_pos r level)

/-- Raw native dyadic approximation stream. -/
noncomputable def stream
    (r : ℝ) :
    PrimeTensor.MulStream :=
  fun d => term r d

/--
The arbitrary-real dyadic barcode stream is intrinsically multiplicative
Cauchy.
-/
theorem stream_cauchy
    (r : ℝ) :
    PrimeTensor.IsMulCauchy
      (stream r) := by

  intro level

  obtain ⟨anchor, hUnit⟩ :=
    eventually_unit_lt_errorBudget
      r level

  refine ⟨anchor, ?_⟩
  intro m n hm hn

  apply
    (
      PrimeTensor.Bridge.MulRat.scaleWithin_iff_real
        level
        (term r m)
        (term r n)
    ).mpr

  let A : ℝ :=
    PrimeTensor.Bridge.MulRat.toReal
      (term r m)

  let B : ℝ :=
    PrimeTensor.Bridge.MulRat.toReal
      (term r n)

  let T : ℝ :=
    target r

  let R : ℝ :=
    PrimeTensor.Bridge.scaleRadius level

  have hApos :
      0 < A := by
    unfold A
    exact
      PrimeTensor.Bridge.MulRat.toReal_pos
        (term r m)

  have hBpos :
      0 < B := by
    unfold B
    exact
      PrimeTensor.Bridge.MulRat.toReal_pos
        (term r n)

  have hRpos :
      0 < R := by
    unfold R
    exact
      PrimeTensor.Bridge.scaleRadius_pos level

  have hTpos :
      0 < T := by
    unfold T
    exact target_pos r

  have hTA :
      T < A := by
    unfold A T
    exact target_lt_term r m

  have hTB :
      T < B := by
    unfold B T
    exact target_lt_term r n

  have hAerr :
      A - T
        ≤
      1 /
        (
          PrimeTensor.Bridge.PrimePairApprox.denom m :
            ℝ
        ) := by
    unfold A T
    exact term_sub_target_le_unit r m

  have hBerr :
      B - T
        ≤
      1 /
        (
          PrimeTensor.Bridge.PrimePairApprox.denom n :
            ℝ
        ) := by
    unfold B T
    exact term_sub_target_le_unit r n

  have hA_budget :
      A - T <
        errorBudget r level :=
    lt_of_le_of_lt
      hAerr
      (hUnit m hm)

  have hB_budget :
      B - T <
        errorBudget r level :=
    lt_of_le_of_lt
      hBerr
      (hUnit n hn)

  have hBudget :
      errorBudget r level =
        R * T - T := by
    unfold errorBudget R T
    ring

  have hA_RT :
      A < R * T := by
    rw [hBudget] at hA_budget
    linarith

  have hB_RT :
      B < R * T := by
    rw [hBudget] at hB_budget
    linarith

  have hRT_RB :
      R * T < R * B :=
    mul_lt_mul_of_pos_left
      hTB
      hRpos

  have hRT_RA :
      R * T < R * A :=
    mul_lt_mul_of_pos_left
      hTA
      hRpos

  have hAB :
      A / B < R := by
    apply (div_lt_iff₀ hBpos).mpr
    exact lt_trans hA_RT hRT_RB

  have hBA :
      B / A < R := by
    apply (div_lt_iff₀ hApos).mpr
    exact lt_trans hB_RT hRT_RA

  constructor

  · exact
      PrimeTensor.Bridge.realScalePow_lt_two_of_lt_radius
        level
        (div_pos hApos hBpos)
        hAB

  · exact
      PrimeTensor.Bridge.realScalePow_lt_two_of_lt_radius
        level
        (div_pos hBpos hApos)
        hBA

/-- Completed native stream encoding one arbitrary real logarithmic target. -/
noncomputable def cauchyStream
    (r : ℝ) :
    PrimeTensor.MulCauchyStream where

  term :=
    stream r

  cauchy :=
    stream_cauchy r

/--
The ordinary real values of the completed barcode stream converge to `exp r`.
-/
theorem cauchyStream_convergesReal
    (r : ℝ) :
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (cauchyStream r)
      (target r) := by

  intro ε hε

  obtain ⟨anchor, hUnit⟩ :=
    PrimeTensor.Bridge.PrimePairApprox.eventually_unit_lt
      hε

  refine ⟨anchor, ?_⟩
  intro n hn

  change
    abs
      (
        PrimeTensor.Bridge.MulRat.toReal
              (term r n) -
            target r
      )
      <
    ε

  have hNonneg :
      0 ≤
        PrimeTensor.Bridge.MulRat.toReal
              (term r n) -
            target r :=
    le_of_lt
      (
        sub_pos.mpr
          (target_lt_term r n)
      )

  rw [abs_of_nonneg hNonneg]

  exact
    lt_of_le_of_lt
      (term_sub_target_le_unit r n)
      (hUnit n hn)

/--
The whole native logarithmic tail converges to the requested real coordinate.
-/
theorem cauchyStream_logConverges
    (r : ℝ) :
    PrimeTensor.Bridge.MulCauchyStream.LogConverges
      (cauchyStream r)
      r := by

  intro ε hε

  obtain ⟨anchor, hTail⟩ :=
    PrimeTensor.Bridge.MulCauchyStream.convergesReal_logTail
      (cauchyStream_convergesReal r)
      (ne_of_gt (target_pos r))
      ε
      hε

  refine ⟨anchor, ?_⟩
  intro n hn

  have h :=
    hTail n hn

  change
    abs
      (
        PrimeTensor.Bridge.MulCauchyStream.logTerm
              (cauchyStream r) n -
            r
      )
      <
    ε

  simpa [
    PrimeTensor.Bridge.MulCauchyStream.logTerm,
    PrimeTensor.Bridge.MulCauchyStream.toRealTerm,
    target
  ] using h

/--
The canonical chosen logarithmic limit of the stream is exactly the requested
real coordinate.
-/
theorem cauchyStream_logLimit
    (r : ℝ) :
    PrimeTensor.Bridge.MulCauchyStream.logLimit
        (cauchyStream r)
      =
    r := by

  exact
    (
      PrimeTensor.Bridge.MulCauchyStream.logConverges_unique
        (
          PrimeTensor.Bridge.MulCauchyStream.logConverges_logLimit
            (cauchyStream r)
        )
        (cauchyStream_logConverges r)
    )

/--
Completed multiplicative real whose canonical logarithmic coordinate is `r`.
-/
noncomputable def fromLog
    (r : ℝ) :
    PrimeTensor.MulReal :=
  PrimeTensor.MulReal.ofStream
    (cauchyStream r)

@[simp]
theorem logValue_fromLog
    (r : ℝ) :
    PrimeTensor.Bridge.MulReal.logValue
        (fromLog r)
      =
    r := by

  unfold fromLog

  rw [
    PrimeTensor.Bridge.MulReal.logValue_ofStream
  ]

  exact cauchyStream_logLimit r

end RealLogEncode

namespace MulReal

/--
The completed logarithmic coordinate hits every ordinary real number.
-/
theorem logValue_surjective :
    Function.Surjective
      PrimeTensor.Bridge.MulReal.logValue := by

  intro r

  exact
    ⟨
      PrimeTensor.Bridge.RealLogEncode.fromLog r,
      PrimeTensor.Bridge.RealLogEncode.logValue_fromLog r
    ⟩

/--
The completed multiplicative carrier is bijective with the ordinary real line
under its canonical logarithmic coordinate.
-/
theorem logValue_bijective :
    Function.Bijective
      PrimeTensor.Bridge.MulReal.logValue :=
  ⟨
    PrimeTensor.Bridge.MulReal.logValue_injective,
    logValue_surjective
  ⟩

/--
Canonical bridge equivalence between completed multiplicative reals and
ordinary additive reals.
-/
noncomputable def logEquiv :
    PrimeTensor.MulReal ≃ ℝ :=
  Equiv.ofBijective
    PrimeTensor.Bridge.MulReal.logValue
    logValue_bijective

@[simp]
theorem logEquiv_apply
    (x : PrimeTensor.MulReal) :
    logEquiv x =
      PrimeTensor.Bridge.MulReal.logValue x := by
  rfl

end MulReal

end Bridge
end PrimeTensor
