import PrimeTensor.Bridge.Scale
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Intrinsic Cauchy proof for the dyadic prime-pair kernel

`Bridge.Approx` constructed explicit native dyadic approximants

    Q_d = floor(T * D_d) / D_d

to

    T = exp(log p * log q),

and proved

    0 <= T - Q_d < 1 / D_d.

`Bridge.Scale` gave an exact conventional interpretation of native
`MulRat.ScaleWithin`.

This file combines the two.  It defines, for every intrinsic scale level, a
real radius `scaleRadius level > 1` whose repeated-square image is exactly `2`.
Eventually every dyadic approximant lies in `(T / scaleRadius level, T]`.
Therefore any two sufficiently late approximants have both directional ratios
strictly below `scaleRadius level`, hence are natively `ScaleWithin level`.

The result is the first concrete `PrimePairStreamSeed` in the project.
-/

namespace PrimeTensor
namespace Bridge

/--
A conventional radius whose native-depth repeated square is exactly the ruler
`2`.
-/
noncomputable def scaleRadius : Depth → ℝ
  | .one => 2
  | .succ d => Real.sqrt (scaleRadius d)

theorem scaleRadius_pos :
    ∀ d : Depth, 0 < scaleRadius d
  | .one => by
      norm_num [scaleRadius]
  | .succ d => by
      change 0 < Real.sqrt (scaleRadius d)
      exact Real.sqrt_pos_of_pos (scaleRadius_pos d)

theorem one_lt_scaleRadius :
    ∀ d : Depth, 1 < scaleRadius d
  | .one => by
      norm_num [scaleRadius]
  | .succ d => by
      change 1 < Real.sqrt (scaleRadius d)
      rw [← Real.sqrt_one]
      exact
        Real.sqrt_lt_sqrt
          (by norm_num)
          (one_lt_scaleRadius d)

/-- Bridge repeated squaring preserves products. -/
theorem realScalePow_mul
    (x y : ℝ) :
    ∀ d : Depth,
      realScalePow (x * y) d =
        realScalePow x d *
          realScalePow y d
  | .one => rfl
  | .succ d => by
      change
        realScalePow (x * y) d *
            realScalePow (x * y) d =
          (realScalePow x d *
              realScalePow x d) *
            (realScalePow y d *
              realScalePow y d)
      rw [realScalePow_mul x y d]
      ring

/-- Bridge repeated squaring preserves nonnegativity. -/
theorem realScalePow_nonneg
    {x : ℝ}
    (hx : 0 ≤ x) :
    ∀ d : Depth,
      0 ≤ realScalePow x d
  | .one => hx
  | .succ d => by
      change
        0 ≤
          realScalePow x d *
            realScalePow x d
      exact
        mul_nonneg
          (realScalePow_nonneg hx d)
          (realScalePow_nonneg hx d)

/-- Bridge repeated squaring preserves strict positivity. -/
theorem realScalePow_pos
    {x : ℝ}
    (hx : 0 < x) :
    ∀ d : Depth,
      0 < realScalePow x d
  | .one => hx
  | .succ d => by
      change
        0 <
          realScalePow x d *
            realScalePow x d
      exact
        mul_pos
          (realScalePow_pos hx d)
          (realScalePow_pos hx d)

/--
Bridge repeated squaring is strictly monotone on the positive real ray.
-/
theorem realScalePow_lt
    {x y : ℝ}
    (hx : 0 < x)
    (hxy : x < y) :
    ∀ d : Depth,
      realScalePow x d <
        realScalePow y d
  | .one => hxy
  | .succ d => by
      change
        realScalePow x d *
            realScalePow x d <
          realScalePow y d *
            realScalePow y d

      have hpow :
          realScalePow x d <
            realScalePow y d :=
        realScalePow_lt hx hxy d

      have hxpow :
          0 <
            realScalePow x d :=
        realScalePow_pos hx d

      nlinarith [
        realScalePow_nonneg
          (le_of_lt <| lt_trans hx hxy)
          d
      ]

/--
The selected radius lands exactly on the conventional ruler `2`.
-/
theorem realScalePow_scaleRadius :
    ∀ d : Depth,
      realScalePow (scaleRadius d) d = 2
  | .one => rfl
  | .succ d => by
      change
        realScalePow
            (Real.sqrt (scaleRadius d)) d *
          realScalePow
            (Real.sqrt (scaleRadius d)) d =
        2

      rw [
        ← realScalePow_mul
          (Real.sqrt (scaleRadius d))
          (Real.sqrt (scaleRadius d))
          d
      ]

      have hr :
          0 ≤ scaleRadius d :=
        le_of_lt (scaleRadius_pos d)

      rw [Real.mul_self_sqrt hr]
      exact realScalePow_scaleRadius d

/--
Any positive conventional ratio below the selected radius is intrinsically
below the ruler after the requested number of repeated squares.
-/
theorem realScalePow_lt_two_of_lt_radius
    {x : ℝ}
    (level : Depth)
    (hx : 0 < x)
    (hxr : x < scaleRadius level) :
    realScalePow x level < 2 := by

  calc
    realScalePow x level
        <
      realScalePow
        (scaleRadius level)
        level :=
      realScalePow_lt hx hxr level
    _ = 2 :=
      realScalePow_scaleRadius level

namespace PrimePairApprox

/--
Bridge-only conversion from a natural counter to a positive native depth.
`0` maps to the first native stage.
-/
def depthOfNat : ℕ → Depth
  | 0 => .one
  | Nat.succ n => .succ (depthOfNat n)

@[simp] theorem precision_depthOfNat :
    ∀ n : ℕ,
      precision (depthOfNat n) =
        n + 1
  | 0 => rfl
  | Nat.succ n => by
      change
        Nat.succ
            (precision (depthOfNat n)) =
          Nat.succ n + 1
      rw [precision_depthOfNat n]

/-- Precision never decreases along a native tail. -/
theorem precision_le_of_atOrAfter
    {a b : Depth}
    (h : Depth.AtOrAfter a b) :
    precision a ≤ precision b := by

  induction h with

  | here =>
      exact le_rfl

  | later h ih =>
      exact
        le_trans ih
          (Nat.le_succ _)

/-- Dyadic denominators never decrease along a native tail. -/
theorem denom_le_of_atOrAfter
    {a b : Depth}
    (h : Depth.AtOrAfter a b) :
    denom a ≤ denom b := by

  unfold denom

  exact
    Nat.pow_le_pow_right
      (by norm_num : 0 < (2 : ℕ))
      (precision_le_of_atOrAfter h)

/-- Cast of the native dyadic denominator into the reals. -/
theorem denom_cast
    (d : Depth) :
    (denom d : ℝ) =
      (2 : ℝ) ^ precision d := by
  simp only [denom, Nat.cast_pow, Nat.cast_ofNat]

/-- Reciprocal dyadic unit expressed as a power of `1/2`. -/
theorem unit_eq_pow
    (d : Depth) :
    1 / (denom d : ℝ) =
      ((1 : ℝ) / 2) ^ precision d := by

  rw [denom_cast]

  calc
    1 / (2 : ℝ) ^ precision d
        =
      (1 : ℝ) ^ precision d /
        (2 : ℝ) ^ precision d := by
          simp
    _ =
      ((1 : ℝ) / 2) ^ precision d :=
        (div_pow (1 : ℝ) 2 (precision d)).symm

/--
Every positive conventional tolerance eventually dominates all later dyadic
units.
-/
theorem eventually_unit_lt
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ anchor : Depth,
      ∀ n : Depth,
        Depth.AtOrAfter anchor n →
        1 / (denom n : ℝ) < ε := by

  obtain ⟨k, hk⟩ :=
    exists_pow_lt_of_lt_one
      hε
      (by norm_num : ((1 : ℝ) / 2) < 1)

  let anchor :=
    depthOfNat k

  refine ⟨anchor, ?_⟩
  intro n hn

  have hprec :
      precision anchor ≤
        precision n :=
    precision_le_of_atOrAfter hn

  have hpow :
      ((1 : ℝ) / 2) ^ precision n ≤
        ((1 : ℝ) / 2) ^ precision anchor := by

    exact
      pow_le_pow_of_le_one
        (by norm_num : 0 ≤ ((1 : ℝ) / 2))
        (by norm_num : ((1 : ℝ) / 2) ≤ 1)
        hprec

  have hanchor :
      ((1 : ℝ) / 2) ^ precision anchor <
        ε := by

    have hprecision :
        precision anchor =
          k + 1 := by
      exact precision_depthOfNat k

    rw [hprecision, pow_succ]

    have hhalf_nonneg :
        0 ≤
          ((1 : ℝ) / 2) ^ k := by
      positivity

    have hstep :
        ((1 : ℝ) / 2) ^ k *
            ((1 : ℝ) / 2) ≤
          ((1 : ℝ) / 2) ^ k := by
      nlinarith

    exact lt_of_le_of_lt hstep hk

  rw [unit_eq_pow]

  exact lt_of_le_of_lt hpow hanchor

/--
The selected multiplicative radius gives a positive additive lower-error
budget around any prime-pair target.
-/
noncomputable def errorBudget
    (p q : Prime)
    (level : Depth) : ℝ :=
  target p q *
      (scaleRadius level - 1) /
    scaleRadius level

theorem errorBudget_pos
    (p q : Prime)
    (level : Depth) :
    0 < errorBudget p q level := by

  unfold errorBudget

  exact
    div_pos
      (mul_pos
        (target_pos p q)
        (sub_pos.mpr
          (one_lt_scaleRadius level)))
      (scaleRadius_pos level)

/--
Algebraic identity behind the lower multiplicative interval:
`T - budget = T / radius`.
-/
theorem target_sub_errorBudget
    (p q : Prime)
    (level : Depth) :
    target p q -
        errorBudget p q level =
      target p q /
        scaleRadius level := by

  unfold errorBudget

  field_simp [
    ne_of_gt
      (scaleRadius_pos level)
  ]

  ring

/--
Every sufficiently late dyadic approximant lies strictly above
`T / scaleRadius level`.
-/
theorem eventually_target_div_radius_lt_term
    (p q : Prime)
    (level : Depth) :
    ∃ anchor : Depth,
      ∀ n : Depth,
        Depth.AtOrAfter anchor n →
        target p q /
            scaleRadius level <
          PrimeTensor.Bridge.MulRat.toReal
            (term p q n) := by

  obtain ⟨anchor, hunit⟩ :=
    eventually_unit_lt
      (errorBudget_pos p q level)

  refine ⟨anchor, ?_⟩
  intro n hn

  have herr :
      target p q -
          PrimeTensor.Bridge.MulRat.toReal
            (term p q n) <
        errorBudget p q level :=
    lt_trans
      (error_lt_unit p q n)
      (hunit n hn)

  have hlower :
      target p q -
          errorBudget p q level <
        PrimeTensor.Bridge.MulRat.toReal
          (term p q n) := by
    linarith

  rw [target_sub_errorBudget p q level] at hlower

  exact hlower

/--
The concrete dyadic prime-pair stream is Cauchy in the native intrinsic scale.
-/
theorem stream_cauchy
    (p q : Prime) :
    PrimeTensor.IsMulCauchy
      (stream p q) := by

  intro level

  obtain ⟨anchor, hlower⟩ :=
    eventually_target_div_radius_lt_term
      p q level

  refine ⟨anchor, ?_⟩
  intro m n hm hn

  apply
    (
      PrimeTensor.Bridge.MulRat.scaleWithin_iff_real
        level
        (term p q m)
        (term p q n)
    ).mpr

  let A :=
    PrimeTensor.Bridge.MulRat.toReal
      (term p q m)

  let B :=
    PrimeTensor.Bridge.MulRat.toReal
      (term p q n)

  let T := target p q
  let R := scaleRadius level

  have hApos : 0 < A := by
    unfold A
    exact
      PrimeTensor.Bridge.MulRat.toReal_pos
        (term p q m)

  have hBpos : 0 < B := by
    unfold B
    exact
      PrimeTensor.Bridge.MulRat.toReal_pos
        (term p q n)

  have hRpos : 0 < R := by
    unfold R
    exact scaleRadius_pos level

  have hAupper : A ≤ T := by
    unfold A T
    exact term_le_target p q m

  have hBupper : B ≤ T := by
    unfold B T
    exact term_le_target p q n

  have hAlower : T / R < A := by
    unfold A T R
    exact hlower m hm

  have hBlower : T / R < B := by
    unfold B T R
    exact hlower n hn

  have hT_lt_RB : T < R * B := by
    have h :=
      (div_lt_iff₀ hRpos).mp hBlower
    nlinarith [mul_comm R B]

  have hT_lt_RA : T < R * A := by
    have h :=
      (div_lt_iff₀ hRpos).mp hAlower
    nlinarith [mul_comm R A]

  have hAB :
      A / B < R := by
    apply (div_lt_iff₀ hBpos).mpr
    exact lt_of_le_of_lt
      hAupper hT_lt_RB

  have hBA :
      B / A < R := by
    apply (div_lt_iff₀ hApos).mpr
    exact lt_of_le_of_lt
      hBupper hT_lt_RA

  constructor

  · exact
      realScalePow_lt_two_of_lt_radius
        level
        (div_pos hApos hBpos)
        hAB

  · exact
      realScalePow_lt_two_of_lt_radius
        level
        (div_pos hBpos hApos)
        hBA

/-- First concrete native Cauchy stream for one prime pair. -/
noncomputable def cauchyStream
    (p q : Prime) :
    PrimeTensor.MulCauchyStream where

  term :=
    stream p q

  cauchy :=
    stream_cauchy p q

/--
The dyadic kernel: the first concrete `PrimePairStreamSeed` in the project.
-/
noncomputable def kernel :
    PrimeTensor.PrimePairStreamSeed where
  realize :=
    cauchyStream

/--
The concrete prime-pair stream also converges to its intended conventional
log-product target.
-/
theorem cauchyStream_convergesReal
    (p q : Prime) :
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (cauchyStream p q)
      (
        PrimeTensor.Bridge.PrimePairStreamSeed.logProductTarget
          p q
      ) := by

  intro ε hε

  obtain ⟨anchor, hunit⟩ :=
    eventually_unit_lt hε

  refine ⟨anchor, ?_⟩
  intro n hn

  change
    abs
      (
        PrimeTensor.Bridge.MulRat.toReal
            (term p q n) -
          target p q
      ) <
    ε

  exact
    lt_trans
      (abs_error_lt_unit p q n)
      (hunit n hn)

/--
The concrete kernel realizes the intended semantic multiplication of logarithmic
coordinates.
-/
theorem kernel_realizesLogProduct :
    PrimeTensor.Bridge.PrimePairStreamSeed.RealizesLogProduct
      kernel := by

  intro p q

  exact
    cauchyStream_convergesReal p q

end PrimePairApprox
end Bridge
end PrimeTensor
