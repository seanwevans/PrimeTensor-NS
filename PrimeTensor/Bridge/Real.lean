import PrimeTensor.Fluid.CouplingUFD
import PrimeTensor.Bridge.Rational
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Conventional real semantics for multiplicative barcodes

Semantic bridge only.  Conventional rationals, reals, zero, subtraction,
absolute value, logarithm, and exponential occur only under
`PrimeTensor.Bridge`.

The native multiplicative carrier is unchanged.
-/

namespace PrimeTensor
namespace Bridge

private theorem multiset_eval_pos
    (q : PrimeMultiset) :
    0 < q.eval := by
  refine Quotient.inductionOn q ?_
  intro b
  exact lt_of_lt_of_le
    Nat.zero_lt_one
    (PrimeBag.one_le_eval b)

private theorem multiset_eval_ne_zero_rat
    (q : PrimeMultiset) :
    (q.eval : ℚ) ≠ 0 := by
  have hq : q.eval ≠ 0 :=
    Nat.ne_of_gt (multiset_eval_pos q)
  exact_mod_cast hq

/--
Cross-product-equivalent oriented prime barcodes have the same conventional
rational interpretation.
-/
theorem PrimeRatio.toRat_eq_of_same
    {a b : PrimeRatio}
    (h : PrimeRatio.Same a b) :
    PrimeTensor.Bridge.PrimeRatio.toRat a =
      PrimeTensor.Bridge.PrimeRatio.toRat b := by

  unfold PrimeTensor.Bridge.PrimeRatio.toRat

  field_simp [
    multiset_eval_ne_zero_rat a.lower,
    multiset_eval_ne_zero_rat b.lower
  ]

  change
    a.upper.eval * b.lower.eval =
      b.upper.eval * a.lower.eval at h

  have h' :
      a.upper.eval * b.lower.eval =
        a.lower.eval * b.upper.eval := by
    calc
      a.upper.eval * b.lower.eval =
          b.upper.eval * a.lower.eval := h
      _ = a.lower.eval * b.upper.eval := by
          rw [Nat.mul_comm]

  exact_mod_cast h'

/--
Conventional rational interpretation of quotient-level finite barcodes.
-/
def MulRat.toRat
    (q : PrimeTensor.MulRat) : ℚ :=
  Quotient.liftOn q
    PrimeTensor.Bridge.PrimeRatio.toRat
    (by
      intro a b h
      change PrimeRatio.Same a b at h
      exact PrimeTensor.Bridge.PrimeRatio.toRat_eq_of_same h)

@[simp] theorem MulRat.toRat_one :
    PrimeTensor.Bridge.MulRat.toRat
        (1 : PrimeTensor.MulRat) =
      1 := by
  change
    PrimeTensor.Bridge.PrimeRatio.toRat
        (1 : PrimeRatio) =
      1
  exact PrimeTensor.Bridge.toRat_one

@[simp] theorem MulRat.toRat_mul
    (a b : PrimeTensor.MulRat) :
    PrimeTensor.Bridge.MulRat.toRat (a * b) =
      PrimeTensor.Bridge.MulRat.toRat a *
        PrimeTensor.Bridge.MulRat.toRat b := by

  refine Quotient.inductionOn₂ a b ?_
  intro x y

  change
    PrimeTensor.Bridge.PrimeRatio.toRat (x * y) =
      PrimeTensor.Bridge.PrimeRatio.toRat x *
        PrimeTensor.Bridge.PrimeRatio.toRat y

  exact PrimeTensor.Bridge.toRat_mul x y

@[simp] theorem MulRat.toRat_inv
    (a : PrimeTensor.MulRat) :
    PrimeTensor.Bridge.MulRat.toRat a⁻¹ =
      (PrimeTensor.Bridge.MulRat.toRat a)⁻¹ := by

  refine Quotient.inductionOn a ?_
  intro x

  change
    PrimeTensor.Bridge.PrimeRatio.toRat x⁻¹ =
      (PrimeTensor.Bridge.PrimeRatio.toRat x)⁻¹

  exact PrimeTensor.Bridge.toRat_inv x

/-- Every finite oriented barcode has positive conventional rational value. -/
theorem PrimeRatio.toRat_pos
    (q : PrimeRatio) :
    0 <
      PrimeTensor.Bridge.PrimeRatio.toRat q := by

  unfold PrimeTensor.Bridge.PrimeRatio.toRat

  have hu :
      0 < (q.upper.eval : ℚ) := by
    exact_mod_cast multiset_eval_pos q.upper

  have hl :
      0 < (q.lower.eval : ℚ) := by
    exact_mod_cast multiset_eval_pos q.lower

  exact div_pos hu hl

/-- Every quotient-level finite barcode has positive rational value. -/
theorem MulRat.toRat_pos
    (q : PrimeTensor.MulRat) :
    0 <
      PrimeTensor.Bridge.MulRat.toRat q := by
  refine Quotient.inductionOn q ?_
  intro x
  exact PrimeTensor.Bridge.PrimeRatio.toRat_pos x

/-- Conventional real interpretation of a finite multiplicative barcode. -/
noncomputable def MulRat.toReal
    (q : PrimeTensor.MulRat) : ℝ :=
  ((PrimeTensor.Bridge.MulRat.toRat q : ℚ) : ℝ)

@[simp] theorem MulRat.toReal_one :
    PrimeTensor.Bridge.MulRat.toReal
        (1 : PrimeTensor.MulRat) =
      1 := by
  unfold PrimeTensor.Bridge.MulRat.toReal
  rw [PrimeTensor.Bridge.MulRat.toRat_one]
  exact Rat.cast_one

@[simp] theorem MulRat.toReal_mul
    (a b : PrimeTensor.MulRat) :
    PrimeTensor.Bridge.MulRat.toReal (a * b) =
      PrimeTensor.Bridge.MulRat.toReal a *
        PrimeTensor.Bridge.MulRat.toReal b := by

  unfold PrimeTensor.Bridge.MulRat.toReal
  rw [PrimeTensor.Bridge.MulRat.toRat_mul]
  exact Rat.cast_mul _ _

@[simp] theorem MulRat.toReal_inv
    (a : PrimeTensor.MulRat) :
    PrimeTensor.Bridge.MulRat.toReal a⁻¹ =
      (PrimeTensor.Bridge.MulRat.toReal a)⁻¹ := by

  unfold PrimeTensor.Bridge.MulRat.toReal
  rw [PrimeTensor.Bridge.MulRat.toRat_inv]
  exact Rat.cast_inv _

/-- Finite multiplicative barcodes interpret as strictly positive reals. -/
theorem MulRat.toReal_pos
    (q : PrimeTensor.MulRat) :
    0 <
      PrimeTensor.Bridge.MulRat.toReal q := by

  unfold PrimeTensor.Bridge.MulRat.toReal

  exact Rat.cast_pos_of_pos
    (PrimeTensor.Bridge.MulRat.toRat_pos q)

/-- Conventional real value of one stage of a native Cauchy stream. -/
noncomputable def MulCauchyStream.toRealTerm
    (s : PrimeTensor.MulCauchyStream)
    (n : Depth) : ℝ :=
  PrimeTensor.Bridge.MulRat.toReal (s.term n)

/--
Conventional epsilon-tail convergence, used only inside the semantic bridge.
The sequence remains indexed by positive `Depth`.
-/
def MulCauchyStream.ConvergesReal
    (s : PrimeTensor.MulCauchyStream)
    (x : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ anchor : Depth,
      ∀ n : Depth,
        Depth.AtOrAfter anchor n →
        abs
          (
            PrimeTensor.Bridge.MulCauchyStream.toRealTerm s n -
              x
          ) < ε

/-- Constant native barcode streams converge to their conventional value. -/
theorem MulCauchyStream.convergesReal_constant
    (q : PrimeTensor.MulRat) :
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (PrimeTensor.MulCauchyStream.constant q)
      (PrimeTensor.Bridge.MulRat.toReal q) := by

  intro ε hε
  refine ⟨.one, ?_⟩
  intro n hn

  change
    abs
      (
        PrimeTensor.Bridge.MulRat.toReal q -
          PrimeTensor.Bridge.MulRat.toReal q
      ) < ε

  rw [sub_self, abs_zero]
  exact hε

/-- Conventional target for coupling two prime atoms. -/
noncomputable def PrimePairStreamSeed.logProductTarget
    (p q : Prime) : ℝ :=
  Real.exp
    (
      Real.log (p.value : ℝ) *
        Real.log (q.value : ℝ)
    )

theorem PrimePairStreamSeed.logProductTarget_pos
    (p q : Prime) :
    0 <
      PrimeTensor.Bridge.PrimePairStreamSeed.logProductTarget
        p q := by
  unfold
    PrimeTensor.Bridge.PrimePairStreamSeed.logProductTarget
  exact Real.exp_pos _

theorem PrimePairStreamSeed.logProductTarget_symm
    (p q : Prime) :
    PrimeTensor.Bridge.PrimePairStreamSeed.logProductTarget
        p q =
      PrimeTensor.Bridge.PrimePairStreamSeed.logProductTarget
        q p := by

  unfold
    PrimeTensor.Bridge.PrimePairStreamSeed.logProductTarget

  rw [mul_comm]

/--
A native prime-pair kernel realizes logarithmic multiplication when its
canonical stream converges conventionally to `exp (log p * log q)`.
-/
def PrimePairStreamSeed.RealizesLogProduct
    (K : PrimeTensor.PrimePairStreamSeed) : Prop :=
  ∀ p q : Prime,
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (K.realize p q)
      (
        PrimeTensor.Bridge.PrimePairStreamSeed.logProductTarget
          p q
      )

/-- Conventional target for coupling two finite multiplicative barcodes. -/
noncomputable def finiteLogProductTarget
    (a b : PrimeTensor.MulRat) : ℝ :=
  Real.exp
    (
      Real.log
          (PrimeTensor.Bridge.MulRat.toReal a) *
        Real.log
          (PrimeTensor.Bridge.MulRat.toReal b)
    )

theorem finiteLogProductTarget_pos
    (a b : PrimeTensor.MulRat) :
    0 <
      PrimeTensor.Bridge.finiteLogProductTarget
        a b := by
  unfold PrimeTensor.Bridge.finiteLogProductTarget
  exact Real.exp_pos _

theorem finiteLogProductTarget_symm
    (a b : PrimeTensor.MulRat) :
    PrimeTensor.Bridge.finiteLogProductTarget a b =
      PrimeTensor.Bridge.finiteLogProductTarget b a := by

  unfold PrimeTensor.Bridge.finiteLogProductTarget
  rw [mul_comm]

end Bridge
end PrimeTensor
