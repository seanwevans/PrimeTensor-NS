import PrimeTensor.Fluid.Coupling

/-!
# Finite barcode coupling

The nonlinear coupling cannot in general close on `MulRat`: for positive
rational inputs, the intended value `exp(log a * log b)` need not be rational.

So the first intrinsic construction stage extends a bilinear coupling seed on
positive prime multisets to oriented rational barcodes, with values already in
`MulReal`.

Inversion carries orientation.  No signed exponent type, subtraction, additive
identity, or ordinary real logarithm is introduced.
-/

namespace PrimeTensor

namespace PrimeMultiset

/-- Equality of represented magnitudes is equality in the quotient itself. -/
theorem eq_of_eval_eq {a b : PrimeMultiset}
    (h : a.eval = b.eval) : a = b := by
  revert h
  refine Quotient.inductionOn₂ a b ?_
  intro x y hxy
  apply Quotient.sound
  change PrimeBag.Same x y
  exact hxy

end PrimeMultiset

namespace MulReal

/--
Cross-product equality implies equality of oriented multiplicative ratios.
-/
theorem ratio_eq_of_cross
    {a b c d : MulReal}
    (h : a * d = c * b) :
    ratio a b = ratio c d := by
  calc
    ratio a b
        = ratio a b * ratio d d := by
            rw [ratio_self, mul_one]
    _ = ratio (a * d) (b * d) :=
          (ratio_mul_pair a b d d).symm
    _ = ratio (c * b) (b * d) := by
          rw [h]
    _ = ratio c b * ratio b d :=
          ratio_mul_pair c b b d
    _ = ratio c d :=
          (ratio_comp c b d).symm

end MulReal

/--
A zero-free multiplicative homomorphism from positive prime multisets into the
completed multiplicative carrier.
-/
structure PrimeMultisetHom where
  toFun : PrimeMultiset → MulReal
  map_one : toFun 1 = 1
  map_mul : ∀ a b : PrimeMultiset,
    toFun (a * b) = toFun a * toFun b

namespace PrimeMultisetHom

instance : CoeFun PrimeMultisetHom
    (fun _ => PrimeMultiset → MulReal) :=
  ⟨PrimeMultisetHom.toFun⟩

/-- Extend a positive multiset homomorphism across one oriented barcode. -/
def evalRatio
    (F : PrimeMultisetHom)
    (q : PrimeRatio) : MulReal :=
  MulReal.ratio (F q.upper) (F q.lower)

@[simp] theorem evalRatio_one
    (F : PrimeMultisetHom) :
    evalRatio F 1 = 1 := by
  unfold evalRatio
  rw [PrimeRatio.one_upper, PrimeRatio.one_lower,
    F.map_one, MulReal.ratio_self]

/-- Oriented extension preserves multiplication of barcode representatives. -/
theorem evalRatio_mul
    (F : PrimeMultisetHom)
    (a b : PrimeRatio) :
    evalRatio F (a * b) =
      evalRatio F a * evalRatio F b := by
  unfold evalRatio
  change
    MulReal.ratio
        (F (a.upper * b.upper))
        (F (a.lower * b.lower)) =
      MulReal.ratio (F a.upper) (F a.lower) *
        MulReal.ratio (F b.upper) (F b.lower)
  rw [F.map_mul, F.map_mul]
  exact MulReal.ratio_mul_pair
    (F a.upper) (F a.lower)
    (F b.upper) (F b.lower)

/-- Oriented extension sends inversion to inversion. -/
theorem evalRatio_inv
    (F : PrimeMultisetHom)
    (a : PrimeRatio) :
    evalRatio F a⁻¹ = (evalRatio F a)⁻¹ := by
  unfold evalRatio
  change
    MulReal.ratio (F a.lower) (F a.upper) =
      (MulReal.ratio (F a.upper) (F a.lower))⁻¹
  exact MulReal.ratio_reverse
    (F a.upper) (F a.lower)

/--
Oriented extension is invariant under rational cross-product equivalence.
-/
theorem evalRatio_same
    (F : PrimeMultisetHom)
    {a b : PrimeRatio}
    (h : PrimeRatio.Same a b) :
    evalRatio F a = evalRatio F b := by

  have hcross :
      a.upper * b.lower =
        b.upper * a.lower := by
    apply PrimeMultiset.eq_of_eval_eq
    change
      a.upper.eval * b.lower.eval =
        b.upper.eval * a.lower.eval at h
    simpa only [PrimeMultiset.eval_mul] using h

  have hmapped := congrArg F.toFun hcross
  rw [F.map_mul, F.map_mul] at hmapped

  exact MulReal.ratio_eq_of_cross hmapped

end PrimeMultisetHom

/--
Bilinear coupling data on positive prime multisets.

This is the finite barcode seed.  A later layer may reduce this further to
values on individual prime pairs using unique factorization.
-/
structure BarcodeCouplingSeed where
  couple : PrimeMultiset → PrimeMultiset → MulReal

  one_left :
    ∀ b : PrimeMultiset,
      couple 1 b = 1

  one_right :
    ∀ a : PrimeMultiset,
      couple a 1 = 1

  mul_left :
    ∀ a b c : PrimeMultiset,
      couple (a * b) c =
        couple a c * couple b c

  mul_right :
    ∀ a b c : PrimeMultiset,
      couple a (b * c) =
        couple a b * couple a c

namespace BarcodeCouplingSeed

/-- Fix the second barcode: the first slot is a multiplicative homomorphism. -/
def leftSection
    (C : BarcodeCouplingSeed)
    (b : PrimeMultiset) : PrimeMultisetHom where
  toFun := fun a => C.couple a b
  map_one := C.one_left b
  map_mul := fun a₁ a₂ => C.mul_left a₁ a₂ b

/-- Extend the first slot across an oriented rational representative. -/
def orientedLeft
    (C : BarcodeCouplingSeed)
    (a : PrimeRatio)
    (b : PrimeMultiset) : MulReal :=
  (leftSection C b).evalRatio a

/-- First-slot orientation respects rational representative equivalence. -/
theorem orientedLeft_same
    (C : BarcodeCouplingSeed)
    {a a' : PrimeRatio}
    (h : PrimeRatio.Same a a')
    (b : PrimeMultiset) :
    orientedLeft C a b =
      orientedLeft C a' b := by
  exact PrimeMultisetHom.evalRatio_same
    (leftSection C b) h

@[simp] theorem orientedLeft_one_first
    (C : BarcodeCouplingSeed)
    (b : PrimeMultiset) :
    orientedLeft C 1 b = 1 := by
  exact PrimeMultisetHom.evalRatio_one
    (leftSection C b)

@[simp] theorem orientedLeft_one_second
    (C : BarcodeCouplingSeed)
    (a : PrimeRatio) :
    orientedLeft C a 1 = 1 := by
  unfold orientedLeft PrimeMultisetHom.evalRatio leftSection
  change
    MulReal.ratio
      (C.couple a.upper 1)
      (C.couple a.lower 1) = 1
  rw [C.one_right, C.one_right,
    MulReal.ratio_self]

/-- Oriented first-slot coupling remains multiplicative in the second slot. -/
theorem orientedLeft_mul_second
    (C : BarcodeCouplingSeed)
    (a : PrimeRatio)
    (b c : PrimeMultiset) :
    orientedLeft C a (b * c) =
      orientedLeft C a b *
        orientedLeft C a c := by
  unfold orientedLeft PrimeMultisetHom.evalRatio leftSection
  change
    MulReal.ratio
        (C.couple a.upper (b * c))
        (C.couple a.lower (b * c)) =
      MulReal.ratio
          (C.couple a.upper b)
          (C.couple a.lower b) *
        MulReal.ratio
          (C.couple a.upper c)
          (C.couple a.lower c)
  rw [C.mul_right, C.mul_right]
  exact MulReal.ratio_mul_pair
    (C.couple a.upper b)
    (C.couple a.lower b)
    (C.couple a.upper c)
    (C.couple a.lower c)

/-- Fix an oriented first barcode: the second positive slot is a homomorphism. -/
def rightSection
    (C : BarcodeCouplingSeed)
    (a : PrimeRatio) : PrimeMultisetHom where
  toFun := fun b => orientedLeft C a b
  map_one := orientedLeft_one_second C a
  map_mul := orientedLeft_mul_second C a

/--
Coupling of two oriented rational representatives, already valued in the
completion.
-/
def coupleRatio
    (C : BarcodeCouplingSeed)
    (a b : PrimeRatio) : MulReal :=
  (rightSection C a).evalRatio b

@[simp] theorem coupleRatio_one_right
    (C : BarcodeCouplingSeed)
    (a : PrimeRatio) :
    coupleRatio C a 1 = 1 := by
  exact PrimeMultisetHom.evalRatio_one
    (rightSection C a)

@[simp] theorem coupleRatio_one_left
    (C : BarcodeCouplingSeed)
    (b : PrimeRatio) :
    coupleRatio C 1 b = 1 := by
  unfold coupleRatio PrimeMultisetHom.evalRatio rightSection
  change
    MulReal.ratio
      (orientedLeft C 1 b.upper)
      (orientedLeft C 1 b.lower) = 1
  rw [orientedLeft_one_first,
    orientedLeft_one_first,
    MulReal.ratio_self]

/-- Coupling preserves multiplication in the second oriented argument. -/
theorem coupleRatio_mul_right
    (C : BarcodeCouplingSeed)
    (a b c : PrimeRatio) :
    coupleRatio C a (b * c) =
      coupleRatio C a b *
        coupleRatio C a c := by
  exact PrimeMultisetHom.evalRatio_mul
    (rightSection C a) b c

/-- Coupling preserves inversion in the second oriented argument. -/
theorem coupleRatio_inv_right
    (C : BarcodeCouplingSeed)
    (a b : PrimeRatio) :
    coupleRatio C a b⁻¹ =
      (coupleRatio C a b)⁻¹ := by
  exact PrimeMultisetHom.evalRatio_inv
    (rightSection C a) b

/-- Oriented first-slot coupling preserves multiplication of representatives. -/
theorem orientedLeft_mul_first
    (C : BarcodeCouplingSeed)
    (a a' : PrimeRatio)
    (b : PrimeMultiset) :
    orientedLeft C (a * a') b =
      orientedLeft C a b *
        orientedLeft C a' b := by
  exact PrimeMultisetHom.evalRatio_mul
    (leftSection C b) a a'

/-- Coupling preserves multiplication in the first oriented argument. -/
theorem coupleRatio_mul_left
    (C : BarcodeCouplingSeed)
    (a a' b : PrimeRatio) :
    coupleRatio C (a * a') b =
      coupleRatio C a b *
        coupleRatio C a' b := by

  unfold coupleRatio PrimeMultisetHom.evalRatio rightSection

  change
    MulReal.ratio
        (orientedLeft C (a * a') b.upper)
        (orientedLeft C (a * a') b.lower) =
      MulReal.ratio
          (orientedLeft C a b.upper)
          (orientedLeft C a b.lower) *
        MulReal.ratio
          (orientedLeft C a' b.upper)
          (orientedLeft C a' b.lower)

  rw [orientedLeft_mul_first,
    orientedLeft_mul_first]

  exact MulReal.ratio_mul_pair
    (orientedLeft C a b.upper)
    (orientedLeft C a b.lower)
    (orientedLeft C a' b.upper)
    (orientedLeft C a' b.lower)

/-- Coupling preserves inversion in the first oriented argument. -/
theorem coupleRatio_inv_left
    (C : BarcodeCouplingSeed)
    (a b : PrimeRatio) :
    coupleRatio C a⁻¹ b =
      (coupleRatio C a b)⁻¹ := by

  unfold coupleRatio PrimeMultisetHom.evalRatio rightSection

  change
    MulReal.ratio
        (orientedLeft C a⁻¹ b.upper)
        (orientedLeft C a⁻¹ b.lower) =
      (MulReal.ratio
        (orientedLeft C a b.upper)
        (orientedLeft C a b.lower))⁻¹

  have hu := PrimeMultisetHom.evalRatio_inv
    (leftSection C b.upper) a
  have hl := PrimeMultisetHom.evalRatio_inv
    (leftSection C b.lower) a

  change
    orientedLeft C a⁻¹ b.upper =
      (orientedLeft C a b.upper)⁻¹ at hu
  change
    orientedLeft C a⁻¹ b.lower =
      (orientedLeft C a b.lower)⁻¹ at hl

  rw [hu, hl]
  calc
    MulReal.ratio
        (orientedLeft C a b.upper)⁻¹
        (orientedLeft C a b.lower)⁻¹
        =
      MulReal.ratio
        (orientedLeft C a b.lower)
        (orientedLeft C a b.upper) :=
      MulReal.ratio_inv_pair
        (orientedLeft C a b.upper)
        (orientedLeft C a b.lower)
    _ =
      (MulReal.ratio
        (orientedLeft C a b.upper)
        (orientedLeft C a b.lower))⁻¹ := by
      exact MulReal.ratio_reverse
        (orientedLeft C a b.upper)
        (orientedLeft C a b.lower)

/-- Coupling respects equivalence of the first rational representative. -/
theorem coupleRatio_same_left
    (C : BarcodeCouplingSeed)
    {a a' b : PrimeRatio}
    (h : PrimeRatio.Same a a') :
    coupleRatio C a b =
      coupleRatio C a' b := by

  unfold coupleRatio PrimeMultisetHom.evalRatio
  change
    MulReal.ratio
        (orientedLeft C a b.upper)
        (orientedLeft C a b.lower) =
      MulReal.ratio
        (orientedLeft C a' b.upper)
        (orientedLeft C a' b.lower)

  rw [orientedLeft_same C h b.upper,
    orientedLeft_same C h b.lower]

/-- Coupling respects equivalence of the second rational representative. -/
theorem coupleRatio_same_right
    (C : BarcodeCouplingSeed)
    {a b b' : PrimeRatio}
    (h : PrimeRatio.Same b b') :
    coupleRatio C a b =
      coupleRatio C a b' := by
  exact PrimeMultisetHom.evalRatio_same
    (rightSection C a) h

end BarcodeCouplingSeed

/--
Finite rational coupling already lands in the completed carrier.
-/
structure FiniteMulCoupling where
  couple : MulRat → MulRat → MulReal

/-- Law-only bilinearity for the finite rational coupling. -/
structure IsFiniteMulCoupling
    (C : FiniteMulCoupling) : Prop where

  couple_one_left :
    ∀ b : MulRat,
      C.couple 1 b = 1

  couple_one_right :
    ∀ a : MulRat,
      C.couple a 1 = 1

  couple_mul_left :
    ∀ a b c : MulRat,
      C.couple (a * b) c =
        C.couple a c * C.couple b c

  couple_mul_right :
    ∀ a b c : MulRat,
      C.couple a (b * c) =
        C.couple a b * C.couple a c

namespace BarcodeCouplingSeed

/-- Quotient-safe coupling of finite rational barcodes. -/
def toFinite
    (C : BarcodeCouplingSeed) : FiniteMulCoupling where
  couple := fun a b =>
    Quotient.liftOn₂ a b
      (fun x y => coupleRatio C x y)
      (by
        intro a₁ b₁ a₂ b₂ ha hb
        change PrimeRatio.Same a₁ a₂ at ha
        change PrimeRatio.Same b₁ b₂ at hb
        calc
          coupleRatio C a₁ b₁
              = coupleRatio C a₂ b₁ :=
                coupleRatio_same_left C ha
          _ = coupleRatio C a₂ b₂ :=
                coupleRatio_same_right C hb)

/-- The finite extension satisfies both multiplicative bilinearity laws. -/
theorem toFinite_lawful
    (C : BarcodeCouplingSeed) :
    IsFiniteMulCoupling (toFinite C) := by

  constructor

  · intro b
    refine Quotient.inductionOn b ?_
    intro y
    exact coupleRatio_one_left C y

  · intro a
    refine Quotient.inductionOn a ?_
    intro x
    exact coupleRatio_one_right C x

  · intro a b c
    refine Quotient.inductionOn a ?_
    intro x
    refine Quotient.inductionOn b ?_
    intro y
    refine Quotient.inductionOn c ?_
    intro z
    exact coupleRatio_mul_left C x y z

  · intro a b c
    refine Quotient.inductionOn a ?_
    intro x
    refine Quotient.inductionOn b ?_
    intro y
    refine Quotient.inductionOn c ?_
    intro z
    exact coupleRatio_mul_right C x y z

end BarcodeCouplingSeed

end PrimeTensor
