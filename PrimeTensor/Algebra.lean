import PrimeTensor.Completion

/-!
# Multiplicative algebra on the completed carrier

This file lifts multiplication and inversion from `MulRat` to intrinsic Cauchy
streams and then through asymptotic equivalence to `MulReal`.

No additive operation, additive identity, subtraction, ordinary rational
coefficient, or ordinary real coefficient is introduced.
-/

namespace PrimeTensor

namespace MulRat

/-- Inversion distributes over multiplication in the finite barcode quotient. -/
theorem inv_mul_pair (a b : MulRat) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  change
    Quotient.mk PrimeRatio.setoid ((x * y)⁻¹) =
      Quotient.mk PrimeRatio.setoid (x⁻¹ * y⁻¹)
  rfl

/-- Inversion fixes the multiplicative pivot. -/
@[simp] theorem inv_one : ((1 : MulRat)⁻¹) = 1 := by
  change
    Quotient.mk PrimeRatio.setoid ((1 : PrimeRatio)⁻¹) =
      Quotient.mk PrimeRatio.setoid (1 : PrimeRatio)
  rfl

/-- Four factors may be regrouped by commutativity and associativity. -/
private theorem mul_four_shuffle (a b c d : MulRat) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  calc
    (a * b) * (c * d)
        = a * (b * (c * d)) := mul_assoc a b (c * d)
    _ = a * ((b * c) * d) := by
      rw [← mul_assoc b c d]
    _ = a * ((c * b) * d) := by
      rw [mul_comm b c]
    _ = a * (c * (b * d)) := by
      rw [mul_assoc c b d]
    _ = (a * c) * (b * d) := (mul_assoc a c (b * d)).symm

/-- Ratio of two products is the product of the corresponding ratios. -/
theorem ratio_mul_pair (a b c d : MulRat) :
    ratio (a * c) (b * d) = ratio a b * ratio c d := by
  unfold ratio
  rw [inv_mul_pair]
  exact mul_four_shuffle a c b⁻¹ d⁻¹

/-- Inverting both endpoints reverses the oriented ratio. -/
theorem ratio_inv_pair (a b : MulRat) :
    ratio a⁻¹ b⁻¹ = ratio b a := by
  unfold ratio
  rw [inv_inv]
  exact mul_comm a⁻¹ b

/--
One finer scale for each factor gives the requested scale for their products.
-/
theorem scaleWithin_mul {level : Depth} {a b c d : MulRat}
    (hab : ScaleWithin (.succ level) a b)
    (hcd : ScaleWithin (.succ level) c d) :
    ScaleWithin level (a * c) (b * d) := by
  unfold ScaleWithin at hab hcd ⊢

  have habForward :
      scalePow (ratio a b) level * scalePow (ratio a b) level < two := by
    simpa [scalePow] using hab.1
  have hcdForward :
      scalePow (ratio c d) level * scalePow (ratio c d) level < two := by
    simpa [scalePow] using hcd.1
  have habBackward :
      scalePow (ratio b a) level * scalePow (ratio b a) level < two := by
    simpa [scalePow] using hab.2
  have hcdBackward :
      scalePow (ratio d c) level * scalePow (ratio d c) level < two := by
    simpa [scalePow] using hcd.2

  constructor
  · rw [ratio_mul_pair a b c d, scalePow_mul]
    exact mul_lt_two_of_sq_lt_two habForward hcdForward
  · rw [ratio_mul_pair b a d c, scalePow_mul]
    exact mul_lt_two_of_sq_lt_two habBackward hcdBackward

/-- Inversion preserves intrinsic multiplicative scale exactly. -/
theorem scaleWithin_inv {level : Depth} {a b : MulRat}
    (h : ScaleWithin level a b) :
    ScaleWithin level a⁻¹ b⁻¹ := by
  unfold ScaleWithin at h ⊢
  rw [ratio_inv_pair a b, ratio_inv_pair b a]
  exact ⟨h.2, h.1⟩

end MulRat

namespace MulCauchyStream

/-- Pointwise multiplication of intrinsic Cauchy streams. -/
def mul (a b : MulCauchyStream) : MulCauchyStream where
  term := fun n => a.term n * b.term n
  cauchy := by
    intro level
    obtain ⟨aAnchor, ha⟩ := a.cauchy (.succ level)
    obtain ⟨bAnchor, hb⟩ := b.cauchy (.succ level)
    let anchor := Depth.join aAnchor bAnchor
    refine ⟨anchor, ?_⟩
    intro m n hm hn
    have ham : Depth.AtOrAfter aAnchor m :=
      Depth.atOrAfter_trans (Depth.left_atOrAfter aAnchor bAnchor) hm
    have han : Depth.AtOrAfter aAnchor n :=
      Depth.atOrAfter_trans (Depth.left_atOrAfter aAnchor bAnchor) hn
    have hbm : Depth.AtOrAfter bAnchor m :=
      Depth.atOrAfter_trans (Depth.right_atOrAfter aAnchor bAnchor) hm
    have hbn : Depth.AtOrAfter bAnchor n :=
      Depth.atOrAfter_trans (Depth.right_atOrAfter aAnchor bAnchor) hn
    exact MulRat.scaleWithin_mul (ha m n ham han) (hb m n hbm hbn)

/-- Pointwise inversion of an intrinsic Cauchy stream. -/
def inv (a : MulCauchyStream) : MulCauchyStream where
  term := fun n => (a.term n)⁻¹
  cauchy := by
    intro level
    obtain ⟨anchor, ha⟩ := a.cauchy level
    refine ⟨anchor, ?_⟩
    intro m n hm hn
    exact MulRat.scaleWithin_inv (ha m n hm hn)

@[simp] theorem mul_term (a b : MulCauchyStream) (n : Depth) :
    (mul a b).term n = a.term n * b.term n := rfl

@[simp] theorem inv_term (a : MulCauchyStream) (n : Depth) :
    (inv a).term n = (a.term n)⁻¹ := rfl

end MulCauchyStream

namespace MulAsymptotic

/-- Pointwise equality implies asymptotic equivalence. -/
theorem of_pointwise {a b : MulCauchyStream}
    (h : ∀ n : Depth, a.term n = b.term n) :
    MulAsymptotic a b := by
  intro level
  refine ⟨.one, ?_⟩
  intro n hn
  rw [h n]
  exact MulRat.scaleWithin_refl level (b.term n)

/-- Asymptotic equivalence is compatible with pointwise multiplication. -/
theorem mul {a a' b b' : MulCauchyStream}
    (ha : MulAsymptotic a a')
    (hb : MulAsymptotic b b') :
    MulAsymptotic (MulCauchyStream.mul a b)
      (MulCauchyStream.mul a' b') := by
  intro level
  obtain ⟨aAnchor, haTail⟩ := ha (.succ level)
  obtain ⟨bAnchor, hbTail⟩ := hb (.succ level)
  let anchor := Depth.join aAnchor bAnchor
  refine ⟨anchor, ?_⟩
  intro n hn
  have han : Depth.AtOrAfter aAnchor n :=
    Depth.atOrAfter_trans (Depth.left_atOrAfter aAnchor bAnchor) hn
  have hbn : Depth.AtOrAfter bAnchor n :=
    Depth.atOrAfter_trans (Depth.right_atOrAfter aAnchor bAnchor) hn
  exact MulRat.scaleWithin_mul (haTail n han) (hbTail n hbn)

/-- Asymptotic equivalence is compatible with pointwise inversion. -/
theorem inv {a b : MulCauchyStream}
    (h : MulAsymptotic a b) :
    MulAsymptotic (MulCauchyStream.inv a) (MulCauchyStream.inv b) := by
  intro level
  obtain ⟨anchor, hTail⟩ := h level
  refine ⟨anchor, ?_⟩
  intro n hn
  exact MulRat.scaleWithin_inv (hTail n hn)

end MulAsymptotic

namespace MulReal

/-- Multiplication induced by pointwise stream multiplication. -/
def mul (a b : MulReal) : MulReal :=
  Quotient.liftOn₂ a b
    (fun x y => ofStream (MulCauchyStream.mul x y))
    (by
      intro a₁ b₁ a₂ b₂ ha hb
      change MulAsymptotic a₁ a₂ at ha
      change MulAsymptotic b₁ b₂ at hb
      change
        Quotient.mk MulAsymptotic.setoid (MulCauchyStream.mul a₁ b₁) =
          Quotient.mk MulAsymptotic.setoid (MulCauchyStream.mul a₂ b₂)
      apply Quotient.sound
      exact MulAsymptotic.mul ha hb)

/-- Inversion induced by pointwise stream inversion. -/
def inv (a : MulReal) : MulReal :=
  Quotient.liftOn a
    (fun x => ofStream (MulCauchyStream.inv x))
    (by
      intro a b h
      change MulAsymptotic a b at h
      change
        Quotient.mk MulAsymptotic.setoid (MulCauchyStream.inv a) =
          Quotient.mk MulAsymptotic.setoid (MulCauchyStream.inv b)
      apply Quotient.sound
      exact MulAsymptotic.inv h)

instance : Mul MulReal := ⟨mul⟩
instance : Inv MulReal := ⟨inv⟩

@[simp] theorem one_mul (a : MulReal) : (1 : MulReal) * a = a := by
  refine Quotient.inductionOn a ?_
  intro x
  change
    Quotient.mk MulAsymptotic.setoid
        (MulCauchyStream.mul (MulCauchyStream.constant 1) x) =
      Quotient.mk MulAsymptotic.setoid x
  apply Quotient.sound
  apply MulAsymptotic.of_pointwise
  intro n
  change (1 : MulRat) * x.term n = x.term n
  exact MulRat.one_mul _

@[simp] theorem mul_one (a : MulReal) : a * (1 : MulReal) = a := by
  refine Quotient.inductionOn a ?_
  intro x
  change
    Quotient.mk MulAsymptotic.setoid
        (MulCauchyStream.mul x (MulCauchyStream.constant 1)) =
      Quotient.mk MulAsymptotic.setoid x
  apply Quotient.sound
  apply MulAsymptotic.of_pointwise
  intro n
  change x.term n * (1 : MulRat) = x.term n
  exact MulRat.mul_one _

theorem mul_assoc (a b c : MulReal) :
    (a * b) * c = a * (b * c) := by
  refine Quotient.inductionOn a ?_
  intro x
  refine Quotient.inductionOn b ?_
  intro y
  refine Quotient.inductionOn c ?_
  intro z
  change
    Quotient.mk MulAsymptotic.setoid
        (MulCauchyStream.mul (MulCauchyStream.mul x y) z) =
      Quotient.mk MulAsymptotic.setoid
        (MulCauchyStream.mul x (MulCauchyStream.mul y z))
  apply Quotient.sound
  apply MulAsymptotic.of_pointwise
  intro n
  exact MulRat.mul_assoc (x.term n) (y.term n) (z.term n)

theorem mul_comm (a b : MulReal) : a * b = b * a := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  change
    Quotient.mk MulAsymptotic.setoid (MulCauchyStream.mul x y) =
      Quotient.mk MulAsymptotic.setoid (MulCauchyStream.mul y x)
  apply Quotient.sound
  apply MulAsymptotic.of_pointwise
  intro n
  exact MulRat.mul_comm (x.term n) (y.term n)

@[simp] theorem inv_inv (a : MulReal) : (a⁻¹)⁻¹ = a := by
  refine Quotient.inductionOn a ?_
  intro x
  change
    Quotient.mk MulAsymptotic.setoid
        (MulCauchyStream.inv (MulCauchyStream.inv x)) =
      Quotient.mk MulAsymptotic.setoid x
  apply Quotient.sound
  apply MulAsymptotic.of_pointwise
  intro n
  exact MulRat.inv_inv (x.term n)

@[simp] theorem mul_inv (a : MulReal) : a * a⁻¹ = 1 := by
  refine Quotient.inductionOn a ?_
  intro x
  change
    Quotient.mk MulAsymptotic.setoid
        (MulCauchyStream.mul x (MulCauchyStream.inv x)) =
      Quotient.mk MulAsymptotic.setoid (MulCauchyStream.constant 1)
  apply Quotient.sound
  apply MulAsymptotic.of_pointwise
  intro n
  change x.term n * (x.term n)⁻¹ = (1 : MulRat)
  exact MulRat.mul_inv (x.term n)

@[simp] theorem inv_mul (a : MulReal) : a⁻¹ * a = 1 := by
  rw [mul_comm]
  exact mul_inv a

end MulReal

end PrimeTensor
