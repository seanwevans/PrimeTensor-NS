import PrimeTensor.Algebra

/-!
# Zero-free multiplicative carrier interface

We deliberately do NOT use Lean's standard `Group` / `CommGroup` classes here.
Those classes carry natural and integer power operations, including zeroth
powers, and a division operation.

This project's object language keeps only:
* the multiplicative pivot `1`,
* multiplication,
* inversion,
* their structural laws.

The operations themselves remain supplied by the carrier; this class is only a
law mixin, so it creates no competing `One`, `Mul`, or `Inv` instances.
-/

namespace PrimeTensor

/--
Laws for a commutative multiplicative carrier with a pivot and inversion,
without additive structure, division, or power operations.
-/
class IsMulCarrier (G : Type*) [One G] [Mul G] [Inv G] : Prop where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  mul_comm : ∀ a b : G, a * b = b * a
  inv_inv : ∀ a : G, (a⁻¹)⁻¹ = a
  mul_inv : ∀ a : G, a * a⁻¹ = 1

namespace IsMulCarrier

variable {G : Type*} [One G] [Mul G] [Inv G] [IsMulCarrier G]

theorem inv_mul (a : G) : a⁻¹ * a = 1 := by
  rw [IsMulCarrier.mul_comm]
  exact IsMulCarrier.mul_inv a

end IsMulCarrier

/-- The finite prime-barcode rationals satisfy the zero-free carrier laws. -/
instance : IsMulCarrier MulRat where
  mul_assoc := MulRat.mul_assoc
  one_mul := MulRat.one_mul
  mul_one := MulRat.mul_one
  mul_comm := MulRat.mul_comm
  inv_inv := MulRat.inv_inv
  mul_inv := MulRat.mul_inv

/-- The intrinsic multiplicative completion satisfies the same laws. -/
instance : IsMulCarrier MulReal where
  mul_assoc := MulReal.mul_assoc
  one_mul := MulReal.one_mul
  mul_one := MulReal.mul_one
  mul_comm := MulReal.mul_comm
  inv_inv := MulReal.inv_inv
  mul_inv := MulReal.mul_inv

namespace MulReal

/-- The finite barcode pivot embeds as the completed pivot. -/
@[simp] theorem ofRat_one : ofRat (1 : MulRat) = (1 : MulReal) := rfl

/-- Finite barcode multiplication is preserved by completion embedding. -/
@[simp] theorem ofRat_mul (a b : MulRat) :
    ofRat (a * b) = ofRat a * ofRat b := by
  change
    Quotient.mk MulAsymptotic.setoid (MulCauchyStream.constant (a * b)) =
      Quotient.mk MulAsymptotic.setoid
        (MulCauchyStream.mul
          (MulCauchyStream.constant a)
          (MulCauchyStream.constant b))
  apply Quotient.sound
  apply MulAsymptotic.of_pointwise
  intro n
  rfl

/-- Finite barcode inversion is preserved by completion embedding. -/
@[simp] theorem ofRat_inv (a : MulRat) :
    ofRat a⁻¹ = (ofRat a)⁻¹ := by
  change
    Quotient.mk MulAsymptotic.setoid (MulCauchyStream.constant a⁻¹) =
      Quotient.mk MulAsymptotic.setoid
        (MulCauchyStream.inv (MulCauchyStream.constant a))
  apply Quotient.sound
  apply MulAsymptotic.of_pointwise
  intro n
  rfl

end MulReal

end PrimeTensor
