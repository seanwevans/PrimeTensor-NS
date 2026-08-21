import PrimeTensor.Analysis.Derivative

/-!
# Algebraic laws for intrinsic nearness and convergence

This file proves that the completed multiplicative topology is compatible with
the native carrier operations.

Multiplication consumes one intrinsic scale level, exactly mirroring the
finite-barcode refinement theorem.  Inversion preserves scale exactly.
-/

namespace PrimeTensor
namespace MulReal

/--
One finer nearness level for each factor yields the requested nearness level
for their products.
-/
theorem scaleNear_mul {level : Depth} {a a' b b' : MulReal}
    (ha : ScaleNear (.succ level) a a')
    (hb : ScaleNear (.succ level) b b') :
    ScaleNear level (a * b) (a' * b') := by
  obtain ⟨as, as', has, has', aAnchor, haTail⟩ := ha
  obtain ⟨bs, bs', hbs, hbs', bAnchor, hbTail⟩ := hb

  refine ⟨MulCauchyStream.mul as bs,
    MulCauchyStream.mul as' bs', ?_, ?_, ?_⟩

  · rw [← has, ← hbs]
    rfl

  · rw [← has', ← hbs']
    rfl

  · let anchor := Depth.join aAnchor bAnchor
    refine ⟨anchor, ?_⟩
    intro n hn

    have han : Depth.AtOrAfter aAnchor n :=
      Depth.atOrAfter_trans (Depth.left_atOrAfter aAnchor bAnchor) hn
    have hbn : Depth.AtOrAfter bAnchor n :=
      Depth.atOrAfter_trans (Depth.right_atOrAfter aAnchor bAnchor) hn

    exact MulRat.scaleWithin_mul (haTail n han) (hbTail n hbn)

/-- Inversion preserves intrinsic nearness at the same scale. -/
theorem scaleNear_inv {level : Depth} {a b : MulReal}
    (h : ScaleNear level a b) :
    ScaleNear level a⁻¹ b⁻¹ := by
  obtain ⟨as, bs, has, hbs, anchor, htail⟩ := h
  refine ⟨MulCauchyStream.inv as, MulCauchyStream.inv bs, ?_, ?_,
    anchor, ?_⟩

  · rw [← has]
    rfl

  · rw [← hbs]
    rfl

  · intro n hn
    exact MulRat.scaleWithin_inv (htail n hn)

/--
Multiplication of convergent completed sequences is convergent.

As at the finite scale level, multiplication costs one refinement level.
-/
theorem converges_mul {a b : Seq} {x y : MulReal}
    (ha : ConvergesTo a x)
    (hb : ConvergesTo b y) :
    ConvergesTo (fun n => a n * b n) (x * y) := by
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

  exact scaleNear_mul (haTail n han) (hbTail n hbn)

/-- Inversion of a convergent completed sequence is convergent. -/
theorem converges_inv {a : Seq} {x : MulReal}
    (h : ConvergesTo a x) :
    ConvergesTo (fun n => (a n)⁻¹) x⁻¹ := by
  intro level
  obtain ⟨anchor, htail⟩ := h level
  refine ⟨anchor, ?_⟩
  intro n hn
  exact scaleNear_inv (htail n hn)

/-- Multiplicative ratios of convergent sequences converge to the target ratio. -/
theorem converges_ratio {a b : Seq} {x y : MulReal}
    (ha : ConvergesTo a x)
    (hb : ConvergesTo b y) :
    ConvergesTo
      (fun n => ratio (a n) (b n))
      (ratio x y) := by
  unfold ratio
  exact converges_mul ha (converges_inv hb)

end MulReal
end PrimeTensor
