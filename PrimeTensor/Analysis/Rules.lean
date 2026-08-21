import PrimeTensor.Analysis.Near.Laws

/-!
# First multiplicative calculus rules

This file proves product and inversion rules for the intrinsic derivative.

The product rule consumes one scale level when combining two first-order
errors; each input error is therefore requested one refinement deeper.
Inversion preserves intrinsic scale exactly and costs no refinement level.
-/

namespace PrimeTensor

namespace Depth

@[simp] theorem advance_succ (level gain : Depth) :
    advance level (.succ gain) = .succ (advance level gain) := rfl

end Depth

namespace MulReal

/-- Inversion distributes over multiplication on the completed carrier. -/
theorem inv_mul_pair (a b : MulReal) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  change
    Quotient.mk MulAsymptotic.setoid
        (MulCauchyStream.inv (MulCauchyStream.mul x y)) =
      Quotient.mk MulAsymptotic.setoid
        (MulCauchyStream.mul
          (MulCauchyStream.inv x)
          (MulCauchyStream.inv y))
  apply Quotient.sound
  apply MulAsymptotic.of_pointwise
  intro n
  exact MulRat.inv_mul_pair (x.term n) (y.term n)

/-- Four completed factors may be regrouped by commutativity and associativity. -/
theorem mul_four_shuffle (a b c d : MulReal) :
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

/-- Ratio of products is the product of the corresponding ratios. -/
theorem ratio_mul_pair (a b c d : MulReal) :
    ratio (a * c) (b * d) = ratio a b * ratio c d := by
  unfold ratio
  rw [inv_mul_pair]
  exact mul_four_shuffle a c b⁻¹ d⁻¹

/-- Simultaneous inversion reverses the oriented ratio. -/
theorem ratio_inv_pair (a b : MulReal) :
    ratio a⁻¹ b⁻¹ = ratio b a := by
  unfold ratio
  rw [inv_inv]
  exact mul_comm a⁻¹ b

/-- Reversing an oriented ratio is the same as inverting it. -/
theorem ratio_reverse (a b : MulReal) :
    ratio b a = (ratio a b)⁻¹ := by
  unfold ratio
  rw [inv_mul_pair, inv_inv]
  exact mul_comm b a⁻¹

end MulReal

namespace MulTangentMap

/-- Pointwise product of multiplicative tangent morphisms. -/
def mul (D E : MulTangentMap) : MulTangentMap where
  toFun := fun h => D h * E h
  map_one := by
    rw [D.map_one, E.map_one]
    exact MulReal.one_mul 1
  map_mul := by
    intro a b
    rw [D.map_mul, E.map_mul]
    exact MulReal.mul_four_shuffle (D a) (D b) (E a) (E b)
  map_inv := by
    intro a
    rw [D.map_inv, E.map_inv]
    symm
    exact MulReal.inv_mul_pair (D a) (E a)

/-- Pointwise inversion of a multiplicative tangent morphism. -/
def inv (D : MulTangentMap) : MulTangentMap where
  toFun := fun h => (D h)⁻¹
  map_one := by
    rw [D.map_one]
    exact MulReal.inv_one
  map_mul := by
    intro a b
    rw [D.map_mul]
    exact MulReal.inv_mul_pair (D a) (D b)
  map_inv := by
    intro a
    rw [D.map_inv, MulReal.inv_inv]

@[simp] theorem mul_apply (D E : MulTangentMap) (h : MulReal) :
    mul D E h = D h * E h := rfl

@[simp] theorem inv_apply (D : MulTangentMap) (h : MulReal) :
    inv D h = (D h)⁻¹ := rfl

end MulTangentMap

namespace MulDifferential

/--
Products of negligible errors remain negligible.

Because completed multiplication costs one intrinsic scale level, each input
error is requested at one additional refinement depth.
-/
theorem negligible_mul
    {e₁ e₂ base : MulReal.Seq}
    (h₁ : NegligibleRelative e₁ base)
    (h₂ : NegligibleRelative e₂ base) :
    NegligibleRelative (fun n => e₁ n * e₂ n) base := by
  intro gain
  obtain ⟨aAnchor, ha⟩ := h₁ (.succ gain)
  obtain ⟨bAnchor, hb⟩ := h₂ (.succ gain)

  let anchor := Depth.join aAnchor bAnchor
  refine ⟨anchor, ?_⟩
  intro n hn level hbase

  have han : Depth.AtOrAfter aAnchor n :=
    Depth.atOrAfter_trans (Depth.left_atOrAfter aAnchor bAnchor) hn
  have hbn : Depth.AtOrAfter bAnchor n :=
    Depth.atOrAfter_trans (Depth.right_atOrAfter aAnchor bAnchor) hn

  have hea := ha n han level hbase
  have heb := hb n hbn level hbase

  have hprod := MulReal.scaleNear_mul hea heb
  rw [MulReal.one_mul] at hprod
  simpa only [Depth.advance_succ] using hprod

/-- Inversion of a negligible error remains negligible at the same rate. -/
theorem negligible_inv
    {e base : MulReal.Seq}
    (h : NegligibleRelative e base) :
    NegligibleRelative (fun n => (e n)⁻¹) base := by
  intro gain
  obtain ⟨anchor, htail⟩ := h gain
  refine ⟨anchor, ?_⟩
  intro n hn level hbase
  exact MulReal.scaleNear_inv (htail n hn level hbase)

/--
First-order equivalence is closed under pointwise multiplication.
-/
theorem firstOrder_mul
    {base actual₁ model₁ actual₂ model₂ : MulReal.Seq}
    (h₁ : FirstOrderEquivalent base actual₁ model₁)
    (h₂ : FirstOrderEquivalent base actual₂ model₂) :
    FirstOrderEquivalent base
      (fun n => actual₁ n * actual₂ n)
      (fun n => model₁ n * model₂ n) := by
  intro gain
  obtain ⟨anchor, htail⟩ := negligible_mul h₁ h₂ gain
  refine ⟨anchor, ?_⟩
  intro n hn level hbase

  change
    MulReal.ScaleNear (Depth.advance level gain)
      (MulReal.ratio
        (actual₁ n * actual₂ n)
        (model₁ n * model₂ n)) 1

  rw [MulReal.ratio_mul_pair]
  exact htail n hn level hbase

/--
First-order equivalence is closed under simultaneous inversion.
-/
theorem firstOrder_inv
    {base actual model : MulReal.Seq}
    (h : FirstOrderEquivalent base actual model) :
    FirstOrderEquivalent base
      (fun n => (actual n)⁻¹)
      (fun n => (model n)⁻¹) := by
  intro gain
  obtain ⟨anchor, htail⟩ := negligible_inv h gain
  refine ⟨anchor, ?_⟩
  intro n hn level hbase

  change
    MulReal.ScaleNear (Depth.advance level gain)
      (MulReal.ratio (actual n)⁻¹ (model n)⁻¹) 1

  rw [MulReal.ratio_inv_pair, MulReal.ratio_reverse]
  exact htail n hn level hbase

/-- Response of a pointwise product is the product of the response germs. -/
theorem response_mul
    (f g : MulReal → MulReal) (x : MulReal) (h : MulReal.Seq) :
    ∀ n : Depth,
      response (fun y => f y * g y) x h n =
        response f x h n * response g x h n := by
  intro n
  unfold response
  exact MulReal.ratio_mul_pair
    (f (x * h n)) (f x)
    (g (x * h n)) (g x)

/-- Response of a pointwise inverse is the inverse response germ. -/
theorem response_inv
    (f : MulReal → MulReal) (x : MulReal) (h : MulReal.Seq) :
    ∀ n : Depth,
      response (fun y => (f y)⁻¹) x h n =
        (response f x h n)⁻¹ := by
  intro n
  unfold response
  rw [MulReal.ratio_inv_pair, MulReal.ratio_reverse]

/--
Multiplicative product rule.

The tangent model for `f*g` is the pointwise product of the tangent models.
-/
theorem hasMulDerivativeAt_mul
    {f g : MulReal → MulReal} {x : MulReal}
    {Df Dg : MulTangentMap}
    (hf : HasMulDerivativeAt f x Df)
    (hg : HasMulDerivativeAt g x Dg) :
    HasMulDerivativeAt
      (fun y => f y * g y)
      x
      (MulTangentMap.mul Df Dg) := by
  intro h hh

  have hf' := hf h hh
  have hg' := hg h hh
  have hp := firstOrder_mul hf' hg'

  intro gain
  obtain ⟨anchor, htail⟩ := hp gain
  refine ⟨anchor, ?_⟩
  intro n hn level hbase

  change
    MulReal.ScaleNear (Depth.advance level gain)
      (MulReal.ratio
        (response (fun y => f y * g y) x h n)
        (MulTangentMap.mul Df Dg (h n))) 1

  rw [response_mul f g x h n, MulTangentMap.mul_apply]
  exact htail n hn level hbase

/--
Multiplicative inversion rule.

Inverting the output inverts the tangent response.
-/
theorem hasMulDerivativeAt_inv
    {f : MulReal → MulReal} {x : MulReal}
    {D : MulTangentMap}
    (hf : HasMulDerivativeAt f x D) :
    HasMulDerivativeAt
      (fun y => (f y)⁻¹)
      x
      (MulTangentMap.inv D) := by
  intro h hh

  have hi := firstOrder_inv (hf h hh)

  intro gain
  obtain ⟨anchor, htail⟩ := hi gain
  refine ⟨anchor, ?_⟩
  intro n hn level hbase

  change
    MulReal.ScaleNear (Depth.advance level gain)
      (MulReal.ratio
        (response (fun y => (f y)⁻¹) x h n)
        (MulTangentMap.inv D (h n))) 1

  rw [response_inv f x h n, MulTangentMap.inv_apply]
  exact htail n hn level hbase

end MulDifferential

end PrimeTensor
