import PrimeTensor.Analysis.Limit

/-!
# Multiplicative differential germs

The multiplicative derivative is not introduced by translating the additive
difference quotient.  Instead, a perturbation is a completed multiplicative
magnitude tending to the pivot `1`, and a function is observed through its
response ratio

    f (x * h) / f x.

A first-order model is a multiplicative tangent map.  Its error is required to
become arbitrarily many intrinsic scale levels finer than the perturbation
itself.

No subtraction, additive zero, zeroth index, or additive epsilon is used.
-/

namespace PrimeTensor

namespace Depth

/--
Advance an intrinsic scale by a positive refinement depth.

There is deliberately no "advance by zero": `.one` means one refinement.
-/
def advance : Depth → Depth → Depth
  | level, .one => .succ level
  | level, .succ gain => .succ (advance level gain)

end Depth

namespace MulReal

/-- Multiplicative ratio in the completed carrier. -/
def ratio (a b : MulReal) : MulReal :=
  a * b⁻¹

@[simp] theorem ratio_self (a : MulReal) :
    ratio a a = 1 := by
  unfold ratio
  exact mul_inv a

/-- Inversion fixes the completed multiplicative pivot. -/
@[simp] theorem inv_one : ((1 : MulReal)⁻¹) = 1 := by
  have h := mul_inv (1 : MulReal)
  rw [one_mul] at h
  exact h

/-- A perturbation of `x` by `h`, followed by comparison with `x`, returns `h`. -/
theorem ratio_mul_base (x h : MulReal) :
    ratio (x * h) x = h := by
  unfold ratio
  calc
    (x * h) * x⁻¹
        = h * (x * x⁻¹) := by
          rw [mul_comm x h]
          exact mul_assoc h x x⁻¹
    _ = h * 1 := by rw [mul_inv x]
    _ = h := mul_one h

end MulReal

/--
A tangent map is a morphism of the native multiplicative carrier.

It has no additive linear structure and no power operation.
-/
structure MulTangentMap where
  toFun : MulReal → MulReal
  map_one : toFun 1 = 1
  map_mul : ∀ a b : MulReal, toFun (a * b) = toFun a * toFun b
  map_inv : ∀ a : MulReal, toFun a⁻¹ = (toFun a)⁻¹

namespace MulTangentMap

instance : CoeFun MulTangentMap (fun _ => MulReal → MulReal) :=
  ⟨MulTangentMap.toFun⟩

/-- Identity tangent morphism. -/
def identity : MulTangentMap where
  toFun := fun h => h
  map_one := rfl
  map_mul := by
    intro a b
    rfl
  map_inv := by
    intro a
    rfl

/-- Trivial tangent morphism, sending every perturbation to the pivot. -/
def trivial : MulTangentMap where
  toFun := fun _ => 1
  map_one := rfl
  map_mul := by
    intro a b
    symm
    exact MulReal.one_mul 1
  map_inv := by
    intro a
    symm
    exact MulReal.inv_one

@[simp] theorem identity_apply (h : MulReal) :
    identity h = h := rfl

@[simp] theorem trivial_apply (h : MulReal) :
    trivial h = 1 := rfl

end MulTangentMap

namespace MulDifferential

/-- A perturbation germ approaches the multiplicative pivot. -/
def ApproachesPivot (h : MulReal.Seq) : Prop :=
  MulReal.ConvergesTo h 1

/--
The response germ of `f` at `x` along a multiplicative perturbation `h`.

Each term records the output ratio created by replacing `x` with `x * h n`.
-/
def response (f : MulReal → MulReal) (x : MulReal)
    (h : MulReal.Seq) : MulReal.Seq :=
  fun n => MulReal.ratio (f (x * h n)) (f x)

/--
`error` is negligible relative to `base` when, eventually, every scale reached
by `base` forces `error` to lie an arbitrarily prescribed positive number of
scale refinements deeper.

This is the intrinsic scale analogue of a little-o relation.
-/
def NegligibleRelative (error base : MulReal.Seq) : Prop :=
  ∀ gain : Depth,
    ∃ anchor : Depth,
      ∀ n : Depth,
        Depth.AtOrAfter anchor n →
        ∀ level : Depth,
          MulReal.ScaleNear level (base n) 1 →
          MulReal.ScaleNear (Depth.advance level gain) (error n) 1

/--
Two response germs agree to first order relative to a perturbation when their
multiplicative error ratio is negligible relative to that perturbation.
-/
def FirstOrderEquivalent
    (base actual model : MulReal.Seq) : Prop :=
  NegligibleRelative
    (fun n => MulReal.ratio (actual n) (model n))
    base

/--
`D` is a multiplicative derivative of `f` at `x` when it models every
pivot-approaching perturbation to first order.
-/
def HasMulDerivativeAt
    (f : MulReal → MulReal) (x : MulReal) (D : MulTangentMap) : Prop :=
  ∀ h : MulReal.Seq,
    ApproachesPivot h →
    FirstOrderEquivalent h
      (response f x h)
      (fun n => D (h n))

/-- Exact agreement of actual and model germs is automatically first-order. -/
theorem firstOrder_of_exact
    {base actual model : MulReal.Seq}
    (h : ∀ n : Depth, actual n = model n) :
    FirstOrderEquivalent base actual model := by
  intro gain
  refine ⟨.one, ?_⟩
  intro n hn level hbase
  have hr :
      MulReal.ratio (actual n) (model n) = 1 := by
    rw [h n]
    exact MulReal.ratio_self (model n)
  change
    MulReal.ScaleNear (Depth.advance level gain)
      (MulReal.ratio (actual n) (model n)) 1
  rw [hr]
  exact MulReal.scaleNear_refl (Depth.advance level gain) 1

/-- The identity function has the identity multiplicative derivative. -/
theorem hasMulDerivativeAt_identity (x : MulReal) :
    HasMulDerivativeAt (fun y => y) x MulTangentMap.identity := by
  intro h hh
  apply firstOrder_of_exact
  intro n
  change MulReal.ratio (x * h n) x = h n
  exact MulReal.ratio_mul_base x (h n)

/-- Every constant function has the trivial multiplicative derivative. -/
theorem hasMulDerivativeAt_constant (c x : MulReal) :
    HasMulDerivativeAt (fun _ => c) x MulTangentMap.trivial := by
  intro h hh
  apply firstOrder_of_exact
  intro n
  change MulReal.ratio c c = 1
  exact MulReal.ratio_self c

end MulDifferential

end PrimeTensor
