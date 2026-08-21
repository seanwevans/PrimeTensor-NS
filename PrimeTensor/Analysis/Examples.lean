import PrimeTensor.Analysis.Rules

/-!
# Derived rules and positive-depth powers

This file develops calculus consequences that require no new continuity
assumption.

Positive powers are indexed by `Depth`:
  one        ↦ x
  succ one   ↦ x*x
  succ(succ one) ↦ x*(x*x)
and so on.

There is no zeroth power in the object language.
-/

namespace PrimeTensor

namespace MulReal

/--
Positive-depth power.

The first depth is the value itself; every successor contributes one more
multiplicative copy.
-/
def depthPow (a : MulReal) : Depth → MulReal
  | .one => a
  | .succ d => a * depthPow a d

@[simp] theorem depthPow_one (a : MulReal) :
    depthPow a .one = a := rfl

@[simp] theorem depthPow_succ (a : MulReal) (d : Depth) :
    depthPow a (.succ d) = a * depthPow a d := rfl

end MulReal

namespace MulTangentMap

/-- Tangent-map ratio, built only from product and inversion. -/
def ratio (D E : MulTangentMap) : MulTangentMap :=
  mul D (inv E)

@[simp] theorem ratio_apply (D E : MulTangentMap) (h : MulReal) :
    ratio D E h = D h * (E h)⁻¹ := rfl

/--
Positive-depth power tangent.

At every positive depth it is built recursively from the identity tangent and
the multiplicative product rule.
-/
def depthPow : Depth → MulTangentMap
  | .one => identity
  | .succ d => mul identity (depthPow d)

@[simp] theorem depthPow_one_apply (h : MulReal) :
    depthPow .one h = h := rfl

theorem depthPow_apply (d : Depth) (h : MulReal) :
    depthPow d h = MulReal.depthPow h d := by
  induction d with
  | one =>
      rfl
  | succ d ih =>
      change h * depthPow d h = h * MulReal.depthPow h d
      rw [ih]

end MulTangentMap

namespace MulDifferential

/--
Ratio rule.

The derivative of the multiplicative ratio is the ratio of the tangent
responses.
-/
theorem hasMulDerivativeAt_ratio
    {f g : MulReal → MulReal} {x : MulReal}
    {Df Dg : MulTangentMap}
    (hf : HasMulDerivativeAt f x Df)
    (hg : HasMulDerivativeAt g x Dg) :
    HasMulDerivativeAt
      (fun y => MulReal.ratio (f y) (g y))
      x
      (MulTangentMap.ratio Df Dg) := by
  unfold MulReal.ratio MulTangentMap.ratio
  exact hasMulDerivativeAt_mul hf (hasMulDerivativeAt_inv hg)

/-- The reciprocal map has the inverted identity tangent. -/
theorem hasMulDerivativeAt_reciprocal (x : MulReal) :
    HasMulDerivativeAt
      (fun y => y⁻¹)
      x
      (MulTangentMap.inv MulTangentMap.identity) := by
  exact hasMulDerivativeAt_inv (hasMulDerivativeAt_identity x)

/--
Every positive-depth power has the corresponding positive-depth tangent power.

This is the zero-free analogue of the familiar power family, but there is no
zeroth case to prove or even state.
-/
theorem hasMulDerivativeAt_depthPow (x : MulReal) :
    ∀ d : Depth,
      HasMulDerivativeAt
        (fun y => MulReal.depthPow y d)
        x
        (MulTangentMap.depthPow d)
  | .one => by
      exact hasMulDerivativeAt_identity x
  | .succ d => by
      change
        HasMulDerivativeAt
          (fun y => y * MulReal.depthPow y d)
          x
          (MulTangentMap.mul
            MulTangentMap.identity
            (MulTangentMap.depthPow d))
      exact hasMulDerivativeAt_mul
        (hasMulDerivativeAt_identity x)
        (hasMulDerivativeAt_depthPow x d)

end MulDifferential

end PrimeTensor
