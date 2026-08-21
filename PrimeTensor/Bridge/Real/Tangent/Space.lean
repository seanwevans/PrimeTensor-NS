import PrimeTensor.Bridge.Log.Surjective

/-!
# Native tangent maps as additive endomorphisms of the real line

The previous bridge proves that the canonical completed logarithmic coordinate

    MulReal.logValue : MulReal → ℝ

is bijective, packaged as

    MulReal.logEquiv : MulReal ≃ ℝ.

This file conjugates every native multiplicative tangent morphism through that
equivalence.  No regularity assumption is needed for the algebraic result:

    native multiplication  ↔ real addition
    native pivot           ↔ real zero
    native inversion       ↔ real negation.

Thus every `MulTangentMap` canonically determines an additive endomorphism of
the ordinary real line.

Continuity is deliberately left to the next layer, where the intrinsic
`MulTangentMap.ScaleControlled` hypothesis can be translated through the exact
scale semantics.
-/

namespace PrimeTensor
namespace Bridge

namespace MulReal

/-- The inverse logarithmic coordinate sends ordinary zero to the native pivot. -/
@[simp]
theorem logEquiv_symm_zero :
    PrimeTensor.Bridge.MulReal.logEquiv.symm 0 =
      (1 : PrimeTensor.MulReal) := by

  apply
    PrimeTensor.Bridge.MulReal.logValue_injective

  have hZero :
      PrimeTensor.Bridge.MulReal.logValue
          (
            PrimeTensor.Bridge.MulReal.logEquiv.symm 0
          )
        =
      0 := by

    exact
      PrimeTensor.Bridge.MulReal.logEquiv.apply_symm_apply
        0

  rw [hZero]

  exact
    PrimeTensor.Bridge.MulReal.logValue_one.symm

/--
The inverse logarithmic coordinate sends real addition to native
multiplication.
-/
theorem logEquiv_symm_add
    (a b : ℝ) :
    PrimeTensor.Bridge.MulReal.logEquiv.symm
        (a + b)
      =
    PrimeTensor.Bridge.MulReal.logEquiv.symm a *
      PrimeTensor.Bridge.MulReal.logEquiv.symm b := by

  apply
    PrimeTensor.Bridge.MulReal.logValue_injective

  have hAB :
      PrimeTensor.Bridge.MulReal.logValue
          (
            PrimeTensor.Bridge.MulReal.logEquiv.symm
              (a + b)
          )
        =
      a + b := by

    exact
      PrimeTensor.Bridge.MulReal.logEquiv.apply_symm_apply
        (a + b)

  have hA :
      PrimeTensor.Bridge.MulReal.logValue
          (
            PrimeTensor.Bridge.MulReal.logEquiv.symm a
          )
        =
      a := by

    exact
      PrimeTensor.Bridge.MulReal.logEquiv.apply_symm_apply
        a

  have hB :
      PrimeTensor.Bridge.MulReal.logValue
          (
            PrimeTensor.Bridge.MulReal.logEquiv.symm b
          )
        =
      b := by

    exact
      PrimeTensor.Bridge.MulReal.logEquiv.apply_symm_apply
        b

  rw [
    PrimeTensor.Bridge.MulReal.logValue_mul,
    hAB,
    hA,
    hB
  ]

/--
The inverse logarithmic coordinate sends real negation to native inversion.
-/
theorem logEquiv_symm_neg
    (a : ℝ) :
    PrimeTensor.Bridge.MulReal.logEquiv.symm
        (-a)
      =
    (
      PrimeTensor.Bridge.MulReal.logEquiv.symm a
    )⁻¹ := by

  apply
    PrimeTensor.Bridge.MulReal.logValue_injective

  have hNeg :
      PrimeTensor.Bridge.MulReal.logValue
          (
            PrimeTensor.Bridge.MulReal.logEquiv.symm
              (-a)
          )
        =
      -a := by

    exact
      PrimeTensor.Bridge.MulReal.logEquiv.apply_symm_apply
        (-a)

  have hA :
      PrimeTensor.Bridge.MulReal.logValue
          (
            PrimeTensor.Bridge.MulReal.logEquiv.symm a
          )
        =
      a := by

    exact
      PrimeTensor.Bridge.MulReal.logEquiv.apply_symm_apply
        a

  rw [
    PrimeTensor.Bridge.MulReal.logValue_inv,
    hNeg,
    hA
  ]

end MulReal

namespace MulTangentMap

/--
Conjugate a native multiplicative tangent morphism into an ordinary real map.
-/
noncomputable def realConjugate
    (D : PrimeTensor.MulTangentMap)
    (r : ℝ) : ℝ :=
  PrimeTensor.Bridge.MulReal.logValue
    (
      D
        (
          PrimeTensor.Bridge.MulReal.logEquiv.symm r
        )
    )

/-- The real conjugate fixes additive zero. -/
@[simp]
theorem realConjugate_zero
    (D : PrimeTensor.MulTangentMap) :
    realConjugate D 0 = 0 := by

  unfold realConjugate

  rw [
    PrimeTensor.Bridge.MulReal.logEquiv_symm_zero,
    D.map_one,
    PrimeTensor.Bridge.MulReal.logValue_one
  ]

/-- The real conjugate preserves ordinary addition. -/
theorem realConjugate_add
    (D : PrimeTensor.MulTangentMap)
    (a b : ℝ) :
    realConjugate D (a + b) =
      realConjugate D a +
        realConjugate D b := by

  unfold realConjugate

  rw [
    PrimeTensor.Bridge.MulReal.logEquiv_symm_add,
    D.map_mul,
    PrimeTensor.Bridge.MulReal.logValue_mul
  ]

/-- The real conjugate preserves ordinary negation. -/
theorem realConjugate_neg
    (D : PrimeTensor.MulTangentMap)
    (a : ℝ) :
    realConjugate D (-a) =
      - realConjugate D a := by

  unfold realConjugate

  rw [
    PrimeTensor.Bridge.MulReal.logEquiv_symm_neg,
    D.map_inv,
    PrimeTensor.Bridge.MulReal.logValue_inv
  ]

/--
The canonical additive endomorphism of `ℝ` associated with a native tangent
morphism.
-/
noncomputable def realAdditive
    (D : PrimeTensor.MulTangentMap) :
    ℝ →+ ℝ where

  toFun :=
    realConjugate D

  map_zero' :=
    realConjugate_zero D

  map_add' :=
    realConjugate_add D

@[simp]
theorem realAdditive_apply
    (D : PrimeTensor.MulTangentMap)
    (r : ℝ) :
    realAdditive D r =
      realConjugate D r := by
  rfl

@[simp]
theorem realAdditive_zero
    (D : PrimeTensor.MulTangentMap) :
    realAdditive D 0 = 0 :=
  (realAdditive D).map_zero

theorem realAdditive_add
    (D : PrimeTensor.MulTangentMap)
    (a b : ℝ) :
    realAdditive D (a + b) =
      realAdditive D a +
        realAdditive D b :=
  (realAdditive D).map_add a b

theorem realAdditive_neg
    (D : PrimeTensor.MulTangentMap)
    (a : ℝ) :
    realAdditive D (-a) =
      - realAdditive D a := by

  rw [
    realAdditive_apply,
    realConjugate_neg,
    realAdditive_apply
  ]

/--
Evaluation of the real conjugate on the logarithmic coordinate of a native
point is exactly the logarithmic coordinate of the native tangent response.
-/
theorem realConjugate_logValue
    (D : PrimeTensor.MulTangentMap)
    (x : PrimeTensor.MulReal) :
    realConjugate D
        (
          PrimeTensor.Bridge.MulReal.logValue x
        )
      =
    PrimeTensor.Bridge.MulReal.logValue
      (D x) := by

  unfold realConjugate

  have hInv :
      PrimeTensor.Bridge.MulReal.logEquiv.symm
          (
            PrimeTensor.Bridge.MulReal.logValue x
          )
        =
      x := by

    change
      PrimeTensor.Bridge.MulReal.logEquiv.symm
          (
            PrimeTensor.Bridge.MulReal.logEquiv x
          )
        =
      x

    exact
      PrimeTensor.Bridge.MulReal.logEquiv.symm_apply_apply
        x

  rw [hInv]

end MulTangentMap

end Bridge
end PrimeTensor
