import PrimeTensor.Bridge.MulReal.Derivative.Semantics

/-!
# The logarithmic coordinate image as the native real tangent space

`MulReal.logValue` is already injective and converts native multiplication,
inversion, and the pivot into ordinary addition, negation, and zero.

Surjectivity onto all of `ℝ` has not yet been proved.  This file therefore
does not assume it.  Instead it isolates the exact coordinate space already
available:

    LogImage = range MulReal.logValue.

Because `logValue` is injective, every point of `LogImage` has a unique native
preimage.  We package the resulting equivalence

    MulReal ≃ LogImage

and transport the native multiplicative operations across it.  Every native
`MulTangentMap` then conjugates to an additive endomorphism of this logarithmic
coordinate image.

A later density/completion theorem may identify `LogImage` with all of `ℝ`
without changing any of the results here.
-/

namespace PrimeTensor
namespace Bridge

/-- The exact real-coordinate image of the completed multiplicative carrier. -/
abbrev LogImage :=
  {
    r : ℝ //
      r ∈
        Set.range
          PrimeTensor.Bridge.MulReal.logValue
  }

namespace LogImage

/-- Embed a completed multiplicative real into its canonical log coordinate. -/
noncomputable def ofMulReal
    (x : PrimeTensor.MulReal) :
    PrimeTensor.Bridge.LogImage :=
  ⟨
    PrimeTensor.Bridge.MulReal.logValue x,
    ⟨x, rfl⟩
  ⟩

/--
Recover the unique native completed point represented by a logarithmic image
coordinate.
-/
noncomputable def toMulReal
    (z : PrimeTensor.Bridge.LogImage) :
    PrimeTensor.MulReal :=
  Classical.choose z.property

@[simp]
theorem logValue_toMulReal
    (z : PrimeTensor.Bridge.LogImage) :
    PrimeTensor.Bridge.MulReal.logValue
        (toMulReal z)
      =
    z.1 := by

  exact Classical.choose_spec z.property

@[simp]
theorem toMulReal_ofMulReal
    (x : PrimeTensor.MulReal) :
    toMulReal (ofMulReal x) = x := by

  apply
    PrimeTensor.Bridge.MulReal.logValue_injective

  rw [
    logValue_toMulReal
  ]

  rfl

@[simp]
theorem ofMulReal_toMulReal
    (z : PrimeTensor.Bridge.LogImage) :
    ofMulReal (toMulReal z) = z := by

  apply Subtype.ext

  exact logValue_toMulReal z

/--
The completed carrier and its exact logarithmic coordinate image are
equivalent.
-/
noncomputable def equiv :
    PrimeTensor.MulReal ≃
      PrimeTensor.Bridge.LogImage where

  toFun := ofMulReal
  invFun := toMulReal
  left_inv := toMulReal_ofMulReal
  right_inv := ofMulReal_toMulReal

/-- Coordinate pivot.  Its underlying real value is zero. -/
noncomputable def zero :
    PrimeTensor.Bridge.LogImage :=
  ofMulReal 1

/--
Coordinate addition transported from intrinsic multiplication.
-/
noncomputable def add
    (a b : PrimeTensor.Bridge.LogImage) :
    PrimeTensor.Bridge.LogImage :=
  ofMulReal
    (
      toMulReal a *
        toMulReal b
    )

/--
Coordinate negation transported from intrinsic inversion.
-/
noncomputable def neg
    (a : PrimeTensor.Bridge.LogImage) :
    PrimeTensor.Bridge.LogImage :=
  ofMulReal
    (
      (toMulReal a)⁻¹
    )

@[simp]
theorem zero_val :
    (zero : PrimeTensor.Bridge.LogImage).1 = 0 := by

  unfold zero
  unfold ofMulReal

  exact
    PrimeTensor.Bridge.MulReal.logValue_one

@[simp]
theorem add_val
    (a b : PrimeTensor.Bridge.LogImage) :
    (add a b).1 =
      a.1 + b.1 := by

  change
    PrimeTensor.Bridge.MulReal.logValue
        (
          toMulReal a *
            toMulReal b
        )
      =
    a.1 + b.1

  rw [
    PrimeTensor.Bridge.MulReal.logValue_mul,
    logValue_toMulReal,
    logValue_toMulReal
  ]

@[simp]
theorem neg_val
    (a : PrimeTensor.Bridge.LogImage) :
    (neg a).1 =
      - a.1 := by

  change
    PrimeTensor.Bridge.MulReal.logValue
        (
          (toMulReal a)⁻¹
        )
      =
    - a.1

  rw [
    PrimeTensor.Bridge.MulReal.logValue_inv,
    logValue_toMulReal
  ]

@[simp]
theorem toMulReal_zero :
    toMulReal zero = 1 := by

  unfold zero

  exact toMulReal_ofMulReal 1

@[simp]
theorem toMulReal_add
    (a b : PrimeTensor.Bridge.LogImage) :
    toMulReal (add a b) =
      toMulReal a *
        toMulReal b := by

  unfold add

  exact
    toMulReal_ofMulReal
      (
        toMulReal a *
          toMulReal b
      )

@[simp]
theorem toMulReal_neg
    (a : PrimeTensor.Bridge.LogImage) :
    toMulReal (neg a) =
      (toMulReal a)⁻¹ := by

  unfold neg

  exact
    toMulReal_ofMulReal
      ((toMulReal a)⁻¹)

end LogImage

namespace MulTangentMap

/--
Conjugate a native multiplicative tangent morphism into the exact logarithmic
coordinate image.
-/
noncomputable def logConjugate
    (D : PrimeTensor.MulTangentMap)
    (z : PrimeTensor.Bridge.LogImage) :
    PrimeTensor.Bridge.LogImage :=
  PrimeTensor.Bridge.LogImage.ofMulReal
    (
      D
        (
          PrimeTensor.Bridge.LogImage.toMulReal z
        )
    )

@[simp]
theorem logConjugate_val
    (D : PrimeTensor.MulTangentMap)
    (z : PrimeTensor.Bridge.LogImage) :
    (logConjugate D z).1 =
      PrimeTensor.Bridge.MulTangentMap.logResponse
        D
        (
          PrimeTensor.Bridge.LogImage.toMulReal z
        ) := by

  rfl

/--
The conjugated tangent fixes additive zero.
-/
theorem logConjugate_zero
    (D : PrimeTensor.MulTangentMap) :
    logConjugate D
        PrimeTensor.Bridge.LogImage.zero
      =
    PrimeTensor.Bridge.LogImage.zero := by

  unfold logConjugate

  rw [
    PrimeTensor.Bridge.LogImage.toMulReal_zero,
    D.map_one
  ]

  rfl

/--
The conjugated tangent is additive on the exact logarithmic coordinate image.
-/
theorem logConjugate_add
    (D : PrimeTensor.MulTangentMap)
    (a b : PrimeTensor.Bridge.LogImage) :
    logConjugate D
        (PrimeTensor.Bridge.LogImage.add a b)
      =
    PrimeTensor.Bridge.LogImage.add
      (logConjugate D a)
      (logConjugate D b) := by

  apply Subtype.ext

  rw [
    logConjugate_val,
    PrimeTensor.Bridge.LogImage.add_val,
    logConjugate_val,
    logConjugate_val,
    PrimeTensor.Bridge.LogImage.toMulReal_add
  ]

  exact
    PrimeTensor.Bridge.MulTangentMap.logResponse_mul
      D
      (PrimeTensor.Bridge.LogImage.toMulReal a)
      (PrimeTensor.Bridge.LogImage.toMulReal b)

/--
The conjugated tangent preserves additive negation.
-/
theorem logConjugate_neg
    (D : PrimeTensor.MulTangentMap)
    (a : PrimeTensor.Bridge.LogImage) :
    logConjugate D
        (PrimeTensor.Bridge.LogImage.neg a)
      =
    PrimeTensor.Bridge.LogImage.neg
      (logConjugate D a) := by

  apply Subtype.ext

  rw [
    logConjugate_val,
    PrimeTensor.Bridge.LogImage.neg_val,
    logConjugate_val,
    PrimeTensor.Bridge.LogImage.toMulReal_neg
  ]

  exact
    PrimeTensor.Bridge.MulTangentMap.logResponse_inv
      D
      (PrimeTensor.Bridge.LogImage.toMulReal a)

/--
Underlying real coordinate form: the conjugated native tangent is additive.
-/
theorem logConjugate_val_add
    (D : PrimeTensor.MulTangentMap)
    (a b : PrimeTensor.Bridge.LogImage) :
    (
      logConjugate D
        (PrimeTensor.Bridge.LogImage.add a b)
    ).1
      =
    (logConjugate D a).1 +
      (logConjugate D b).1 := by

  rw [
    logConjugate_add,
    PrimeTensor.Bridge.LogImage.add_val
  ]

/--
Underlying real coordinate form: the conjugated native tangent preserves
negation.
-/
theorem logConjugate_val_neg
    (D : PrimeTensor.MulTangentMap)
    (a : PrimeTensor.Bridge.LogImage) :
    (
      logConjugate D
        (PrimeTensor.Bridge.LogImage.neg a)
    ).1
      =
    -
      (logConjugate D a).1 := by

  rw [
    logConjugate_neg,
    PrimeTensor.Bridge.LogImage.neg_val
  ]

end MulTangentMap

end Bridge
end PrimeTensor
