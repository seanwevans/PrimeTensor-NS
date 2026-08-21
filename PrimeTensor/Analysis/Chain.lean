import PrimeTensor.Analysis.Control

/-!
# Multiplicative chain rule with explicit inner-response admissibility

The derivative and quantitative tangent-control axioms are almost sufficient
for composition.  One additional hypothesis is exposed explicitly:

negligibility measured relative to the actual inner response germ must imply
negligibility relative to the original perturbation germ.

This is the intrinsic multiplicative analogue of the classical local
`Df(h) = O(h)` comparison needed to transport an outer little-o error back to
the original variable.

Nothing is hidden in an additive norm or subtraction-based estimate.
-/

namespace PrimeTensor

namespace MulReal

/-- Multiplicative ratios compose through an intermediate completed magnitude. -/
theorem ratio_comp (a b c : MulReal) :
    ratio a c = ratio a b * ratio b c := by
  unfold ratio
  symm
  calc
    (a * b⁻¹) * (b * c⁻¹)
        = ((a * b⁻¹) * b) * c⁻¹ :=
          (mul_assoc (a * b⁻¹) b c⁻¹).symm
    _ = (a * (b⁻¹ * b)) * c⁻¹ := by
      rw [mul_assoc a b⁻¹ b]
    _ = (a * 1) * c⁻¹ := by
      rw [inv_mul b]
    _ = a * c⁻¹ := by
      rw [mul_one]

/-- Multiplying an oriented ratio by its denominator reconstructs the numerator. -/
theorem ratio_mul_right (a b : MulReal) :
    ratio a b * b = a := by
  unfold ratio
  calc
    (a * b⁻¹) * b = a * (b⁻¹ * b) := mul_assoc a b⁻¹ b
    _ = a * 1 := by rw [inv_mul b]
    _ = a := mul_one a

/-- Multiplying the denominator by its oriented ratio also reconstructs the numerator. -/
theorem mul_ratio_right (a b : MulReal) :
    b * ratio a b = a := by
  rw [mul_comm]
  exact ratio_mul_right a b

/-- Pointwise equality preserves intrinsic convergence. -/
theorem converges_congr
    {a b : Seq} {x : MulReal}
    (h : ∀ n : Depth, a n = b n)
    (ha : ConvergesTo a x) :
    ConvergesTo b x := by
  intro level
  obtain ⟨anchor, htail⟩ := ha level
  refine ⟨anchor, ?_⟩
  intro n hn
  rw [← h n]
  exact htail n hn

end MulReal

namespace MulTangentMap

/-- Composition of multiplicative tangent morphisms. -/
def comp (Dg Df : MulTangentMap) : MulTangentMap where
  toFun := fun h => Dg (Df h)
  map_one := by
    rw [Df.map_one, Dg.map_one]
  map_mul := by
    intro a b
    rw [Df.map_mul, Dg.map_mul]
  map_inv := by
    intro a
    rw [Df.map_inv, Dg.map_inv]

@[simp] theorem comp_apply (Dg Df : MulTangentMap) (h : MulReal) :
    comp Dg Df h = Dg (Df h) := rfl

/-- Tangent morphisms preserve multiplicative ratios. -/
theorem map_ratio (D : MulTangentMap) (a b : MulReal) :
    D (MulReal.ratio a b) =
      MulReal.ratio (D a) (D b) := by
  unfold MulReal.ratio
  rw [D.map_mul, D.map_inv]

end MulTangentMap

namespace MulDifferential

/-- Pointwise equality preserves negligibility relative to a fixed base germ. -/
theorem negligible_congr
    {error₁ error₂ base : MulReal.Seq}
    (h : ∀ n : Depth, error₁ n = error₂ n)
    (he : NegligibleRelative error₁ base) :
    NegligibleRelative error₂ base := by
  intro gain
  obtain ⟨anchor, htail⟩ := he gain
  refine ⟨anchor, ?_⟩
  intro n hn level hbase
  rw [← h n]
  exact htail n hn level hbase

/--
A negligible error over a pivot-convergent base itself converges to the pivot.
-/
theorem negligible_converges
    {error base : MulReal.Seq}
    (he : NegligibleRelative error base)
    (hb : ApproachesPivot base) :
    MulReal.ConvergesTo error 1 := by
  intro level

  obtain ⟨eAnchor, heTail⟩ := he .one
  obtain ⟨bAnchor, hbTail⟩ := hb level

  let anchor := Depth.join eAnchor bAnchor
  refine ⟨anchor, ?_⟩
  intro n hn

  have hen : Depth.AtOrAfter eAnchor n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter eAnchor bAnchor) hn

  have hbn : Depth.AtOrAfter bAnchor n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter eAnchor bAnchor) hn

  have hfine :=
    heTail n hen level (hbTail n hbn)

  have hfine' :
      MulReal.ScaleNear (.succ level) (error n) 1 := by
    simpa [Depth.advance] using hfine

  exact MulReal.scaleNear_succ_weaken hfine'

/--
A differentiable response with a scale-controlled tangent actually approaches
the multiplicative pivot.
-/
theorem response_converges
    {f : MulReal → MulReal} {x : MulReal}
    {D : MulTangentMap}
    (hf : HasMulDerivativeAt f x D)
    (hD : D.ScaleControlled)
    {h : MulReal.Seq}
    (hh : ApproachesPivot h) :
    MulReal.ConvergesTo (response f x h) 1 := by

  have hfirst := hf h hh

  have herror :
      MulReal.ConvergesTo
        (fun n =>
          MulReal.ratio
            (response f x h n)
            (D (h n)))
        1 :=
    negligible_converges hfirst hh

  have hmodel :
      MulReal.ConvergesTo
        (fun n => D (h n))
        1 :=
    hD.maps_converges hh

  have hproduct :=
    MulReal.converges_mul herror hmodel

  rw [MulReal.one_mul] at hproduct

  exact MulReal.converges_congr
    (fun n =>
      MulReal.ratio_mul_right
        (response f x h n)
        (D (h n)))
    hproduct

/--
The exact additional hypothesis needed to transport outer little-o errors
through an inner response germ.

It says that, along every pivot-approaching perturbation, anything negligible
relative to the actual inner response is also negligible relative to the
original perturbation.
-/
def ChainAdmissibleAt
    (f : MulReal → MulReal) (x : MulReal) : Prop :=
  ∀ h : MulReal.Seq,
    ApproachesPivot h →
    ∀ error : MulReal.Seq,
      NegligibleRelative error (response f x h) →
      NegligibleRelative error h

/-- The identity map is chain-admissible at every point. -/
theorem chainAdmissibleAt_identity (x : MulReal) :
    ChainAdmissibleAt (fun y => y) x := by
  intro h hh error he
  intro gain

  obtain ⟨anchor, htail⟩ := he gain
  refine ⟨anchor, ?_⟩
  intro n hn level hbase

  apply htail n hn level

  have hresponse :
      response (fun y => y) x h n = h n := by
    change MulReal.ratio (x * h n) x = h n
    exact MulReal.ratio_mul_base x (h n)

  rw [hresponse]
  exact hbase

/-- Response of a composition is the outer response along the inner response germ. -/
theorem response_comp
    (f g : MulReal → MulReal)
    (x : MulReal)
    (h : MulReal.Seq) :
    ∀ n : Depth,
      response (fun y => g (f y)) x h n =
        response g (f x) (response f x h) n := by
  intro n
  unfold response
  rw [MulReal.mul_ratio_right
    (f (x * h n))
    (f x)]

/--
Chain rule under explicit quantitative hypotheses.

`Df` must be scale controlled so the actual inner response approaches `1`.
`Dg` must be scale controlled so it transports the inner negligible error.
`f` must be chain-admissible so the outer negligible error can be measured
back against the original perturbation.
-/
theorem hasMulDerivativeAt_comp
    {f g : MulReal → MulReal}
    {x : MulReal}
    {Df Dg : MulTangentMap}
    (hf : HasMulDerivativeAt f x Df)
    (hDf : Df.ScaleControlled)
    (hadm : ChainAdmissibleAt f x)
    (hg : HasMulDerivativeAt g (f x) Dg)
    (hDg : Dg.ScaleControlled) :
    HasMulDerivativeAt
      (fun y => g (f y))
      x
      (MulTangentMap.comp Dg Df) := by

  intro h hh

  let inner : MulReal.Seq := response f x h

  have hinnerPivot :
      ApproachesPivot inner := by
    exact response_converges hf hDf hh

  have houter :
      FirstOrderEquivalent inner
        (response g (f x) inner)
        (fun n => Dg (inner n)) :=
    hg inner hinnerPivot

  have houterBack :
      NegligibleRelative
        (fun n =>
          MulReal.ratio
            (response g (f x) inner n)
            (Dg (inner n)))
        h :=
    hadm h hh _ houter

  have hinnerError :
      NegligibleRelative
        (fun n =>
          MulReal.ratio
            (inner n)
            (Df (h n)))
        h := by
    exact hf h hh

  have hmappedInnerError :
      NegligibleRelative
        (fun n =>
          Dg
            (MulReal.ratio
              (inner n)
              (Df (h n))))
        h :=
    negligible_map hDg hinnerError

  have htransport :
      NegligibleRelative
        (fun n =>
          MulReal.ratio
            (Dg (inner n))
            (Dg (Df (h n))))
        h := by
    apply negligible_congr
      (fun n =>
        MulTangentMap.map_ratio
          Dg
          (inner n)
          (Df (h n)))
    exact hmappedInnerError

  have hcombined :
      NegligibleRelative
        (fun n =>
          MulReal.ratio
              (response g (f x) inner n)
              (Dg (inner n)) *
            MulReal.ratio
              (Dg (inner n))
              (Dg (Df (h n))))
        h :=
    negligible_mul houterBack htransport

  apply negligible_congr ?_ hcombined
  intro n

  have hresponse :
      response (fun y => g (f y)) x h n =
        response g (f x) inner n := by
    simpa [inner] using response_comp f g x h n

  have htangent :
      MulTangentMap.comp Dg Df (h n) =
        Dg (Df (h n)) := by
    rfl

  calc
    MulReal.ratio
          (response g (f x) inner n)
          (Dg (inner n)) *
        MulReal.ratio
          (Dg (inner n))
          (Dg (Df (h n)))
        =
      MulReal.ratio
        (response g (f x) inner n)
        (Dg (Df (h n))) :=
      (MulReal.ratio_comp
        (response g (f x) inner n)
        (Dg (inner n))
        (Dg (Df (h n)))).symm
    _ =
      MulReal.ratio
        (response (fun y => g (f y)) x h n)
        (MulTangentMap.comp Dg Df (h n)) := by
      rw [hresponse, htangent]

end MulDifferential

end PrimeTensor
