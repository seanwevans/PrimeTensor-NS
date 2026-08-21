import PrimeTensor.Analysis.Chain

/-!
# Primitive response-scale growth control

`ChainAdmissibleAt` quantifies over arbitrary error germs.  This file replaces
that second-order transport assumption by a first-order geometric condition on
the inner response germ itself.

No subtraction-like operation on scale indices is introduced.  Instead, scale
comparison is expressed entirely through `Depth.AtOrAfter`.
-/

namespace PrimeTensor
namespace MulDifferential

/--
First-order quantitative control of the actual response germ.

For every requested refinement gain relative to the original perturbation,
there is a finite response-side gain such that, eventually, every base scale
admits a response scale whose refined endpoint lies at or beyond the requested
base endpoint.

This talks only about the perturbation and its response; it does not quantify
over error germs.
-/
def ResponseScaleControlledAt
    (f : MulReal → MulReal) (x : MulReal) : Prop :=
  ∀ h : MulReal.Seq,
    ApproachesPivot h →
    ∀ targetGain : Depth,
      ∃ responseGain : Depth,
      ∃ anchor : Depth,
        ∀ n : Depth,
          Depth.AtOrAfter anchor n →
          ∀ level : Depth,
            MulReal.ScaleNear level (h n) 1 →
            ∃ responseLevel : Depth,
              MulReal.ScaleNear responseLevel
                (response f x h n) 1 ∧
              Depth.AtOrAfter
                (Depth.advance level targetGain)
                (Depth.advance responseLevel responseGain)

/--
Primitive response-scale control implies the error-transport property used by
the chain rule.
-/
theorem chainAdmissible_of_responseScaleControlled
    {f : MulReal → MulReal} {x : MulReal}
    (hf : ResponseScaleControlledAt f x) :
    ChainAdmissibleAt f x := by
  intro h hh error he targetGain

  obtain ⟨responseGain, controlAnchor, hcontrol⟩ :=
    hf h hh targetGain

  obtain ⟨errorAnchor, herror⟩ :=
    he responseGain

  let anchor := Depth.join controlAnchor errorAnchor
  refine ⟨anchor, ?_⟩
  intro n hn level hbase

  have hcn : Depth.AtOrAfter controlAnchor n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter controlAnchor errorAnchor) hn

  have hen : Depth.AtOrAfter errorAnchor n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter controlAnchor errorAnchor) hn

  obtain ⟨responseLevel, hresponse, hscale⟩ :=
    hcontrol n hcn level hbase

  have herrFine :=
    herror n hen responseLevel hresponse

  exact MulReal.scaleNear_weaken hscale herrFine

/-- The identity response has exact scale control. -/
theorem responseScaleControlledAt_identity (x : MulReal) :
    ResponseScaleControlledAt (fun y => y) x := by
  intro h hh targetGain

  refine ⟨targetGain, .one, ?_⟩
  intro n hn level hbase

  refine ⟨level, ?_, ?_⟩

  · have hresponse :
        response (fun y => y) x h n = h n := by
      change MulReal.ratio (x * h n) x = h n
      exact MulReal.ratio_mul_base x (h n)
    rw [hresponse]
    exact hbase

  · exact .here _

/-- A constant response is maximally scale controlled. -/
theorem responseScaleControlledAt_constant (c x : MulReal) :
    ResponseScaleControlledAt (fun _ => c) x := by
  intro h hh targetGain

  refine ⟨targetGain, .one, ?_⟩
  intro n hn level hbase

  refine ⟨level, ?_, ?_⟩

  · change
      MulReal.ScaleNear level
        (MulReal.ratio c c) 1
    rw [MulReal.ratio_self]
    exact MulReal.scaleNear_refl level 1

  · exact .here _

/--
Chain rule stated only with first-order response geometry.

This removes the explicit second-order `ChainAdmissibleAt` assumption from the
user-facing theorem.
-/
theorem hasMulDerivativeAt_comp_of_responseScaleControlled
    {f g : MulReal → MulReal}
    {x : MulReal}
    {Df Dg : MulTangentMap}
    (hf : HasMulDerivativeAt f x Df)
    (hDf : Df.ScaleControlled)
    (hresponse : ResponseScaleControlledAt f x)
    (hg : HasMulDerivativeAt g (f x) Dg)
    (hDg : Dg.ScaleControlled) :
    HasMulDerivativeAt
      (fun y => g (f y))
      x
      (MulTangentMap.comp Dg Df) := by
  exact hasMulDerivativeAt_comp
    hf
    hDf
    (chainAdmissible_of_responseScaleControlled hresponse)
    hg
    hDg

end MulDifferential
end PrimeTensor
