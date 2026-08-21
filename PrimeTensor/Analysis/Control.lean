import PrimeTensor.Analysis.Examples

/-!
# Quantitative scale control for multiplicative tangent maps

Ordinary continuity at the pivot is not enough for the multiplicative chain
rule.  The derivative uses a relative scale rate, so tangent maps need a
quantitative statement saying that arbitrarily fine input refinements produce
arbitrarily fine output refinements with finite scale distortion.

This file develops exactly that structure.

No additive metric, zeroth scale, subtraction, or conventional norm is used.
-/

namespace PrimeTensor

namespace MulRat

/--
One finer finite-barcode scale implies the current scale.
-/
theorem scaleWithin_succ_weaken {level : Depth} {a b : MulRat}
    (h : ScaleWithin (.succ level) a b) :
    ScaleWithin level a b := by
  unfold ScaleWithin at h ⊢

  have hone :
      (1 : MulRat) * (1 : MulRat) < two := by
    rw [one_mul]
    exact one_lt_two

  constructor
  · have hsquare :
        scalePow (ratio a b) level * scalePow (ratio a b) level < two := by
      simpa [scalePow] using h.1
    have hout :=
      mul_lt_two_of_sq_lt_two hsquare hone
    rw [mul_one] at hout
    exact hout

  · have hsquare :
        scalePow (ratio b a) level * scalePow (ratio b a) level < two := by
      simpa [scalePow] using h.2
    have hout :=
      mul_lt_two_of_sq_lt_two hsquare hone
    rw [mul_one] at hout
    exact hout

end MulRat

namespace MulReal

/--
One finer completed scale implies the current completed scale.
-/
theorem scaleNear_succ_weaken {level : Depth} {a b : MulReal}
    (h : ScaleNear (.succ level) a b) :
    ScaleNear level a b := by
  obtain ⟨as, bs, has, hbs, anchor, htail⟩ := h
  refine ⟨as, bs, has, hbs, anchor, ?_⟩
  intro n hn
  exact MulRat.scaleWithin_succ_weaken (htail n hn)

/--
Scale nearness may be weakened along positive-depth tail order.
-/
theorem scaleNear_weaken {coarse fine : Depth} {a b : MulReal}
    (hcf : Depth.AtOrAfter coarse fine)
    (h : ScaleNear fine a b) :
    ScaleNear coarse a b := by
  induction hcf with
  | here =>
      exact h
  | later hcf ih =>
      exact ih (scaleNear_succ_weaken h)

end MulReal

namespace Depth

/--
Advancing a base scale respects refinement order in the gain argument.
-/
theorem advance_atOrAfter (level : Depth) {a b : Depth}
    (hab : AtOrAfter a b) :
    AtOrAfter (advance level a) (advance level b) := by
  induction hab with
  | here =>
      exact .here _
  | later hab ih =>
      exact .later ih

/-- Advancing by the joined gain is at least as fine as advancing by the left gain. -/
theorem advance_left_join (level a b : Depth) :
    AtOrAfter (advance level a) (advance level (join a b)) := by
  exact advance_atOrAfter level (left_atOrAfter a b)

/-- Advancing by the joined gain is at least as fine as advancing by the right gain. -/
theorem advance_right_join (level a b : Depth) :
    AtOrAfter (advance level b) (advance level (join a b)) := by
  exact advance_atOrAfter level (right_atOrAfter a b)

end Depth

namespace MulTangentMap

/--
Quantitative intrinsic scale control.

For every requested positive output refinement gain, there is a finite positive
input refinement gain that guarantees it, uniformly over the ambient scale.
-/
def ScaleControlled (D : MulTangentMap) : Prop :=
  ∀ targetGain : Depth,
    ∃ sourceGain : Depth,
      ∀ level : Depth, ∀ h : MulReal,
        MulReal.ScaleNear (Depth.advance level sourceGain) h 1 →
        MulReal.ScaleNear (Depth.advance level targetGain) (D h) 1

/-- The identity tangent is scale controlled with no relative distortion. -/
theorem scaleControlled_identity :
    ScaleControlled identity := by
  intro targetGain
  refine ⟨targetGain, ?_⟩
  intro level h hh
  exact hh

/-- The trivial tangent is scale controlled at every requested refinement. -/
theorem scaleControlled_trivial :
    ScaleControlled trivial := by
  intro targetGain
  refine ⟨targetGain, ?_⟩
  intro level h hh
  change MulReal.ScaleNear (Depth.advance level targetGain) 1 1
  exact MulReal.scaleNear_refl (Depth.advance level targetGain) 1

/-- Inversion preserves quantitative scale control. -/
theorem ScaleControlled.inv {D : MulTangentMap}
    (hD : ScaleControlled D) :
    ScaleControlled (inv D) := by
  intro targetGain
  obtain ⟨sourceGain, hcontrol⟩ := hD targetGain
  refine ⟨sourceGain, ?_⟩
  intro level h hh

  have hout :=
    MulReal.scaleNear_inv (hcontrol level h hh)

  change
    MulReal.ScaleNear (Depth.advance level targetGain)
      (D h)⁻¹ 1

  simpa only [MulReal.inv_one] using hout

/--
Products of scale-controlled tangents are scale controlled.

Each factor is requested one output refinement deeper, because completed
multiplication consumes one scale level.
-/
theorem ScaleControlled.mul {D E : MulTangentMap}
    (hD : ScaleControlled D)
    (hE : ScaleControlled E) :
    ScaleControlled (mul D E) := by
  intro targetGain

  obtain ⟨sourceD, hcontrolD⟩ := hD (.succ targetGain)
  obtain ⟨sourceE, hcontrolE⟩ := hE (.succ targetGain)

  let sourceGain := Depth.join sourceD sourceE
  refine ⟨sourceGain, ?_⟩
  intro level h hh

  have hhD :
      MulReal.ScaleNear (Depth.advance level sourceD) h 1 :=
    MulReal.scaleNear_weaken
      (Depth.advance_left_join level sourceD sourceE)
      hh

  have hhE :
      MulReal.ScaleNear (Depth.advance level sourceE) h 1 :=
    MulReal.scaleNear_weaken
      (Depth.advance_right_join level sourceD sourceE)
      hh

  have hDfine := hcontrolD level h hhD
  have hEfine := hcontrolE level h hhE

  have hprod := MulReal.scaleNear_mul hDfine hEfine
  rw [MulReal.one_mul] at hprod

  simpa only [Depth.advance_succ, mul_apply] using hprod

/-- Positive-depth tangent powers are quantitatively scale controlled. -/
theorem scaleControlled_depthPow :
    ∀ d : Depth, ScaleControlled (depthPow d)
  | .one => scaleControlled_identity
  | .succ d =>
      ScaleControlled.mul
        scaleControlled_identity
        (scaleControlled_depthPow d)

/--
A scale-controlled tangent sends pivot-convergent sequences to
pivot-convergent sequences.
-/
theorem ScaleControlled.maps_converges
    {D : MulTangentMap}
    (hD : ScaleControlled D)
    {s : MulReal.Seq}
    (hs : MulReal.ConvergesTo s 1) :
    MulReal.ConvergesTo (fun n => D (s n)) 1 := by
  intro level

  obtain ⟨sourceGain, hcontrol⟩ := hD .one
  obtain ⟨anchor, htail⟩ :=
    hs (Depth.advance level sourceGain)

  refine ⟨anchor, ?_⟩
  intro n hn

  have hout :=
    hcontrol level (s n) (htail n hn)

  have hout' :
      MulReal.ScaleNear (.succ level) (D (s n)) 1 := by
    simpa [Depth.advance] using hout

  exact MulReal.scaleNear_succ_weaken hout'

end MulTangentMap

namespace MulDifferential

/--
Quantitative scale control transports negligible errors through tangent maps.
-/
theorem negligible_map
    {D : MulTangentMap}
    (hD : D.ScaleControlled)
    {error base : MulReal.Seq}
    (herror : NegligibleRelative error base) :
    NegligibleRelative (fun n => D (error n)) base := by
  intro targetGain

  obtain ⟨sourceGain, hcontrol⟩ := hD targetGain
  obtain ⟨anchor, htail⟩ := herror sourceGain

  refine ⟨anchor, ?_⟩
  intro n hn level hbase

  exact hcontrol level (error n)
    (htail n hn level hbase)

end MulDifferential

end PrimeTensor
