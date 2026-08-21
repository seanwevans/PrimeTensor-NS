import PrimeTensor.Bridge.LogScale
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Intrinsic Cauchy streams in logarithmic coordinates

This is a bridge-only theorem layer.

`Bridge.LogScale` identifies native intrinsic scale closeness with ordinary
distance in real logarithmic coordinates.  Here we prove that the bridge
radii become arbitrarily small, then transfer the two native completion
relations into ordinary epsilon statements:

* every `MulCauchyStream` is Cauchy in log coordinates;
* `MulAsymptotic a b` means the log-coordinate difference tends to zero.

These are interpretation theorems only.  No additive structure is added to
the native `MulRat`, `MulReal`, or completion layers.
-/

namespace PrimeTensor
namespace Bridge

/--
Embed an ordinary natural refinement count into the native positive `Depth`.

`depthFromNat 0 = .one`; each natural successor adds one native successor.
This is bridge bookkeeping only.
-/
def depthFromNat : ℕ → Depth
  | 0 => .one
  | n + 1 => .succ (depthFromNat n)

@[simp] theorem depthFromNat_zero :
    depthFromNat 0 = .one := by
  rfl

@[simp] theorem depthFromNat_succ
    (n : ℕ) :
    depthFromNat (n + 1) =
      .succ (depthFromNat n) := by
  rfl

/--
The bridge scale factor at `depthFromNat n` is exactly `2^n`.
-/
theorem logScaleFactor_depthFromNat :
    ∀ n : ℕ,
      logScaleFactor (depthFromNat n) =
        (2 : ℝ) ^ n

  | 0 => by
      simp only [
        depthFromNat_zero,
        logScaleFactor_one,
        pow_zero
      ]

  | n + 1 => by
      rw [
        depthFromNat_succ,
        logScaleFactor_succ,
        logScaleFactor_depthFromNat n,
        pow_succ
      ]

      ring

/--
Native bridge radii are arbitrarily small.

This is the only Archimedean ingredient needed to turn intrinsic Cauchy
control into ordinary epsilon-Cauchy control.
-/
theorem exists_logScaleRadius_lt
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ d : Depth,
      logScaleRadius d < ε := by

  have htwo :
      (1 : ℝ) < 2 := by
    norm_num

  obtain ⟨n, hn⟩ :=
    pow_unbounded_of_one_lt
      (Real.log 2 / ε)
      htwo

  refine ⟨depthFromNat n, ?_⟩

  unfold logScaleRadius

  rw [logScaleFactor_depthFromNat]

  have hpow :
      0 < (2 : ℝ) ^ n :=
    pow_pos (by norm_num) n

  have hn' :
      Real.log 2 <
        (2 : ℝ) ^ n * ε := by

    rw [div_lt_iff₀ hε] at hn
    exact hn

  rw [div_lt_iff₀ hpow]

  simpa only [mul_comm] using hn'

namespace MulCauchyStream

/--
Ordinary real logarithmic coordinate of one finite stream term.
-/
noncomputable def logTerm
    (s : PrimeTensor.MulCauchyStream)
    (n : Depth) : ℝ :=
  Real.log
    (
      PrimeTensor.Bridge.MulRat.toReal
        (s.term n)
    )

/--
Bridge-only ordinary epsilon-Cauchy property of logarithmic coordinates.
-/
def LogCauchy
    (s : PrimeTensor.MulCauchyStream) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ anchor : Depth,
      ∀ m n : Depth,
        Depth.AtOrAfter anchor m →
        Depth.AtOrAfter anchor n →
        abs (logTerm s m - logTerm s n) < ε

/--
Every intrinsic multiplicative Cauchy stream is an ordinary Cauchy sequence
after taking conventional real logarithmic coordinates.
-/
theorem logCauchy
    (s : PrimeTensor.MulCauchyStream) :
    LogCauchy s := by

  intro ε hε

  obtain ⟨level, hRadius⟩ :=
    exists_logScaleRadius_lt hε

  obtain ⟨anchor, hTail⟩ :=
    s.cauchy level

  refine ⟨anchor, ?_⟩

  intro m n hm hn

  have hScale :
      PrimeTensor.MulRat.ScaleWithin level
        (s.term m)
        (s.term n) :=
    hTail m n hm hn

  have hLog :
      abs
        (
          Real.log
              (PrimeTensor.Bridge.MulRat.toReal
                (s.term m)) -
            Real.log
              (PrimeTensor.Bridge.MulRat.toReal
                (s.term n))
        )
        <
      logScaleRadius level :=
    (
      PrimeTensor.Bridge.MulRat.scaleWithin_iff_log
          level
          (s.term m)
          (s.term n)
    ).mp hScale

  change
    abs (logTerm s m - logTerm s n) < ε

  exact lt_trans hLog hRadius

end MulCauchyStream

/--
Bridge-only epsilon form of intrinsic asymptotic equivalence in logarithmic
coordinates.
-/
def LogAsymptotic
    (a b : PrimeTensor.MulCauchyStream) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ anchor : Depth,
      ∀ n : Depth,
        Depth.AtOrAfter anchor n →
        abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logTerm a n -
              PrimeTensor.Bridge.MulCauchyStream.logTerm b n
          )
          < ε

/--
Intrinsic `MulAsymptotic` equivalence implies ordinary convergence of the
log-coordinate difference to zero.
-/
theorem logAsymptotic_of_mulAsymptotic
    {a b : PrimeTensor.MulCauchyStream}
    (h : PrimeTensor.MulAsymptotic a b) :
    LogAsymptotic a b := by

  intro ε hε

  obtain ⟨level, hRadius⟩ :=
    exists_logScaleRadius_lt hε

  obtain ⟨anchor, hTail⟩ :=
    h level

  refine ⟨anchor, ?_⟩

  intro n hn

  have hScale :
      PrimeTensor.MulRat.ScaleWithin level
        (a.term n)
        (b.term n) :=
    hTail n hn

  have hLog :
      abs
        (
          Real.log
              (PrimeTensor.Bridge.MulRat.toReal
                (a.term n)) -
            Real.log
              (PrimeTensor.Bridge.MulRat.toReal
                (b.term n))
        )
        <
      logScaleRadius level :=
    (
      PrimeTensor.Bridge.MulRat.scaleWithin_iff_log
          level
          (a.term n)
          (b.term n)
    ).mp hScale

  change
    abs
      (
        PrimeTensor.Bridge.MulCauchyStream.logTerm a n -
          PrimeTensor.Bridge.MulCauchyStream.logTerm b n
      )
      < ε

  exact lt_trans hLog hRadius

end Bridge
end PrimeTensor
