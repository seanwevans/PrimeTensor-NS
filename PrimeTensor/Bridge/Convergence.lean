import PrimeTensor.Bridge.Real
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Filter semantics for bridge convergence

`Bridge.Real` introduced an epsilon-tail predicate

    MulCauchyStream.ConvergesReal s x

for the conventional real interpretation of a native positive-depth stream.
This file identifies that predicate with ordinary filter convergence on the
native `Depth` tail filter.

Once this equivalence is available, ordinary continuity theorems from mathlib
can be reused inside the bridge instead of reproving epsilon estimates for every
native stream operation.

The first consequences are closure of `ConvergesReal` under native stream
multiplication, inversion at a nonzero limit, and oriented ratio.
-/

namespace PrimeTensor
namespace Bridge

namespace Depth

/--
The conventional filter of native positive-depth tails.

A set is eventually true precisely when it contains every index at or after
some native `Depth` anchor.
-/
def tailFilter : Filter PrimeTensor.Depth where
  sets :=
    {S | ∃ anchor : PrimeTensor.Depth,
      ∀ n : PrimeTensor.Depth,
        PrimeTensor.Depth.AtOrAfter anchor n →
        n ∈ S}

  univ_sets := by
    refine ⟨.one, ?_⟩
    intro n hn
    trivial

  sets_of_superset := by
    intro A B hA hAB
    obtain ⟨anchor, hTail⟩ := hA
    refine ⟨anchor, ?_⟩
    intro n hn
    exact hAB (hTail n hn)

  inter_sets := by
    intro A B hA hB
    obtain ⟨aAnchor, ha⟩ := hA
    obtain ⟨bAnchor, hb⟩ := hB

    let anchor :=
      PrimeTensor.Depth.join aAnchor bAnchor

    refine ⟨anchor, ?_⟩
    intro n hn

    have hna :
        PrimeTensor.Depth.AtOrAfter aAnchor n :=
      PrimeTensor.Depth.atOrAfter_trans
        (PrimeTensor.Depth.left_atOrAfter
          aAnchor bAnchor)
        hn

    have hnb :
        PrimeTensor.Depth.AtOrAfter bAnchor n :=
      PrimeTensor.Depth.atOrAfter_trans
        (PrimeTensor.Depth.right_atOrAfter
          aAnchor bAnchor)
        hn

    exact ⟨ha n hna, hb n hnb⟩

/-- Unfolding rule for eventual truth on the positive-depth tail filter. -/
theorem eventually_tailFilter_iff
    {P : PrimeTensor.Depth → Prop} :
    (∀ᶠ n in tailFilter, P n) ↔
      ∃ anchor : PrimeTensor.Depth,
        ∀ n : PrimeTensor.Depth,
          PrimeTensor.Depth.AtOrAfter anchor n →
          P n := by
  rfl

end Depth

namespace MulCauchyStream

/--
The bridge epsilon-tail definition is exactly ordinary real convergence along
the native positive-depth tail filter.
-/
theorem convergesReal_iff_tendsto
    (s : PrimeTensor.MulCauchyStream)
    (x : ℝ) :
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal s x ↔
      Filter.Tendsto
        (PrimeTensor.Bridge.MulCauchyStream.toRealTerm s)
        PrimeTensor.Bridge.Depth.tailFilter
        (nhds x) := by

  rw [Metric.tendsto_nhds]

  constructor

  · intro h ε hε

    rw [PrimeTensor.Bridge.Depth.eventually_tailFilter_iff]

    obtain ⟨anchor, hTail⟩ :=
      h ε hε

    refine ⟨anchor, ?_⟩
    intro n hn

    rw [Real.dist_eq]

    exact hTail n hn

  · intro h ε hε

    have hEventually :=
      h ε hε

    rw [PrimeTensor.Bridge.Depth.eventually_tailFilter_iff]
      at hEventually

    obtain ⟨anchor, hTail⟩ :=
      hEventually

    refine ⟨anchor, ?_⟩
    intro n hn

    have hn := hTail n hn

    rw [Real.dist_eq] at hn

    exact hn

/-- Conventional convergence is preserved by native pointwise multiplication. -/
theorem convergesReal_mul
    {a b : PrimeTensor.MulCauchyStream}
    {x y : ℝ}
    (ha : PrimeTensor.Bridge.MulCauchyStream.ConvergesReal a x)
    (hb : PrimeTensor.Bridge.MulCauchyStream.ConvergesReal b y) :
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (PrimeTensor.MulCauchyStream.mul a b)
      (x * y) := by

  rw [PrimeTensor.Bridge.MulCauchyStream.convergesReal_iff_tendsto]
    at ha hb ⊢

  have hmul := ha.mul hb

  change
    Filter.Tendsto
      (fun n : PrimeTensor.Depth =>
        PrimeTensor.Bridge.MulRat.toReal (a.term n) *
          PrimeTensor.Bridge.MulRat.toReal (b.term n))
      PrimeTensor.Bridge.Depth.tailFilter
      (nhds (x * y))
    at hmul

  unfold
    PrimeTensor.Bridge.MulCauchyStream.toRealTerm

  simpa only [
    PrimeTensor.MulCauchyStream.mul_term,
    PrimeTensor.Bridge.MulRat.toReal_mul
  ] using hmul

/-- Conventional convergence is preserved by native pointwise inversion. -/
theorem convergesReal_inv
    {a : PrimeTensor.MulCauchyStream}
    {x : ℝ}
    (ha : PrimeTensor.Bridge.MulCauchyStream.ConvergesReal a x)
    (hx : x ≠ 0) :
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (PrimeTensor.MulCauchyStream.inv a)
      x⁻¹ := by

  rw [PrimeTensor.Bridge.MulCauchyStream.convergesReal_iff_tendsto]
    at ha ⊢

  have hinv := ha.inv₀ hx

  change
    Filter.Tendsto
      (fun n : PrimeTensor.Depth =>
        (PrimeTensor.Bridge.MulRat.toReal (a.term n))⁻¹)
      PrimeTensor.Bridge.Depth.tailFilter
      (nhds x⁻¹)
    at hinv

  unfold
    PrimeTensor.Bridge.MulCauchyStream.toRealTerm

  simpa only [
    PrimeTensor.MulCauchyStream.inv_term,
    PrimeTensor.Bridge.MulRat.toReal_inv
  ] using hinv

/-- Conventional convergence is preserved by native pointwise oriented ratio. -/
theorem convergesReal_ratio
    {a b : PrimeTensor.MulCauchyStream}
    {x y : ℝ}
    (ha : PrimeTensor.Bridge.MulCauchyStream.ConvergesReal a x)
    (hb : PrimeTensor.Bridge.MulCauchyStream.ConvergesReal b y)
    (hy : y ≠ 0) :
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (
        PrimeTensor.MulCauchyStream.mul
          a
          (PrimeTensor.MulCauchyStream.inv b)
      )
      (x / y) := by

  have hInv :=
    PrimeTensor.Bridge.MulCauchyStream.convergesReal_inv
      hb hy

  have hMul :=
    PrimeTensor.Bridge.MulCauchyStream.convergesReal_mul
      ha hInv

  simpa only [div_eq_mul_inv] using hMul

end MulCauchyStream

end Bridge
end PrimeTensor
