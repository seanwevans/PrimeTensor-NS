import PrimeTensor.Fluid.VorticityDiffusionBranch
import PrimeTensor.Analysis.Control

/-!
# Field-scale convergence and native diffusion refinement

A fixed `MulBalanceState` is not by itself a refinement process.  If two fixed
values fail to be near at one intrinsic scale, failure at every finer scale is
just monotonicity.  Likewise, requiring one fixed ratio to be near `1` at every
finer scale is essentially an equality demand.

The scale variable relevant to a cascade must therefore be separated from the
refinement stage.

This file introduces positive-depth-indexed *families of scalar fields* and
their intrinsic field-scale convergence.  For diffusion we use the topology
that the operator actually needs: convergence of the same-axis second spatial
derivatives.

Under that second-jet convergence:

* the three same-axis second derivatives converge pointwise in native scale;
* their three-factor multiplicative Laplacian converges;
* the ratio of the stagewise Laplacian to the limiting Laplacian converges to
  the multiplicative pivot `1`.

This is the first nontrivial refinement-indexed diffusion statement.  No norm,
subtraction, additive identity, ordinary metric, logarithm, or zeroth scale is
introduced.
-/

namespace PrimeTensor

namespace MulReal

/--
One finer scale of nearness between `a` and `b` makes their oriented ratio
near the pivot at the requested scale.

The one-level cost is exactly the completed multiplication cost.
-/
theorem scaleNear_ratio_one
    {level : Depth}
    {a b : MulReal}
    (h : ScaleNear (.succ level) a b) :
    ScaleNear level (ratio a b) 1 := by

  have hInv :
      ScaleNear
        (.succ level)
        b⁻¹
        b⁻¹ :=
    scaleNear_refl
      (.succ level)
      b⁻¹

  have hProduct :=
    scaleNear_mul h hInv

  change
    ScaleNear level
      (a * b⁻¹)
      1

  rw [mul_inv] at hProduct

  exact hProduct

end MulReal

namespace FieldScale

/-- A native multiplicative scalar field. -/
abbrev Field
    (X : Type)
    (dim : Depth) :=
  PrimeTensor.ScalarField
    X PrimeTensor.MulReal dim

/-- A positive-depth-indexed refinement family of native scalar fields. -/
abbrev Seq
    (X : Type)
    (dim : Depth) :=
  Depth → Field X dim

/--
Pointwise intrinsic nearness of two fields at one common scale.
-/
def Near
    {X : Type}
    {dim : Depth}
    (level : Depth)
    (f g : Field X dim) : Prop :=
  ∀ x : PrimeTensor.Point X dim,
    MulReal.ScaleNear
      level
      (f x)
      (g x)

/--
A field refinement family converges when every intrinsic output scale is
eventually reached pointwise everywhere.
-/
def ConvergesTo
    {X : Type}
    {dim : Depth}
    (s : Seq X dim)
    (f : Field X dim) : Prop :=
  ∀ level : Depth,
    ∃ anchor : Depth,
      ∀ n : Depth,
        Depth.AtOrAfter anchor n →
          Near level (s n) f

/-- Every field is near itself at every intrinsic scale. -/
theorem near_refl
    {X : Type}
    {dim : Depth}
    (level : Depth)
    (f : Field X dim) :
    Near level f f := by

  intro x

  exact
    MulReal.scaleNear_refl
      level
      (f x)

/-- Field nearness weakens from finer scales to coarser scales. -/
theorem near_weaken
    {X : Type}
    {dim : Depth}
    {coarse fine : Depth}
    {f g : Field X dim}
    (hcf : Depth.AtOrAfter coarse fine)
    (h : Near fine f g) :
    Near coarse f g := by

  intro x

  exact
    MulReal.scaleNear_weaken
      hcf
      (h x)

/--
Pointwise products of convergent field families converge.

As on the completed scalar carrier, multiplication consumes one intrinsic
refinement level.
-/
theorem converges_mul
    {X : Type}
    {dim : Depth}
    {a b : Seq X dim}
    {f g : Field X dim}
    (ha : ConvergesTo a f)
    (hb : ConvergesTo b g) :
    ConvergesTo
      (fun n x =>
        a n x * b n x)
      (fun x =>
        f x * g x) := by

  intro level

  obtain ⟨aAnchor, haTail⟩ :=
    ha (.succ level)

  obtain ⟨bAnchor, hbTail⟩ :=
    hb (.succ level)

  let anchor :=
    Depth.join aAnchor bAnchor

  refine ⟨anchor, ?_⟩

  intro n hn

  have han :
      Depth.AtOrAfter aAnchor n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter aAnchor bAnchor)
      hn

  have hbn :
      Depth.AtOrAfter bAnchor n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter aAnchor bAnchor)
      hn

  intro x

  exact
    MulReal.scaleNear_mul
      (haTail n han x)
      (hbTail n hbn x)

/--
Stagewise ratio of a refinement family to its limiting field.
-/
noncomputable def ratioToLimit
    {X : Type}
    {dim : Depth}
    (s : Seq X dim)
    (f : Field X dim) :
    Seq X dim :=
  fun n x =>
    MulReal.ratio
      (s n x)
      (f x)

/--
Field convergence is equivalently visible as convergence of the stagewise
oriented ratio toward the multiplicative pivot, with the one refinement level
consumed by ratio formation made explicit.
-/
theorem ratioToLimit_convergesTo_one
    {X : Type}
    {dim : Depth}
    {s : Seq X dim}
    {f : Field X dim}
    (hs : ConvergesTo s f) :
    ConvergesTo
      (ratioToLimit s f)
      (fun _ => (1 : MulReal)) := by

  intro level

  obtain ⟨anchor, hTail⟩ :=
    hs (.succ level)

  refine ⟨anchor, ?_⟩

  intro n hn
  intro x

  unfold ratioToLimit

  exact
    MulReal.scaleNear_ratio_one
      (hTail n hn x)

/--
Same-axis second-derivative nearness.

This is the intrinsic topology directly consumed by the multiplicative
Laplacian.  We deliberately do not claim that pointwise field nearness alone
controls derivatives.
-/
def SecondDerivativeNear
    {X : Type}
    {dim : Depth}
    (D :
      PrimeTensor.Differential
        X PrimeTensor.MulReal dim)
    (level : Depth)
    (f g : Field X dim) : Prop :=
  ∀ i : PrimeTensor.Axis dim,
    Near
      level
      (D.d i (D.d i f))
      (D.d i (D.d i g))

/--
A refinement family converges in the native same-axis second-jet topology.
-/
def SecondDerivativeConvergesTo
    {X : Type}
    {dim : Depth}
    (D :
      PrimeTensor.Differential
        X PrimeTensor.MulReal dim)
    (s : Seq X dim)
    (f : Field X dim) : Prop :=
  ∀ level : Depth,
    ∃ anchor : Depth,
      ∀ n : Depth,
        Depth.AtOrAfter anchor n →
          SecondDerivativeNear
            D level
            (s n)
            f

end FieldScale

namespace Bridge
namespace Euclidean

/--
The explicit three-factor native Laplacian field in Euclidean dimension three.

This is definitionally the shape used by the native vorticity diffusion terms.
-/
noncomputable def mulLaplacian3Field
    (
      f :
        FieldScale.Field
          ℝ Depth.three
    ) :
    FieldScale.Field
      ℝ Depth.three :=
  fun x =>
    mulSpatial3.d
        xAxis
        (mulSpatial3.d xAxis f)
        x
      *
    (
      mulSpatial3.d
          yAxis
          (mulSpatial3.d yAxis f)
          x
        *
      mulSpatial3.d
          zAxis
          (mulSpatial3.d zAxis f)
          x
    )

/--
Second-jet nearness two levels finer than `level` is sufficient to resolve the
three-factor native Laplacian at `level`.

Two levels are consumed by the nested three-factor multiplication.
-/
theorem mulLaplacian3Field_near
    {level : Depth}
    {
      f g :
        FieldScale.Field
          ℝ Depth.three
    }
    (
      h :
        FieldScale.SecondDerivativeNear
          mulSpatial3
          (.succ (.succ level))
          f g
    ) :
    FieldScale.Near
      level
      (mulLaplacian3Field f)
      (mulLaplacian3Field g) := by

  intro x

  have hxFine :=
    h xAxis x

  have hyFine :=
    h yAxis x

  have hzFine :=
    h zAxis x

  have hx :
      MulReal.ScaleNear
        (.succ level)
        (
          mulSpatial3.d
            xAxis
            (mulSpatial3.d xAxis f)
            x
        )
        (
          mulSpatial3.d
            xAxis
            (mulSpatial3.d xAxis g)
            x
        ) :=
    MulReal.scaleNear_succ_weaken
      hxFine

  have hyz :
      MulReal.ScaleNear
        (.succ level)
        (
          mulSpatial3.d
              yAxis
              (mulSpatial3.d yAxis f)
              x
            *
          mulSpatial3.d
              zAxis
              (mulSpatial3.d zAxis f)
              x
        )
        (
          mulSpatial3.d
              yAxis
              (mulSpatial3.d yAxis g)
              x
            *
          mulSpatial3.d
              zAxis
              (mulSpatial3.d zAxis g)
              x
        ) :=
    MulReal.scaleNear_mul
      hyFine
      hzFine

  unfold mulLaplacian3Field

  exact
    MulReal.scaleNear_mul
      hx
      hyz

/--
Convergence in the native same-axis second-jet topology implies convergence of
the multiplicative three-dimensional Laplacian field.
-/
theorem mulLaplacian3Field_converges
    {
      s :
        FieldScale.Seq
          ℝ Depth.three
    }
    {
      f :
        FieldScale.Field
          ℝ Depth.three
    }
    (
      hs :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          s f
    ) :
    FieldScale.ConvergesTo
      (fun n =>
        mulLaplacian3Field
          (s n))
      (mulLaplacian3Field f) := by

  intro level

  obtain ⟨anchor, hTail⟩ :=
    hs (.succ (.succ level))

  refine ⟨anchor, ?_⟩

  intro n hn

  exact
    mulLaplacian3Field_near
      (hTail n hn)

/--
The stagewise native diffusion ratio converges to the multiplicative pivot.

This is the sequence-based form of "diffusion resolves under refinement":
for every requested intrinsic scale, sufficiently late second-jet refinement
makes the Laplacian ratio near `1`.
-/
theorem mulLaplacian3Field_ratio_convergesTo_one
    {
      s :
        FieldScale.Seq
          ℝ Depth.three
    }
    {
      f :
        FieldScale.Field
          ℝ Depth.three
    }
    (
      hs :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          s f
    ) :
    FieldScale.ConvergesTo
      (
        FieldScale.ratioToLimit
          (fun n =>
            mulLaplacian3Field
              (s n))
          (mulLaplacian3Field f)
      )
      (fun _ => (1 : MulReal)) := by

  exact
    FieldScale.ratioToLimit_convergesTo_one
      (mulLaplacian3Field_converges hs)

end Euclidean
end Bridge

end PrimeTensor
