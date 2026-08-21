import PrimeTensor.Fluid.Vorticity.Field.Scale

/-!
# Refinement-indexed diffusion in the native vorticity balance

`VorticityFieldScale` proves that convergence of a refinement family in the
same-axis second-jet topology forces convergence of the three-factor native
Laplacian, and hence convergence of its stagewise ratio to the pivot `1`.

This file identifies the actual native vorticity diffusion components with that
Laplacian construction and feeds the result back into
`vorticityBalancePerturbationX/Y/Z`.

Thus, for a positive-depth-indexed family of velocity fields `uₙ` approaching a
limiting field `u` strongly enough that the corresponding native vorticity
component converges in same-axis second derivatives, the *diffusion slot* of
the relative native balance state

    ratio (balanceState uₙ) (balanceState u)

converges intrinsically to `1`.

This is a genuine refinement-indexed diffusion-resolution statement.  It does
not require one fixed diffusion ratio to be near `1` at every scale.

No norm, subtraction, additive identity, ordinary metric, logarithm, or zeroth
scale is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Positive-depth-indexed family of native three-dimensional velocity fields. -/
abbrev VelocityRefinementSeq :=
  Depth →
    PrimeTensor.SpaceTimeVectorField
      ℝ ℝ PrimeTensor.MulReal Depth.three

/-- Native x-vorticity field at fixed time. -/
noncomputable def vorticityFieldX
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) :
    FieldScale.Field
      ℝ Depth.three :=
  fun x =>
    mulVorticityX u t x

/-- Native y-vorticity field at fixed time. -/
noncomputable def vorticityFieldY
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) :
    FieldScale.Field
      ℝ Depth.three :=
  fun x =>
    mulVorticityY u t x

/-- Native z-vorticity field at fixed time. -/
noncomputable def vorticityFieldZ
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) :
    FieldScale.Field
      ℝ Depth.three :=
  fun x =>
    mulVorticityZ u t x

/--
The native x-vorticity diffusion component is exactly the explicit
three-factor native Laplacian of the native x-vorticity field.
-/
theorem mulVorticityDiffusionX_eq_mulLaplacian3Field
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    mulVorticityDiffusionX u t x
      =
    mulLaplacian3Field
      (vorticityFieldX u t)
      x := by

  rfl

/--
The native y-vorticity diffusion component is exactly the explicit
three-factor native Laplacian of the native y-vorticity field.
-/
theorem mulVorticityDiffusionY_eq_mulLaplacian3Field
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    mulVorticityDiffusionY u t x
      =
    mulLaplacian3Field
      (vorticityFieldY u t)
      x := by

  rfl

/--
The native z-vorticity diffusion component is exactly the explicit
three-factor native Laplacian of the native z-vorticity field.
-/
theorem mulVorticityDiffusionZ_eq_mulLaplacian3Field
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    mulVorticityDiffusionZ u t x
      =
    mulLaplacian3Field
      (vorticityFieldZ u t)
      x := by

  rfl

/-- Refinement sequence of native x-vorticity fields at fixed time. -/
noncomputable def vorticityFieldSeqX
    (U : VelocityRefinementSeq)
    (t : ℝ) :
    FieldScale.Seq
      ℝ Depth.three :=
  fun n =>
    vorticityFieldX
      (U n)
      t

/-- Refinement sequence of native y-vorticity fields at fixed time. -/
noncomputable def vorticityFieldSeqY
    (U : VelocityRefinementSeq)
    (t : ℝ) :
    FieldScale.Seq
      ℝ Depth.three :=
  fun n =>
    vorticityFieldY
      (U n)
      t

/-- Refinement sequence of native z-vorticity fields at fixed time. -/
noncomputable def vorticityFieldSeqZ
    (U : VelocityRefinementSeq)
    (t : ℝ) :
    FieldScale.Seq
      ℝ Depth.three :=
  fun n =>
    vorticityFieldZ
      (U n)
      t

/--
The actual x-diffusion fields of a velocity refinement family converge whenever
the associated x-vorticity fields converge in same-axis second derivatives.
-/
theorem mulVorticityDiffusionX_converges
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldSeqX U t)
          (vorticityFieldX u t)
    ) :
    FieldScale.ConvergesTo
      (
        fun n x =>
          mulVorticityDiffusionX
            (U n) t x
      )
      (
        fun x =>
          mulVorticityDiffusionX
            u t x
      ) := by

  simpa [
    vorticityFieldSeqX,
    mulVorticityDiffusionX_eq_mulLaplacian3Field
  ] using
    (mulLaplacian3Field_converges hω)

/--
The actual y-diffusion fields of a velocity refinement family converge whenever
the associated y-vorticity fields converge in same-axis second derivatives.
-/
theorem mulVorticityDiffusionY_converges
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldSeqY U t)
          (vorticityFieldY u t)
    ) :
    FieldScale.ConvergesTo
      (
        fun n x =>
          mulVorticityDiffusionY
            (U n) t x
      )
      (
        fun x =>
          mulVorticityDiffusionY
            u t x
      ) := by

  simpa [
    vorticityFieldSeqY,
    mulVorticityDiffusionY_eq_mulLaplacian3Field
  ] using
    (mulLaplacian3Field_converges hω)

/--
The actual z-diffusion fields of a velocity refinement family converge whenever
the associated z-vorticity fields converge in same-axis second derivatives.
-/
theorem mulVorticityDiffusionZ_converges
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldSeqZ U t)
          (vorticityFieldZ u t)
    ) :
    FieldScale.ConvergesTo
      (
        fun n x =>
          mulVorticityDiffusionZ
            (U n) t x
      )
      (
        fun x =>
          mulVorticityDiffusionZ
            u t x
      ) := by

  simpa [
    vorticityFieldSeqZ,
    mulVorticityDiffusionZ_eq_mulLaplacian3Field
  ] using
    (mulLaplacian3Field_converges hω)

/--
The x-diffusion slot of the stagewise relative native balance state converges
to the pivot.
-/
theorem vorticityBalancePerturbationX_diffusion_convergesTo_one
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldSeqX U t)
          (vorticityFieldX u t)
    ) :
    FieldScale.ConvergesTo
      (
        fun n x =>
          (
            vorticityBalancePerturbationX
              (U n) u t x
          ).diffusion
      )
      (fun _ => (1 : MulReal)) := by

  have hDiffusion :
      FieldScale.ConvergesTo
        (
          fun n x =>
            mulVorticityDiffusionX
              (U n) t x
        )
        (
          fun x =>
            mulVorticityDiffusionX
              u t x
        ) :=
    mulVorticityDiffusionX_converges
      hω

  have hRatio :=
    FieldScale.ratioToLimit_convergesTo_one
      hDiffusion

  change
    FieldScale.ConvergesTo
      (
        fun n x =>
          MulReal.ratio
            (mulVorticityDiffusionX (U n) t x)
            (mulVorticityDiffusionX u t x)
      )
      (fun _ => (1 : MulReal))
    at hRatio

  simpa [
    vorticityBalancePerturbationX,
    MulBalanceState.ratio,
    vorticityBalanceStateX
  ] using hRatio

/--
The y-diffusion slot of the stagewise relative native balance state converges
to the pivot.
-/
theorem vorticityBalancePerturbationY_diffusion_convergesTo_one
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldSeqY U t)
          (vorticityFieldY u t)
    ) :
    FieldScale.ConvergesTo
      (
        fun n x =>
          (
            vorticityBalancePerturbationY
              (U n) u t x
          ).diffusion
      )
      (fun _ => (1 : MulReal)) := by

  have hDiffusion :
      FieldScale.ConvergesTo
        (
          fun n x =>
            mulVorticityDiffusionY
              (U n) t x
        )
        (
          fun x =>
            mulVorticityDiffusionY
              u t x
        ) :=
    mulVorticityDiffusionY_converges
      hω

  have hRatio :=
    FieldScale.ratioToLimit_convergesTo_one
      hDiffusion

  change
    FieldScale.ConvergesTo
      (
        fun n x =>
          MulReal.ratio
            (mulVorticityDiffusionY (U n) t x)
            (mulVorticityDiffusionY u t x)
      )
      (fun _ => (1 : MulReal))
    at hRatio

  simpa [
    vorticityBalancePerturbationY,
    MulBalanceState.ratio,
    vorticityBalanceStateY
  ] using hRatio

/--
The z-diffusion slot of the stagewise relative native balance state converges
to the pivot.
-/
theorem vorticityBalancePerturbationZ_diffusion_convergesTo_one
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldSeqZ U t)
          (vorticityFieldZ u t)
    ) :
    FieldScale.ConvergesTo
      (
        fun n x =>
          (
            vorticityBalancePerturbationZ
              (U n) u t x
          ).diffusion
      )
      (fun _ => (1 : MulReal)) := by

  have hDiffusion :
      FieldScale.ConvergesTo
        (
          fun n x =>
            mulVorticityDiffusionZ
              (U n) t x
        )
        (
          fun x =>
            mulVorticityDiffusionZ
              u t x
        ) :=
    mulVorticityDiffusionZ_converges
      hω

  have hRatio :=
    FieldScale.ratioToLimit_convergesTo_one
      hDiffusion

  change
    FieldScale.ConvergesTo
      (
        fun n x =>
          MulReal.ratio
            (mulVorticityDiffusionZ (U n) t x)
            (mulVorticityDiffusionZ u t x)
      )
      (fun _ => (1 : MulReal))
    at hRatio

  simpa [
    vorticityBalancePerturbationZ,
    MulBalanceState.ratio,
    vorticityBalanceStateZ
  ] using hRatio

end Euclidean
end Bridge
end PrimeTensor
