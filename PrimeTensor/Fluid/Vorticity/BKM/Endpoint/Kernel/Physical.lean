import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Canonical.Slice
import PrimeTensor.Fluid.Vorticity.L1Linf.Control
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# BKM endpoint: physical kernel bounds

The canonical-slice Fourier estimate identifies every velocity-gradient mode
with a bounded degree-zero multiplier applied to curl modes.  To use a
physical vorticity `L∞` envelope, one must localize that multiplier in
frequency and return to physical space.

The resulting terms have the form

    (K * ω)(x) = ∫ K(y) ω(x-y) dy.

This file proves the measure-theoretic estimate needed at that stage:

    ‖K * f‖∞ ≤ ‖K‖₁ ‖f‖∞.

It also packages the two-kernel form that matches the three-dimensional
Biot--Savart formulas and specializes the scalar input to the actual
componentwise physical vorticity envelope.

No frequency cutoff or kernel-mass estimate is assumed to exist here.  Those
are the remaining harmonic-analysis steps.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeBKMEndpointPhysicalKernel
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceBKMEndpointPhysicalKernel :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Raw physical convolution used by the localized BKM argument. -/
noncomputable def h3BKMPhysicalConvolution
    (K f : Point3 → ℂ)
    (x : Point3) : ℂ :=
  ∫ y : Point3,
    K y * f (x - y)
    ∂(volume : Measure Point3)

/--
An integrable kernel acting on a globally bounded function is pointwise
controlled by its `L¹` kernel mass.
-/
theorem norm_h3BKMPhysicalConvolution_le
    (K f : Point3 → ℂ)
    (M : ℝ)
    (hK : Integrable K (volume : Measure Point3))
    (hf : ∀ z : Point3, ‖f z‖ ≤ M)
    (x : Point3) :
    ‖h3BKMPhysicalConvolution K f x‖
      ≤
    M * ∫ y : Point3, ‖K y‖ ∂(volume : Measure Point3) := by

  have hMajor :
      Integrable
        (fun y : Point3 => M * ‖K y‖)
        (volume : Measure Point3) :=
    hK.norm.const_mul M

  unfold h3BKMPhysicalConvolution

  calc
    ‖∫ y : Point3,
        K y * f (x - y)
        ∂(volume : Measure Point3)‖
        ≤
      ∫ y : Point3,
        M * ‖K y‖
        ∂(volume : Measure Point3) := by

      apply
        norm_integral_le_of_norm_le
          hMajor

      filter_upwards with y

      rw [norm_mul]

      have hPoint :
          ‖K y‖ * ‖f (x - y)‖
            ≤
          ‖K y‖ * M :=
        mul_le_mul_of_nonneg_left
          (hf (x - y))
          (norm_nonneg _)

      simpa only [mul_comm] using hPoint

    _ =
      M * ∫ y : Point3, ‖K y‖
        ∂(volume : Measure Point3) := by
      rw [integral_const_mul]

/--
Two localized curl contributions are controlled by the sum of their kernel
`L¹` masses times the common physical `L∞` envelope.
-/
theorem norm_h3BKMPhysicalConvolution_add_le
    (K₁ K₂ f₁ f₂ : Point3 → ℂ)
    (M : ℝ)
    (hK₁ : Integrable K₁ (volume : Measure Point3))
    (hK₂ : Integrable K₂ (volume : Measure Point3))
    (hf₁ : ∀ z : Point3, ‖f₁ z‖ ≤ M)
    (hf₂ : ∀ z : Point3, ‖f₂ z‖ ≤ M)
    (x : Point3) :
    ‖h3BKMPhysicalConvolution K₁ f₁ x
        +
      h3BKMPhysicalConvolution K₂ f₂ x‖
      ≤
    M *
      (
        (∫ y : Point3, ‖K₁ y‖ ∂(volume : Measure Point3))
          +
        (∫ y : Point3, ‖K₂ y‖ ∂(volume : Measure Point3))
      ) := by

  calc
    ‖h3BKMPhysicalConvolution K₁ f₁ x
          +
        h3BKMPhysicalConvolution K₂ f₂ x‖
        ≤
      ‖h3BKMPhysicalConvolution K₁ f₁ x‖
        +
      ‖h3BKMPhysicalConvolution K₂ f₂ x‖ :=
      norm_add_le _ _

    _ ≤
      M * (∫ y : Point3, ‖K₁ y‖ ∂(volume : Measure Point3))
        +
      M * (∫ y : Point3, ‖K₂ y‖ ∂(volume : Measure Point3)) :=
      add_le_add
        (norm_h3BKMPhysicalConvolution_le
          K₁ f₁ M hK₁ hf₁ x)
        (norm_h3BKMPhysicalConvolution_le
          K₂ f₂ M hK₂ hf₂ x)

    _ =
      M *
        (
          (∫ y : Point3, ‖K₁ y‖ ∂(volume : Measure Point3))
            +
          (∫ y : Point3, ‖K₂ y‖ ∂(volume : Measure Point3))
        ) := by
      ring

/-- Physical x-vorticity viewed as a complex scalar field. -/
noncomputable def h3BKMPhysicalVorticityX
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (x : Point3) : ℂ :=
  (
    realVorticityX
      (logSpaceTimeVectorField u)
      t x :
    ℂ
  )

/-- Physical y-vorticity viewed as a complex scalar field. -/
noncomputable def h3BKMPhysicalVorticityY
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (x : Point3) : ℂ :=
  (
    realVorticityY
      (logSpaceTimeVectorField u)
      t x :
    ℂ
  )

/-- Physical z-vorticity viewed as a complex scalar field. -/
noncomputable def h3BKMPhysicalVorticityZ
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (t : ℝ)
    (x : Point3) : ℂ :=
  (
    realVorticityZ
      (logSpaceTimeVectorField u)
      t x :
    ℂ
  )

/-- The physical vorticity envelope bounds the complexified x-component. -/
theorem norm_h3BKMPhysicalVorticityX_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (x : Point3) :
    ‖h3BKMPhysicalVorticityX u t x‖ ≤ g t := by

  unfold h3BKMPhysicalVorticityX

  simpa only [
    Complex.norm_real,
    Real.norm_eq_abs
  ] using
    (hEnvelope x).1

/-- The physical vorticity envelope bounds the complexified y-component. -/
theorem norm_h3BKMPhysicalVorticityY_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (x : Point3) :
    ‖h3BKMPhysicalVorticityY u t x‖ ≤ g t := by

  unfold h3BKMPhysicalVorticityY

  simpa only [
    Complex.norm_real,
    Real.norm_eq_abs
  ] using
    (hEnvelope x).2.1

/-- The physical vorticity envelope bounds the complexified z-component. -/
theorem norm_h3BKMPhysicalVorticityZ_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (x : Point3) :
    ‖h3BKMPhysicalVorticityZ u t x‖ ≤ g t := by

  unfold h3BKMPhysicalVorticityZ

  simpa only [
    Complex.norm_real,
    Real.norm_eq_abs
  ] using
    (hEnvelope x).2.2

/--
Any integrable kernel acting on the x-vorticity is controlled directly by the
physical vorticity envelope.
-/
theorem norm_h3BKMPhysicalConvolution_vorticityX_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (K : Point3 → ℂ)
    (hK : Integrable K (volume : Measure Point3))
    (x : Point3) :
    ‖h3BKMPhysicalConvolution
        K
        (h3BKMPhysicalVorticityX u t)
        x‖
      ≤
    g t * ∫ y : Point3, ‖K y‖ ∂(volume : Measure Point3) := by

  exact
    norm_h3BKMPhysicalConvolution_le
      K
      (h3BKMPhysicalVorticityX u t)
      (g t)
      hK
      (norm_h3BKMPhysicalVorticityX_le hEnvelope)
      x

/-- Y-vorticity analogue. -/
theorem norm_h3BKMPhysicalConvolution_vorticityY_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (K : Point3 → ℂ)
    (hK : Integrable K (volume : Measure Point3))
    (x : Point3) :
    ‖h3BKMPhysicalConvolution
        K
        (h3BKMPhysicalVorticityY u t)
        x‖
      ≤
    g t * ∫ y : Point3, ‖K y‖ ∂(volume : Measure Point3) := by

  exact
    norm_h3BKMPhysicalConvolution_le
      K
      (h3BKMPhysicalVorticityY u t)
      (g t)
      hK
      (norm_h3BKMPhysicalVorticityY_le hEnvelope)
      x

/-- Z-vorticity analogue. -/
theorem norm_h3BKMPhysicalConvolution_vorticityZ_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (K : Point3 → ℂ)
    (hK : Integrable K (volume : Measure Point3))
    (x : Point3) :
    ‖h3BKMPhysicalConvolution
        K
        (h3BKMPhysicalVorticityZ u t)
        x‖
      ≤
    g t * ∫ y : Point3, ‖K y‖ ∂(volume : Measure Point3) := by

  exact
    norm_h3BKMPhysicalConvolution_le
      K
      (h3BKMPhysicalVorticityZ u t)
      (g t)
      hK
      (norm_h3BKMPhysicalVorticityZ_le hEnvelope)
      x

/--
The exact two-vorticity estimate needed by a localized Biot--Savart gradient
entry.  The component fields are parameters, so this single theorem covers
the `(Z,Y)`, `(Z,X)`, and `(Y,X)` pairings appearing in the three target
velocity components.
-/
theorem norm_h3BKMPhysicalTwoVorticityConvolutions_le
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ}
    {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (K₁ K₂ : Point3 → ℂ)
    (hK₁ : Integrable K₁ (volume : Measure Point3))
    (hK₂ : Integrable K₂ (volume : Measure Point3))
    (ω₁ ω₂ : Point3 → ℂ)
    (hω₁ :
      ∀ x : Point3,
        ‖ω₁ x‖ ≤ g t)
    (hω₂ :
      ∀ x : Point3,
        ‖ω₂ x‖ ≤ g t)
    (x : Point3) :
    ‖h3BKMPhysicalConvolution K₁ ω₁ x
        +
      h3BKMPhysicalConvolution K₂ ω₂ x‖
      ≤
    g t *
      (
        (∫ y : Point3, ‖K₁ y‖ ∂(volume : Measure Point3))
          +
        (∫ y : Point3, ‖K₂ y‖ ∂(volume : Measure Point3))
      ) := by

  exact
    norm_h3BKMPhysicalConvolution_add_le
      K₁ K₂
      ω₁ ω₂
      (g t)
      hK₁ hK₂
      hω₁ hω₂
      x

end

end Euclidean
end Bridge
end PrimeTensor
