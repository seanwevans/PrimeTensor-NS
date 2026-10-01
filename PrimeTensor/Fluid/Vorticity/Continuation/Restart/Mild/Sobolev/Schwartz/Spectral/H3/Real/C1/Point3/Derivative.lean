import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Transport

/-!
# Point3 coordinate derivatives of the arbitrary-H³ inverse-Fourier representative

`H3.Real.C1.Derivative` identifies the genuine line derivative of the complex
inverse-Fourier representative on the Euclidean Fourier carrier.  The physical
Navier--Stokes layer, however, differentiates the real representative on
PrimeTensor's `Point3` carrier through `spatial3.d`.

This file closes exactly that representation gap.

First we pass the complex line derivative through `Complex.reCLM`.  Then the
existing Sobolev transport theorem supplies a second line-derivative witness
whose value is `spatial3.d`.  Uniqueness of the line derivative identifies the
two values.

The resulting formula is the coordinatewise bridge needed to turn the already
proved inverse-Fourier raw-divergence identity into physical-space
incompressibility.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal FourierTransform LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3RealC1Point3Derivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Taking real parts carries the exact complex inverse-Fourier coordinate
line derivative to the real representative on the Euclidean carrier. -/
theorem h3SpectralScalarRealC1Representative_hasLineDerivAt_fin
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    HasLineDerivAt ℝ
      (h3SpectralScalarRealC1Representative G)
      ((FourierTransformInv.fourierInv
        (h3SpectralScalarRawFourierCoordinateDerivative G i)
        x).re)
      x
      (h3FourierAxisDirection (h3AxisOfFin3 i)) := by
  have hComplex :=
    h3SpectralScalarC1Representative_hasLineDerivAt_fin
      G i x

  unfold HasLineDerivAt at hComplex ⊢

  have hReal :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt
      (0 : ℝ)
      hComplex

  simpa only [
    h3SpectralScalarRealC1Representative,
    Function.comp_def,
    Complex.reCLM_apply
  ] using hReal

/-- The intrinsic `Point3` spatial coordinate derivative is exactly the real
part of the inverse Fourier transform of the corresponding raw derivative
multiplier. -/
theorem h3SpectralScalarRealC1RepresentativeOnPoint3_spatialDerivative_fin
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (x : Point3) :
    spatial3.d
        (h3AxisOfFin3 i)
        (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
        x
      =
    (FourierTransformInv.fourierInv
      (h3SpectralScalarRawFourierCoordinateDerivative G i)
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re := by
  let ξ : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  have hC1 :
      SpatialC1
        (h3SpectralScalarRealC1RepresentativeOnPoint3 G) :=
    h3SpectralScalarRealC1RepresentativeOnPoint3_contDiff_one G

  have hTransport :=
    h3TransportScalarField_hasLineDerivAt
      hC1
      (h3AxisOfFin3 i)
      ξ

  have hPoint :
      h3FourierToPoint3CLM ξ = x := by
    ext j
    rfl

  have hTransportFunction :
      (fun y : H3FourierPoint3 =>
        h3SpectralScalarRealC1RepresentativeOnPoint3 G
          (h3FourierToPoint3CLM y))
        =
      h3SpectralScalarRealC1Representative G := by
    funext y
    unfold h3SpectralScalarRealC1RepresentativeOnPoint3
    congr 1

  rw [hTransportFunction, hPoint] at hTransport

  change
    HasLineDerivAt ℝ
      (h3SpectralScalarRealC1Representative G)
      (spatial3.d
        (h3AxisOfFin3 i)
        (h3SpectralScalarRealC1RepresentativeOnPoint3 G)
        x)
      ξ
      (h3FourierAxisDirection (h3AxisOfFin3 i))
    at hTransport

  have hFourier :=
    h3SpectralScalarRealC1Representative_hasLineDerivAt_fin
      G i ξ

  have hUnique := hTransport.unique hFourier

  simpa only [ξ] using hUnique

end
end Euclidean
end Bridge
end PrimeTensor
