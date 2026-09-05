import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Derivative

/-!
# Fréchet-coordinate formula for the arbitrary-H³ C¹ representative

`Derivative` already proves the explicit coordinate line derivative of the
canonical arbitrary-H³ inverse-Fourier representative:

    D_{e_i} C1(G)(x)
      =
    F⁻¹[d_i · raw(G)](x).

The same representative is globally `C¹`, so its canonical Fréchet derivative
exists.  Evaluating that Fréchet derivative on the same coordinate direction
gives another line derivative of the same scalar line path.

Uniqueness of the one-dimensional derivative therefore identifies the two
values.  This tiny bridge lets later quotient arguments move freely between
the operator-valued `fderiv` language and the explicit Fourier multiplier
language without reopening Fourier differentiation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped ENNReal NNReal FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3RealC1FDerivCoordinate
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The canonical Fréchet derivative of the arbitrary-H³ `C¹` representative,
evaluated on a canonical coordinate direction, is exactly inverse Fourier
reconstruction of the corresponding derivative-symbol multiplier. -/
theorem h3SpectralScalarC1Representative_fderiv_apply_fin
    (G : H3SpectralScalarState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    (fderiv ℝ
        (h3SpectralScalarC1Representative G)
        x)
        (h3FourierAxisDirection (h3AxisOfFin3 i))
      =
    FourierTransformInv.fourierInv
      (h3SpectralScalarRawFourierCoordinateDerivative G i)
      x := by
  let v : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 i)

  have hDiffGlobal :
      Differentiable ℝ
        (h3SpectralScalarC1Representative G) :=
    (h3SpectralScalarC1Representative_contDiff_one G).differentiable_one

  have hDiff :
      DifferentiableAt ℝ
        (h3SpectralScalarC1Representative G)
        x :=
    hDiffGlobal x

  have hCanonical :
      HasLineDerivAt ℝ
        (h3SpectralScalarC1Representative G)
        ((fderiv ℝ
          (h3SpectralScalarC1Representative G)
          x) v)
        x
        v :=
    hDiff.hasFDerivAt.hasLineDerivAt v

  have hExplicit :
      HasLineDerivAt ℝ
        (h3SpectralScalarC1Representative G)
        (FourierTransformInv.fourierInv
          (h3SpectralScalarRawFourierCoordinateDerivative G i)
          x)
        x
        v := by
    dsimp only [v]
    exact
      h3SpectralScalarC1Representative_hasLineDerivAt_fin
        G i x

  have hUnique := hCanonical.unique hExplicit

  dsimp only [v] at hUnique
  exact hUnique

end

end Euclidean
end Bridge
end PrimeTensor
