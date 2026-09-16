import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedWeakProjectedRHSPhysicalReduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Test.Fixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Diffusion.Fourier

/-!
# Selected weak-test Laplacian in Fourier space

The remaining selected weak-to-physical diffusion seam is most naturally
closed on the Fourier side.

For a compact smooth scalar weak test `φ`, the existing first-derivative
Plancherel bridge gives

    Fourier(∂ᵢ φ) = dᵢ Fourier(φ)

almost everywhere.  Applying that bridge once more to the bundled derivative
test gives

    Fourier(∂ᵢ² φ) = dᵢ² Fourier(φ).

Summing over the three coordinate axes and using the already-proved diffusion
symbol identity

    Σᵢ dᵢ² = -q

then yields the exact Fourier transform of the compact-test Laplacian.

No selected-state regularity, endpoint passage, or old-branch input occurs in
this file.  The next increment can pair this identity directly against the
selected raw Fourier state and the packaged selected Laplacian.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongSelectedWeakTestLaplacianFourier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongSelectedWeakTestLaplacianFourier :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The bundled pure second derivative of a compact weak test has exactly the
square of the coordinate Fourier derivative symbol as its scalar Plancherel
multiplier. -/
theorem h3WeakTestFunctionPhysicalL2_secondSpatialDerivative_fourier_ae
    (φ : H3WeakTestFunction)
    (i : Fin 3) :
    (h3ScalarFourierL2
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSecondSpatialDerivative
            (h3AxisOfFin3 i) φ)) :
        H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3FourierDerivativeSymbol2 i i ξ *
        h3ScalarFourierL2
          (h3WeakTestFunctionPhysicalL2 φ) ξ) := by
  let dφ : H3WeakTestFunction :=
    h3WeakTestFunctionSpatialDerivative
      (h3AxisOfFin3 i) φ

  have hFirst :=
    h3WeakTestFunctionPhysicalL2_spatialDerivative_fourier_ae
      φ i

  have hSecond :=
    h3WeakTestFunctionPhysicalL2_spatialDerivative_fourier_ae
      dφ i

  filter_upwards [hFirst, hSecond] with ξ hFirstξ hSecondξ

  dsimp only [dφ] at hSecondξ

  change
    h3ScalarFourierL2
        (h3WeakTestFunctionPhysicalL2
          (h3WeakTestFunctionSpatialDerivative
            (h3AxisOfFin3 i)
            (h3WeakTestFunctionSpatialDerivative
              (h3AxisOfFin3 i) φ))) ξ
      =
    h3FourierDerivativeSymbol2 i i ξ *
      h3ScalarFourierL2
        (h3WeakTestFunctionPhysicalL2 φ) ξ

  rw [hSecondξ, hFirstξ]

  simp only [h3FourierDerivativeSymbol2, mul_assoc]

/-- Summing the three bundled pure second derivatives of a compact weak test
produces exactly the scalar Laplacian Fourier multiplier `-q(ξ)`. -/
theorem sum_h3WeakTestFunctionPhysicalL2_secondSpatialDerivative_fourier_ae
    (φ : H3WeakTestFunction) :
    ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
      (∑ i : Fin 3,
        h3ScalarFourierL2
          (h3WeakTestFunctionPhysicalL2
            (h3WeakTestFunctionSecondSpatialDerivative
              (h3AxisOfFin3 i) φ))
          ξ)
        =
      -(h3FourierGradientSquare ξ : ℂ) *
        h3ScalarFourierL2
          (h3WeakTestFunctionPhysicalL2 φ) ξ := by
  have h0 :=
    h3WeakTestFunctionPhysicalL2_secondSpatialDerivative_fourier_ae
      φ (0 : Fin 3)

  have h1 :=
    h3WeakTestFunctionPhysicalL2_secondSpatialDerivative_fourier_ae
      φ (1 : Fin 3)

  have h2 :=
    h3WeakTestFunctionPhysicalL2_secondSpatialDerivative_fourier_ae
      φ (2 : Fin 3)

  filter_upwards [h0, h1, h2] with ξ h0ξ h1ξ h2ξ

  simp only [Fin.sum_univ_three]

  rw [h0ξ, h1ξ, h2ξ]

  calc
    (h3FourierDerivativeSymbol2 0 0 ξ *
          h3ScalarFourierL2
            (h3WeakTestFunctionPhysicalL2 φ) ξ
        +
      h3FourierDerivativeSymbol2 1 1 ξ *
          h3ScalarFourierL2
            (h3WeakTestFunctionPhysicalL2 φ) ξ)
        +
      h3FourierDerivativeSymbol2 2 2 ξ *
        h3ScalarFourierL2
          (h3WeakTestFunctionPhysicalL2 φ) ξ
        =
      (∑ i : Fin 3,
        h3FourierDerivativeSymbol2 i i ξ) *
        h3ScalarFourierL2
          (h3WeakTestFunctionPhysicalL2 φ) ξ := by
            simp only [Fin.sum_univ_three]
            ring
    _ =
      -(h3FourierGradientSquare ξ : ℂ) *
        h3ScalarFourierL2
          (h3WeakTestFunctionPhysicalL2 φ) ξ := by
            rw [sum_h3FourierDerivativeSymbol2_diag_eq_neg_gradientSquare]

end

end Euclidean
end Bridge
end PrimeTensor
