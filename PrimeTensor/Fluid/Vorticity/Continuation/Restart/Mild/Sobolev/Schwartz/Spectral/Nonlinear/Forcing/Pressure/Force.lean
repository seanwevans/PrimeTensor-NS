import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.C0.Bridge

/-!
# Physical pressure force from the H³ Leray complement

The pressure derivative bridge gives

    ∂ᵢ p
      =
    Re 𝓕⁻((P F)ᵢ - Fᵢ).

The physical Navier--Stokes interface uses the pressure force `-∂ᵢ p`.
This file performs the final linear Fourier algebra and records the exact
physical identity

    -∂ᵢ p
      =
    Re 𝓕⁻(Fᵢ) - Re 𝓕⁻((P F)ᵢ).

The projected term is written using the already-established continuous forcing
representative.  Thus this theorem has precisely the shape needed to combine
with

    ∂ₜu = Δu - P F

and the classicalization identity

    Re 𝓕⁻F = (u · ∇)u.

We also package the static pressure reconstruction into a spacetime scalar field
for an arbitrary spectral path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PressureForce
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical physical pressure field associated pointwise in time to a
spectral velocity path. -/
noncomputable def h3RawFinPressureRealC1OfPath
    (W : ℝ → H3SpectralFinVectorState) :
    SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
  fun s x =>
    h3RawFinPressureRealC1RepresentativeOnPoint3
      (W s) (W s) x

/-- Inverse Fourier transform distributes over the difference between the
projected and raw nonlinear forcing. -/
theorem h3RawFinLeraySubRaw_fourierInv_eq_leray_fourierInv_sub_raw_fourierInv
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3RawFinLerayOuterProductDivergence U V i ξ
            -
          h3RawFinOuterProductDivergence U V i ξ)
        x
      =
    h3RawFinLerayOuterProductDivergenceC0Representative
        U V i x
      -
    FourierTransformInv.fourierInv
        (h3RawFinOuterProductDivergence U V i)
        x := by
  let P : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence U V i
  let F : H3FourierPoint3 → ℂ :=
    h3RawFinOuterProductDivergence U V i

  have hP :
      Integrable P
        (volume : Measure H3FourierPoint3) := by
    simpa only [P] using
      h3RawFinLerayOuterProductDivergence_integrable U V i

  have hF :
      Integrable F
        (volume : Measure H3FourierPoint3) := by
    simpa only [F] using
      h3RawFinOuterProductDivergence_integrable U V i

  have hNegF :
      Integrable ((-1 : ℂ) • F)
        (volume : Measure H3FourierPoint3) := by
    simpa using hF.neg

  have hInnerNegContinuous :
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          ((-(innerₗ H3FourierPoint3)) p.1) p.2) := by
    change Continuous
      (fun p : H3FourierPoint3 × H3FourierPoint3 =>
        -inner ℝ p.1 p.2)
    exact
      (continuous_inner (𝕜 := ℝ) (E := H3FourierPoint3)).neg

  have hSubFunction :
      (fun ξ : H3FourierPoint3 => P ξ - F ξ)
        =
      P + ((-1 : ℂ) • F) := by
    funext ξ
    simp [sub_eq_add_neg]

  change
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        (fun ξ : H3FourierPoint3 => P ξ - F ξ)
        x
      =
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        P x
      -
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        F x

  rw [hSubFunction]

  rw [
    VectorFourier.fourierIntegral_add
      Real.continuous_fourierChar
      hInnerNegContinuous
      hP
      hNegF
  ]

  rw [
    VectorFourier.fourierIntegral_const_smul
  ]

  simp [sub_eq_add_neg]

/-- For a spectral path, the physical pressure-force component is exactly raw
nonlinear forcing minus Leray-projected forcing after real inverse-Fourier
reconstruction. -/
theorem h3RawFinPressureRealC1OfPath_pressureForceComponent_eq_raw_sub_leray
    (W : ℝ → H3SpectralFinVectorState)
    (s : ℝ)
    (i : Fin 3)
    (x : Point3) :
    PrimeTensor.Bridge.RealFluid.pressureForceComponent
        spatial3
        (h3RawFinPressureRealC1OfPath W)
        s x
        (h3AxisOfFin3 i)
      =
    (FourierTransformInv.fourierInv
      (h3RawFinOuterProductDivergence
        (W s) (W s) i)
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
      -
    (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
      (W s) (W s) i x).re := by
  unfold
    PrimeTensor.Bridge.RealFluid.pressureForceComponent
    h3RawFinPressureRealC1OfPath

  rw [
    h3RawFinPressureRealC1RepresentativeOnPoint3_spatialDerivative_fin_eq_leray_sub_raw
  ]

  rw [
    h3RawFinLeraySubRaw_fourierInv_eq_leray_fourierInv_sub_raw_fourierInv
  ]

  unfold
    h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3

  simp

end

end Euclidean
end Bridge
end PrimeTensor
