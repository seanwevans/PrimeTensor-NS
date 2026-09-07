import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.FourierL2HeatGeneratorIntegral

/-!
# Physical L² temporal admissibility: quotient-safe Laplacian CLM

The raw Fourier Laplacian on weighted H³ scalar data is already known to be
contractive:

    ‖Δ̂_L² G‖ ≤ ‖G‖.

For the semigroup FTC argument it is useful to package this map as an actual
real continuous linear map from the weighted H³ state into raw Fourier `L²`.
That allows the quotient-safe generator to be transported through Bochner
integrals using the standard continuous-linear-map integral API.

This file supplies the missing algebraic packaging.  No new analytic estimate
is required.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2LaplacianCLM
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The quotient-safe raw Fourier Laplacian preserves zero. -/
@[simp]
theorem h3SpectralScalarLaplacianRawFourierL2_zero :
    h3SpectralScalarLaplacianRawFourierL2
        (0 : H3SpectralScalarState)
      =
    0 := by
  have h :=
    h3SpectralScalarLaplacianRawFourierL2_sub
      (0 : H3SpectralScalarState)
      (0 : H3SpectralScalarState)
  simpa using h

/-- The quotient-safe raw Fourier Laplacian preserves negation. -/
theorem h3SpectralScalarLaplacianRawFourierL2_neg
    (G : H3SpectralScalarState) :
    h3SpectralScalarLaplacianRawFourierL2 (-G)
      =
    -h3SpectralScalarLaplacianRawFourierL2 G := by
  have h :=
    h3SpectralScalarLaplacianRawFourierL2_sub
      (0 : H3SpectralScalarState)
      G
  simpa using h

/-- The quotient-safe raw Fourier Laplacian preserves addition. -/
theorem h3SpectralScalarLaplacianRawFourierL2_add
    (G H : H3SpectralScalarState) :
    h3SpectralScalarLaplacianRawFourierL2 (G + H)
      =
    h3SpectralScalarLaplacianRawFourierL2 G
      +
    h3SpectralScalarLaplacianRawFourierL2 H := by
  have h :=
    h3SpectralScalarLaplacianRawFourierL2_sub
      G (-H)
  rw [sub_neg_eq_add] at h
  rw [h3SpectralScalarLaplacianRawFourierL2_neg] at h
  simpa using h

/-- The quotient-safe raw Fourier Laplacian is real homogeneous. -/
theorem h3SpectralScalarLaplacianRawFourierL2_smul_real
    (c : ℝ)
    (G : H3SpectralScalarState) :
    h3SpectralScalarLaplacianRawFourierL2 (c • G)
      =
    c • h3SpectralScalarLaplacianRawFourierL2 G := by
  apply MeasureTheory.Lp.ext

  have hLeft :=
    h3SpectralScalarLaplacianRawFourierL2_ae (c • G)

  have hRight :=
    h3SpectralScalarLaplacianRawFourierL2_ae G

  have hIn :=
    MeasureTheory.Lp.coeFn_smul c G

  have hOut :=
    MeasureTheory.Lp.coeFn_smul
      c
      (h3SpectralScalarLaplacianRawFourierL2 G)

  filter_upwards [hLeft, hRight, hIn, hOut] with
      ξ hLeftξ hRightξ hInξ hOutξ

  simp only [Pi.smul_apply] at hInξ hOutξ
  rw [hLeftξ, hOutξ, hRightξ, hInξ]
  rw [Complex.real_smul, Complex.real_smul]
  ring

/-- Raw Fourier Laplacian on weighted H³ scalar data as a real linear map. -/
noncomputable def h3SpectralScalarLaplacianRawFourierL2LinearMap :
    H3SpectralScalarState →ₗ[ℝ] H3FourierComplexL2 where
  toFun := h3SpectralScalarLaplacianRawFourierL2
  map_add' := h3SpectralScalarLaplacianRawFourierL2_add
  map_smul' := h3SpectralScalarLaplacianRawFourierL2_smul_real

/-- Raw Fourier Laplacian on weighted H³ scalar data as a contractive real
continuous linear map. -/
noncomputable def h3SpectralScalarLaplacianRawFourierL2CLM :
    H3SpectralScalarState →L[ℝ] H3FourierComplexL2 :=
  h3SpectralScalarLaplacianRawFourierL2LinearMap.mkContinuous
    1
    (fun G => by
      change
        ‖h3SpectralScalarLaplacianRawFourierL2 G‖
          ≤
        1 * ‖G‖
      simpa using
        norm_h3SpectralScalarLaplacianRawFourierL2_le G)

@[simp]
theorem h3SpectralScalarLaplacianRawFourierL2CLM_apply
    (G : H3SpectralScalarState) :
    h3SpectralScalarLaplacianRawFourierL2CLM G
      =
    h3SpectralScalarLaplacianRawFourierL2 G :=
  rfl

end

end Euclidean
end Bridge
end PrimeTensor
