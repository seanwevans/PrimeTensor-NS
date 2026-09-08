import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.DiffusionMass

/-!
# Four-term triangle bounds for the pressure-free vorticity RHS

`RHSExpansion` writes each pressure-free vorticity component as

    (diffusion₁ - diffusion₂) - (advection₁ - advection₂).

The diffusion and differentiated-advection masses are now independently
controlled.  This file inserts the last purely algebraic bridge: the norm of
that nested difference is bounded by the sum of the four component norms.

Weighted versions multiply by the nonnegative weak-test norm.  No integration
or endpoint estimate is performed here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- A four-term triangle inequality adapted to the curl-diffusion minus
curl-advection shape. -/
theorem norm_sub_sub_sub_le_four
    (a b c d : ℝ) :
    ‖(a - b) - (c - d)‖
      ≤
    (‖a‖ + ‖b‖) + (‖c‖ + ‖d‖) := by
  exact
    (norm_sub_le (a - b) (c - d)).trans
      (add_le_add
        (norm_sub_le a b)
        (norm_sub_le c d))

/-- Pointwise x-vorticity RHS triangle bound. -/
theorem norm_h3LoggedPreterminalVorticityRHSX_le_four
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    ‖h3LoggedPreterminalVorticityRHSX u s x‖
      ≤
    (
      ‖spatial3.d
          yAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (fun q =>
              (logSpaceTimeVectorField u s q).component zAxis))
          x‖
        +
      ‖spatial3.d
          zAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (fun q =>
              (logSpaceTimeVectorField u s q).component yAxis))
          x‖
    )
      +
    (
      ‖spatial3.d
          yAxis
          (fun q =>
            realAdvectionComponent
              (logSpaceTimeVectorField u) s q zAxis)
          x‖
        +
      ‖spatial3.d
          zAxis
          (fun q =>
            realAdvectionComponent
              (logSpaceTimeVectorField u) s q yAxis)
          x‖
    ) := by
  rw [
    h3LoggedPreterminalVorticityRHSX_eq_curlLaplacian_sub_curlAdvection
      hNS hs x
  ]
  exact norm_sub_sub_sub_le_four _ _ _ _

/-- Pointwise y-vorticity RHS triangle bound. -/
theorem norm_h3LoggedPreterminalVorticityRHSY_le_four
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    ‖h3LoggedPreterminalVorticityRHSY u s x‖
      ≤
    (
      ‖spatial3.d
          zAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (fun q =>
              (logSpaceTimeVectorField u s q).component xAxis))
          x‖
        +
      ‖spatial3.d
          xAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (fun q =>
              (logSpaceTimeVectorField u s q).component zAxis))
          x‖
    )
      +
    (
      ‖spatial3.d
          zAxis
          (fun q =>
            realAdvectionComponent
              (logSpaceTimeVectorField u) s q xAxis)
          x‖
        +
      ‖spatial3.d
          xAxis
          (fun q =>
            realAdvectionComponent
              (logSpaceTimeVectorField u) s q zAxis)
          x‖
    ) := by
  rw [
    h3LoggedPreterminalVorticityRHSY_eq_curlLaplacian_sub_curlAdvection
      hNS hs x
  ]
  exact norm_sub_sub_sub_le_four _ _ _ _

/-- Pointwise z-vorticity RHS triangle bound. -/
theorem norm_h3LoggedPreterminalVorticityRHSZ_le_four
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    ‖h3LoggedPreterminalVorticityRHSZ u s x‖
      ≤
    (
      ‖spatial3.d
          xAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (fun q =>
              (logSpaceTimeVectorField u s q).component yAxis))
          x‖
        +
      ‖spatial3.d
          yAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (fun q =>
              (logSpaceTimeVectorField u s q).component xAxis))
          x‖
    )
      +
    (
      ‖spatial3.d
          xAxis
          (fun q =>
            realAdvectionComponent
              (logSpaceTimeVectorField u) s q yAxis)
          x‖
        +
      ‖spatial3.d
          yAxis
          (fun q =>
            realAdvectionComponent
              (logSpaceTimeVectorField u) s q xAxis)
          x‖
    ) := by
  rw [
    h3LoggedPreterminalVorticityRHSZ_eq_curlLaplacian_sub_curlAdvection
      hNS hs x
  ]
  exact norm_sub_sub_sub_le_four _ _ _ _

/-- Weak-test-weighted x-vorticity RHS triangle bound. -/
theorem weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSX_le_four
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ψ : H3WeakTestFunction)
    (x : Point3) :
    ‖ψ x‖ * ‖h3LoggedPreterminalVorticityRHSX u s x‖
      ≤
    (
      ‖ψ x‖ *
        ‖spatial3.d
            yAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun q =>
                (logSpaceTimeVectorField u s q).component zAxis))
            x‖
        +
      ‖ψ x‖ *
        ‖spatial3.d
            zAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun q =>
                (logSpaceTimeVectorField u s q).component yAxis))
            x‖
    )
      +
    (
      ‖ψ x‖ *
        ‖spatial3.d
            yAxis
            (fun q =>
              realAdvectionComponent
                (logSpaceTimeVectorField u) s q zAxis)
            x‖
        +
      ‖ψ x‖ *
        ‖spatial3.d
            zAxis
            (fun q =>
              realAdvectionComponent
                (logSpaceTimeVectorField u) s q yAxis)
            x‖
    ) := by
  have h :=
    norm_h3LoggedPreterminalVorticityRHSX_le_four
      hNS hs x
  have hWeighted :=
    mul_le_mul_of_nonneg_left
      h
      (norm_nonneg (ψ x))
  simpa only [mul_add] using hWeighted

/-- Weak-test-weighted y-vorticity RHS triangle bound. -/
theorem weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSY_le_four
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ψ : H3WeakTestFunction)
    (x : Point3) :
    ‖ψ x‖ * ‖h3LoggedPreterminalVorticityRHSY u s x‖
      ≤
    (
      ‖ψ x‖ *
        ‖spatial3.d
            zAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun q =>
                (logSpaceTimeVectorField u s q).component xAxis))
            x‖
        +
      ‖ψ x‖ *
        ‖spatial3.d
            xAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun q =>
                (logSpaceTimeVectorField u s q).component zAxis))
            x‖
    )
      +
    (
      ‖ψ x‖ *
        ‖spatial3.d
            zAxis
            (fun q =>
              realAdvectionComponent
                (logSpaceTimeVectorField u) s q xAxis)
            x‖
        +
      ‖ψ x‖ *
        ‖spatial3.d
            xAxis
            (fun q =>
              realAdvectionComponent
                (logSpaceTimeVectorField u) s q zAxis)
            x‖
    ) := by
  have h :=
    norm_h3LoggedPreterminalVorticityRHSY_le_four
      hNS hs x
  have hWeighted :=
    mul_le_mul_of_nonneg_left
      h
      (norm_nonneg (ψ x))
  simpa only [mul_add] using hWeighted

/-- Weak-test-weighted z-vorticity RHS triangle bound. -/
theorem weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSZ_le_four
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (ψ : H3WeakTestFunction)
    (x : Point3) :
    ‖ψ x‖ * ‖h3LoggedPreterminalVorticityRHSZ u s x‖
      ≤
    (
      ‖ψ x‖ *
        ‖spatial3.d
            xAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun q =>
                (logSpaceTimeVectorField u s q).component yAxis))
            x‖
        +
      ‖ψ x‖ *
        ‖spatial3.d
            yAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3
              (fun q =>
                (logSpaceTimeVectorField u s q).component xAxis))
            x‖
    )
      +
    (
      ‖ψ x‖ *
        ‖spatial3.d
            xAxis
            (fun q =>
              realAdvectionComponent
                (logSpaceTimeVectorField u) s q yAxis)
            x‖
        +
      ‖ψ x‖ *
        ‖spatial3.d
            yAxis
            (fun q =>
              realAdvectionComponent
                (logSpaceTimeVectorField u) s q xAxis)
            x‖
    ) := by
  have h :=
    norm_h3LoggedPreterminalVorticityRHSZ_le_four
      hNS hs x
  have hWeighted :=
    mul_le_mul_of_nonneg_left
      h
      (norm_nonneg (ψ x))
  simpa only [mul_add] using hWeighted

end

end Euclidean
end Bridge
end PrimeTensor
