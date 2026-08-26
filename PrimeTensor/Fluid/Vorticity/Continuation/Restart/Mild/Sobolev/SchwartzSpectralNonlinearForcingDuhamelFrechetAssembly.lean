import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralNonlinearForcingDuhamelCoordinateC1
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Bridge.Energy
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Fréchet assembly for the nonlinear Duhamel reconstruction

The preceding checkpoint proves ordinary `C¹` regularity along each of the
three Euclidean coordinate lines, and the preceding continuity checkpoint
proves that the corresponding integrated coordinate derivatives are continuous
in the spatial point.

This file performs the finite-dimensional bookkeeping needed to turn those
three scalar coordinate derivatives into one real continuous linear map on
`H3FourierPoint3`.

For a triple `D : Fin 3 → ℂ`, the assembled operator is

  h ↦ ∑ j, h_j • D_j.

At strictly positive heat lag, the already-established spatial `C³`
reconstruction is genuinely Fréchet differentiable.  Its Fréchet derivative
agrees with the assembled operator because both agree on the three canonical
coordinate directions and every point of `H3FourierPoint3` is the sum of its
three coordinate components.

The same assembler applied to the time-integrated coordinate derivatives gives
a continuous candidate Fréchet derivative field for the full Duhamel term.
The next checkpoint can therefore pass the full Fréchet derivative through the
time integral with Mathlib's parametric-integral theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Filter
open scoped Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingDuhamelFrechetAssembly
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Coordinate evaluation on the Euclidean Fourier carrier, bundled as a
continuous real-linear functional. -/
noncomputable def h3FourierCoordinateCLM
    (a : PrimeTensor.Axis Depth.three) :
    H3FourierPoint3 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj a : Point3 →L[ℝ] ℝ).comp
    h3FourierToPoint3CLM

@[simp]
theorem h3FourierCoordinateCLM_apply
    (a : PrimeTensor.Axis Depth.three)
    (h : H3FourierPoint3) :
    h3FourierCoordinateCLM a h = h a := by
  rfl

/-- For a fixed coordinate functional, multiplication by a complex coefficient
is a continuous real-linear map from the coefficient to the resulting spatial
continuous linear map. -/
noncomputable def h3FourierCoordinateLiftCLM
    (a : PrimeTensor.Axis Depth.three) :
    ℂ →L[ℝ] (H3FourierPoint3 →L[ℝ] ℂ) :=
  LinearMap.toContinuousLinearMap
    ((h3FourierCoordinateCLM a).smulRightₗ :
      ℂ →ₗ[ℝ] (H3FourierPoint3 →L[ℝ] ℂ))

@[simp]
theorem h3FourierCoordinateLiftCLM_apply
    (a : PrimeTensor.Axis Depth.three)
    (z : ℂ)
    (h : H3FourierPoint3) :
    h3FourierCoordinateLiftCLM a z h = (h a) • z := by
  rfl

/-- Assemble three complex coordinate derivatives into one continuous
real-linear functional on the Euclidean Fourier carrier. -/
noncomputable def h3AssembleCoordinateDerivative
    (D : Fin 3 → ℂ) :
    H3FourierPoint3 →L[ℝ] ℂ :=
  ∑ j : Fin 3,
    h3FourierCoordinateLiftCLM (h3AxisOfFin3 j) (D j)

@[simp]
theorem h3AssembleCoordinateDerivative_apply
    (D : Fin 3 → ℂ)
    (h : H3FourierPoint3) :
    h3AssembleCoordinateDerivative D h
      =
    ∑ j : Fin 3,
      (h (h3AxisOfFin3 j)) • D j := by
  simp [h3AssembleCoordinateDerivative]


/-- The three conventional H3 axes are pairwise distinct. -/
theorem h3_xAxis_ne_yAxis : xAxis ≠ yAxis := by
  intro h
  change
    (PrimeTensor.Axis.first : PrimeTensor.Axis Depth.three) =
      PrimeTensor.Axis.next
        (PrimeTensor.Axis.first : PrimeTensor.Axis Depth.two)
    at h
  cases h

theorem h3_xAxis_ne_zAxis : xAxis ≠ zAxis := by
  intro h
  change
    (PrimeTensor.Axis.first : PrimeTensor.Axis Depth.three) =
      PrimeTensor.Axis.next
        (PrimeTensor.Axis.next
          (PrimeTensor.Axis.first : PrimeTensor.Axis Depth.one))
    at h
  cases h

theorem h3_yAxis_ne_zAxis : yAxis ≠ zAxis := by
  intro h
  have hRank :=
    congrArg
      (fun a : PrimeTensor.Axis Depth.three => axisRank a)
      h
  norm_num [axisRank, yAxis, zAxis] at hRank

/-- Concrete off-diagonal coordinate values for the canonical H3 axes.
These are stated directly for `axisDirection` because coercion through
`h3FourierAxisDirection` unfolds to this form in the finite-dimensional
coordinate calculations below. -/
@[simp]
theorem axisDirection_y_x_h3 : axisDirection yAxis xAxis = 0 :=
  axisDirection_other h3_xAxis_ne_yAxis

@[simp]
theorem axisDirection_z_x_h3 : axisDirection zAxis xAxis = 0 :=
  axisDirection_other h3_xAxis_ne_zAxis

@[simp]
theorem axisDirection_x_y_h3 : axisDirection xAxis yAxis = 0 :=
  axisDirection_other h3_xAxis_ne_yAxis.symm

@[simp]
theorem axisDirection_z_y_h3 : axisDirection zAxis yAxis = 0 :=
  axisDirection_other h3_yAxis_ne_zAxis

@[simp]
theorem axisDirection_x_z_h3 : axisDirection xAxis zAxis = 0 :=
  axisDirection_other h3_xAxis_ne_zAxis.symm

@[simp]
theorem axisDirection_y_z_h3 : axisDirection yAxis zAxis = 0 :=
  axisDirection_other h3_yAxis_ne_zAxis.symm

@[simp]
theorem h3FourierAxisDirection_x_x :
    h3FourierAxisDirection xAxis xAxis = 1 := by
  change axisDirection xAxis xAxis = 1
  exact axisDirection_same xAxis

@[simp]
theorem h3FourierAxisDirection_y_y :
    h3FourierAxisDirection yAxis yAxis = 1 := by
  change axisDirection yAxis yAxis = 1
  exact axisDirection_same yAxis

@[simp]
theorem h3FourierAxisDirection_z_z :
    h3FourierAxisDirection zAxis zAxis = 1 := by
  change axisDirection zAxis zAxis = 1
  exact axisDirection_same zAxis

@[simp]
theorem h3FourierAxisDirection_y_x :
    h3FourierAxisDirection yAxis xAxis = 0 := by
  change axisDirection yAxis xAxis = 0
  exact axisDirection_other h3_xAxis_ne_yAxis

@[simp]
theorem h3FourierAxisDirection_z_x :
    h3FourierAxisDirection zAxis xAxis = 0 := by
  change axisDirection zAxis xAxis = 0
  exact axisDirection_other h3_xAxis_ne_zAxis

@[simp]
theorem h3FourierAxisDirection_x_y :
    h3FourierAxisDirection xAxis yAxis = 0 := by
  change axisDirection xAxis yAxis = 0
  exact axisDirection_other h3_xAxis_ne_yAxis.symm

@[simp]
theorem h3FourierAxisDirection_z_y :
    h3FourierAxisDirection zAxis yAxis = 0 := by
  change axisDirection zAxis yAxis = 0
  exact axisDirection_other h3_yAxis_ne_zAxis

@[simp]
theorem h3FourierAxisDirection_x_z :
    h3FourierAxisDirection xAxis zAxis = 0 := by
  change axisDirection xAxis zAxis = 0
  exact axisDirection_other h3_xAxis_ne_zAxis.symm

@[simp]
theorem h3FourierAxisDirection_y_z :
    h3FourierAxisDirection yAxis zAxis = 0 := by
  change axisDirection yAxis zAxis = 0
  exact axisDirection_other h3_yAxis_ne_zAxis.symm

/-- Every vector in the three-dimensional Euclidean Fourier carrier is the
sum of its three coordinate components along the canonical axis directions. -/
theorem h3FourierPoint_eq_sum_axis_components
    (h : H3FourierPoint3) :
    h
      =
    ∑ j : Fin 3,
      (h (h3AxisOfFin3 j)) •
        h3FourierAxisDirection (h3AxisOfFin3 j) := by
  ext a
  rw [Fin.sum_univ_three]
  simp only [h3AxisOfFin3_zero, h3AxisOfFin3_one, h3AxisOfFin3_two,
    PiLp.add_apply, PiLp.smul_apply]
  cases a with
  | first =>
      change h xAxis =
        h xAxis • h3FourierAxisDirection xAxis xAxis +
          h yAxis • h3FourierAxisDirection yAxis xAxis +
        h zAxis • h3FourierAxisDirection zAxis xAxis
      simp
  | next a =>
      cases a with
      | first =>
          change h yAxis =
            h xAxis • h3FourierAxisDirection xAxis yAxis +
              h yAxis • h3FourierAxisDirection yAxis yAxis +
            h zAxis • h3FourierAxisDirection zAxis yAxis
          simp
      | next a =>
          cases a with
          | first =>
              change h zAxis =
                h xAxis • h3FourierAxisDirection xAxis zAxis +
                  h yAxis • h3FourierAxisDirection yAxis zAxis +
                h zAxis • h3FourierAxisDirection zAxis zAxis
              simp

/-- The assembled operator applied to a canonical coordinate direction returns
exactly the corresponding coordinate coefficient. -/
@[simp]
theorem h3AssembleCoordinateDerivative_axis
    (D : Fin 3 → ℂ)
    (j : Fin 3) :
    h3AssembleCoordinateDerivative D
        (h3FourierAxisDirection (h3AxisOfFin3 j))
      =
    D j := by
  rw [h3AssembleCoordinateDerivative_apply, Fin.sum_univ_three]
  fin_cases j
  · change
      h3FourierAxisDirection xAxis xAxis • D 0 +
          h3FourierAxisDirection xAxis yAxis • D 1 +
        h3FourierAxisDirection xAxis zAxis • D 2 = D 0
    simp
  · change
      h3FourierAxisDirection yAxis xAxis • D 0 +
          h3FourierAxisDirection yAxis yAxis • D 1 +
        h3FourierAxisDirection yAxis zAxis • D 2 = D 1
    simp
  · change
      h3FourierAxisDirection zAxis xAxis • D 0 +
          h3FourierAxisDirection zAxis yAxis • D 1 +
        h3FourierAxisDirection zAxis zAxis • D 2 = D 2
    simp

/-- Full fixed-lag Fréchet derivative assembled from the three previously
constructed first-coordinate inverse-Fourier representatives. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    H3FourierPoint3 →L[ℝ] ℂ :=
  h3AssembleCoordinateDerivative
    (fun j : Fin 3 =>
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ U V i j x)

/-- At positive heat lag, the coordinatewise assembly is exactly Mathlib's
Fréchet derivative of the classical `C³` reconstruction. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative_eq_fderiv
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative
        ν τ U V i x
      =
    fderiv ℝ
      (h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ U V i)
      x := by
  let f : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatC3Representative
      ν τ U V i

  have hfC1 : ContDiff ℝ 1 f := by
    exact
      (h3RawFinLerayOuterProductDivergenceHeatC3Representative_contDiff_three
        hν hτ U V i).of_le (by norm_num)

  have hfDiff : DifferentiableAt ℝ f x :=
    hfC1.differentiable_one.differentiableAt

  have hAxis
      (j : Fin 3) :
      (fderiv ℝ f x)
          (h3FourierAxisDirection (h3AxisOfFin3 j))
        =
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ U V i j x := by
    have hFrechetLine :=
      hfDiff.hasFDerivAt.hasLineDerivAt
        (h3FourierAxisDirection (h3AxisOfFin3 j))

    have hCoordinateLine :
        HasLineDerivAt ℝ f
          (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
            ν τ U V i j x)
          x
          (h3FourierAxisDirection (h3AxisOfFin3 j)) := by
      exact
        h3RawFinLerayOuterProductDivergenceHeatC3Representative_hasDerivAt_coordinate
          hν hτ U V i j x

    exact hFrechetLine.unique hCoordinateLine

  apply ContinuousLinearMap.ext
  intro h

  unfold h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative
  rw [h3AssembleCoordinateDerivative_apply]

  calc
    (∑ j : Fin 3,
        (h (h3AxisOfFin3 j)) •
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
            ν τ U V i j x)
        =
      ∑ j : Fin 3,
        (h (h3AxisOfFin3 j)) •
          (fderiv ℝ f x)
            (h3FourierAxisDirection (h3AxisOfFin3 j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hAxis j]
    _ =
      (fderiv ℝ f x)
        (∑ j : Fin 3,
          (h (h3AxisOfFin3 j)) •
            h3FourierAxisDirection (h3AxisOfFin3 j)) := by
          rw [map_sum]
          simp only [map_smul]
    _ = (fderiv ℝ f x) h := by
          rw [← h3FourierPoint_eq_sum_axis_components h]

/-- In particular, the assembled fixed-lag operator is a genuine Fréchet
 derivative witness. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Representative_hasFDerivAt
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    HasFDerivAt
      (h3RawFinLerayOuterProductDivergenceHeatC3Representative
        ν τ U V i)
      (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative
        ν τ U V i x)
      x := by
  have hfC1 :
      ContDiff ℝ 1
        (h3RawFinLerayOuterProductDivergenceHeatC3Representative
          ν τ U V i) :=
    (h3RawFinLerayOuterProductDivergenceHeatC3Representative_contDiff_three
      hν hτ U V i).of_le (by norm_num)

  rw [h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative_eq_fderiv
    hν hτ U V i x]
  exact hfC1.differentiable_one.differentiableAt.hasFDerivAt

/-- Continuous candidate Fréchet derivative field of the full nonlinear
Duhamel reconstruction, assembled from the three integrated coordinate
derivatives. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    H3FourierPoint3 →L[ℝ] ℂ :=
  h3AssembleCoordinateDerivative
    (fun j : Fin 3 =>
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
        ν t U V i j x)

/-- The assembled Duhamel Fréchet-derivative candidate has the already-proved
coordinate derivatives as its values on the canonical axes. -/
@[simp]
theorem h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel_axis
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t U V i x
        (h3FourierAxisDirection (h3AxisOfFin3 j))
      =
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
      ν t U V i j x := by
  unfold h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
  exact h3AssembleCoordinateDerivative_axis
    (fun k : Fin 3 =>
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
        ν t U V i k x)
    j

/-- The assembled full Duhamel derivative field is continuous in the spatial
point. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel_continuous
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s ∈ Set.Ioo (0 : ℝ) t, ‖U s‖ ≤ MU)
    (hV : ∀ s ∈ Set.Ioo (0 : ℝ) t, ‖V s‖ ≤ MV)
    (i : Fin 3) :
    Continuous
      (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t U V i) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
  unfold h3AssembleCoordinateDerivative

  apply continuous_finsetSum
  intro j hj

  exact
    (h3FourierCoordinateLiftCLM (h3AxisOfFin3 j)).continuous.comp
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel_continuous
        hν ht hMU hMV U V hUcont hVcont hU hV i j)

end
end Euclidean
end Bridge
end PrimeTensor
