import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.HessianAssembly
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Second.Coordinate.Spatial.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Time.Integrability
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Fixed-lag second Fréchet derivative

At strictly positive heat lag, the physical nonlinear forcing reconstruction is
already `C³`.  The first Fréchet layer identified its derivative with the
assembled three-coordinate inverse-Fourier derivative.

This file identifies the derivative of that first-Fréchet field with the
rank-two Hessian assembled from the nine mixed second-coordinate
representatives.

The key point is finite-dimensional uniqueness.  On an outer canonical axis
`k`, evaluate the derivative of the `fderiv` field on an inner canonical axis
`j`.  This scalar line derivative is uniquely identified by the existing
mixed `j,k` second-coordinate theorem.  Agreement on the three inner axes gives
equality of the inner continuous linear maps; agreement on the three outer
axes then gives equality of the full Hessian.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Filter
open scoped Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterFixedLagHessian
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The fixed-lag rank-two Fréchet derivative candidate assembled from the nine
mixed second-coordinate inverse-Fourier representatives. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRepresentative
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    H3FourierPoint3 →L[ℝ]
      (H3FourierPoint3 →L[ℝ] ℂ) :=
  h3AssembleSecondCoordinateDerivative
    (fun j k : Fin 3 =>
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν τ U V i j k x)

/-- On an outer canonical direction, the assembled Hessian is exactly the
first-order assembler applied to the corresponding column of mixed second
derivatives. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRepresentative_axis
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRepresentative
        ν τ U V i x
        (h3FourierAxisDirection (h3AxisOfFin3 k))
      =
    h3AssembleCoordinateDerivative
      (fun j : Fin 3 =>
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν τ U V i j k x) := by
  apply h3ContinuousLinearMap_ext_axes
  intro j

  rw [h3AssembleCoordinateDerivative_axis]

  unfold
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRepresentative

  exact
    h3AssembleSecondCoordinateDerivative_axis_axis
      (fun j k : Fin 3 =>
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν τ U V i j k x)
      j k

/-- At positive heat lag, the assembled rank-two representative is exactly the
Fréchet derivative of the first-Fréchet representative field. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRepresentative_eq_fderiv
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRepresentative
        ν τ U V i x
      =
    fderiv ℝ
      (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative
        ν τ U V i)
      x := by
  let f : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatC3Representative
      ν τ U V i

  let G : H3FourierPoint3 → (H3FourierPoint3 →L[ℝ] ℂ) :=
    h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative
      ν τ U V i

  let H :
      H3FourierPoint3 →
        (H3FourierPoint3 →L[ℝ] (H3FourierPoint3 →L[ℝ] ℂ)) :=
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRepresentative
      ν τ U V i

  have hfC3 : ContDiff ℝ 3 f := by
    dsimp only [f]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Representative_contDiff_three
        hν hτ U V i

  have hfC2 : ContDiff ℝ (1 + 1) f := by
    exact hfC3.of_le (by norm_num)

  have hfdC1 : ContDiff ℝ 1 (fderiv ℝ f) := by
    exact (contDiff_succ_iff_fderiv.mp hfC2).2.2

  have hfdDiffAt :
      DifferentiableAt ℝ (fderiv ℝ f) x :=
    hfdC1.differentiable_one.differentiableAt

  have hGEq :
      G = fderiv ℝ f := by
    funext y
    dsimp only [G, f]
    exact
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative_eq_fderiv
        hν hτ U V i y

  have hScalarAxis
      (j k : Fin 3) :
      (fderiv ℝ (fderiv ℝ f) x)
          (h3FourierAxisDirection (h3AxisOfFin3 k))
          (h3FourierAxisDirection (h3AxisOfFin3 j))
        =
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν τ U V i j k x := by
    let ej : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 j)

    let ek : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 k)

    have hEvalFDeriv :
        HasFDerivAt
          (fun y : H3FourierPoint3 => (fderiv ℝ f y) ej)
          ((fderiv ℝ (fderiv ℝ f) x).flip ej)
          x := by
      have h :=
        hfdDiffAt.hasFDerivAt.clm_apply
          (hasFDerivAt_const ej x)
      simpa using h

    have hEvalLine :
        HasDerivAt
          (fun r : ℝ => (fderiv ℝ f (x + r • ek)) ej)
          ((fderiv ℝ (fderiv ℝ f) x) ek ej)
          0 := by
      have hLine := hEvalFDeriv.hasLineDerivAt ek
      change
        HasDerivAt
          (fun r : ℝ => (fderiv ℝ f (x + r • ek)) ej)
          ((fderiv ℝ (fderiv ℝ f) x) ek ej)
          0
        at hLine
      exact hLine

    have hEvalEq
        (r : ℝ) :
        (fderiv ℝ f (x + r • ek)) ej
          =
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν τ U V i j (x + r • ek) := by
      rw [
        ←
          h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative_eq_fderiv
            hν hτ U V i (x + r • ek)
      ]
      unfold
        h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative
      dsimp only [ej]
      exact
        h3AssembleCoordinateDerivative_axis
          (fun m : Fin 3 =>
            h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
              ν τ U V i m (x + r • ek))
          j

    have hEvalLine' :
        HasDerivAt
          (fun r : ℝ =>
            h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
              ν τ U V i j (x + r • ek))
          ((fderiv ℝ (fderiv ℝ f) x) ek ej)
          0 := by
      simpa only [hEvalEq] using hEvalLine

    have hMixed :
        HasDerivAt
          (fun r : ℝ =>
            h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
              ν τ U V i j (x + r • ek))
          (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
            ν τ U V i j k x)
          0 := by
      dsimp only [ek]
      exact
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_hasDerivAt_secondCoordinate
          hν hτ U V i j k x

    have hUnique := hEvalLine'.unique hMixed
    simpa only [ej, ek] using hUnique

  have hOuterAxis
      (k : Fin 3) :
      (fderiv ℝ (fderiv ℝ f) x)
          (h3FourierAxisDirection (h3AxisOfFin3 k))
        =
      h3AssembleCoordinateDerivative
        (fun j : Fin 3 =>
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
            ν τ U V i j k x) := by
    apply h3ContinuousLinearMap_ext_axes
    intro j

    rw [h3AssembleCoordinateDerivative_axis]
    exact hScalarAxis j k

  have hHEq :
      H x = fderiv ℝ (fderiv ℝ f) x := by
    apply ContinuousLinearMap.ext
    intro h

    rw [h3FourierPoint_eq_sum_axis_components h]
    rw [map_sum, map_sum]
    simp only [map_smul]

    apply Finset.sum_congr rfl
    intro k hk

    dsimp only [H]
    rw [
      h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRepresentative_axis
    ]
    rw [hOuterAxis k]

  change H x = fderiv ℝ G x
  rw [hGEq]
  exact hHEq

/-- Consequently, the fixed-lag first-Fréchet representative has the assembled
rank-two representative as a genuine Fréchet derivative. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative_hasFDerivAt_secondFrechet
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    HasFDerivAt
      (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative
        ν τ U V i)
      (h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRepresentative
        ν τ U V i x)
      x := by
  let f : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatC3Representative
      ν τ U V i

  have hfC3 : ContDiff ℝ 3 f := by
    dsimp only [f]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Representative_contDiff_three
        hν hτ U V i

  have hfC2 : ContDiff ℝ (1 + 1) f := by
    exact hfC3.of_le (by norm_num)

  have hfdC1 : ContDiff ℝ 1 (fderiv ℝ f) := by
    exact (contDiff_succ_iff_fderiv.mp hfC2).2.2

  let G : H3FourierPoint3 → (H3FourierPoint3 →L[ℝ] ℂ) :=
    h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative
      ν τ U V i

  let H :
      H3FourierPoint3 →
        (H3FourierPoint3 →L[ℝ] (H3FourierPoint3 →L[ℝ] ℂ)) :=
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRepresentative
      ν τ U V i

  have hGEq :
      G = fderiv ℝ f := by
    funext y
    dsimp only [G, f]
    exact
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative_eq_fderiv
        hν hτ U V i y

  have hHEqRaw :=
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRepresentative_eq_fderiv
      hν hτ U V i x

  change H x = fderiv ℝ G x at hHEqRaw

  have hHEq :
      H x = fderiv ℝ (fderiv ℝ f) x := by
    rw [hGEq] at hHEqRaw
    exact hHEqRaw

  change HasFDerivAt G (H x) x
  rw [hGEq, hHEq]
  exact
    hfdC1.differentiable_one.differentiableAt.hasFDerivAt

end
end Euclidean
end Bridge
end PrimeTensor
