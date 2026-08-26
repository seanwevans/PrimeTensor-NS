import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Coordinate C¹ regularity of the nonlinear Duhamel reconstruction

The preceding two checkpoints prove that each Euclidean coordinate derivative
passes through the full retarded Duhamel integral and that the resulting
integrated derivative field is continuous in space.

This file packages those facts into ordinary one-dimensional `C¹` regularity
along every affine coordinate line.  This is the clean intermediate interface
between the analytic differentiation-under-the-integral argument and the
finite-dimensional Fréchet `C¹` packaging used downstream.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Filter
open scoped Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingDuhamelCoordinateC1
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The Duhamel coordinate derivative identity at an arbitrary parameter value
of the affine coordinate line. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_hasDerivAt_coordinate_at
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
    (i j : Fin 3)
    (x : H3FourierPoint3)
    (r : ℝ) :
    HasDerivAt
      (fun q : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t U V i
          (x + q • h3FourierAxisDirection (h3AxisOfFin3 j)))
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
        ν t U V i j
        (x + r • h3FourierAxisDirection (h3AxisOfFin3 j)))
      r := by
  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 j)

  have h0 :
      HasDerivAt
        (fun q : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν t U V i ((x + r • e) + q • e))
        (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
          ν t U V i j (x + r • e))
        0 := by
    simpa [e] using
      (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_hasDerivAt_coordinate
        hν ht hMU hMV U V hUcont hVcont hU hV i j (x + r • e))

  have hShift :
      HasDerivAt (fun q : ℝ => q - r) 1 r := by
    simpa using (hasDerivAt_id r).sub_const r

  have hComp := h0.scomp_of_eq r hShift (by simp)

  have hPoint (q : ℝ) :
      (x + r • e) + (q - r) • e = x + q • e := by
    rw [sub_smul]
    abel

  have hFunEq :
      (fun q : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t U V i (x + q • e))
        =ᶠ[𝓝 r]
      ((fun q : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν t U V i ((x + r • e) + q • e)) ∘
        fun q : ℝ => q - r) := by
    filter_upwards with q
    simp only [Function.comp_apply]
    rw [hPoint q]

  have hTransport := hComp.congr_of_eventuallyEq hFunEq

  have hDerivEq :
      (1 : ℝ) •
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
            ν t U V i j (x + r • e)
        =
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
        ν t U V i j (x + r • e) :=
    one_smul ℝ _

  have hFinal := hTransport.congr_deriv hDerivEq
  simpa only [e] using hFinal

/-- Equality form of the arbitrary-parameter coordinate derivative. -/
theorem deriv_h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_coordinate_at
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
    (i j : Fin 3)
    (x : H3FourierPoint3)
    (r : ℝ) :
    deriv
      (fun q : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t U V i
          (x + q • h3FourierAxisDirection (h3AxisOfFin3 j)))
      r
      =
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
      ν t U V i j
      (x + r • h3FourierAxisDirection (h3AxisOfFin3 j)) := by
  exact
    (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_hasDerivAt_coordinate_at
      hν ht hMU hMV U V hUcont hVcont hU hV i j x r).deriv

/-- Every affine Euclidean coordinate line through the nonlinear Duhamel
reconstruction is an ordinary `C¹` function of its line parameter. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_coordinate_contDiff_one
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
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    ContDiff ℝ 1
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t U V i
          (x + r • h3FourierAxisDirection (h3AxisOfFin3 j))) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro r
    exact
      (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_hasDerivAt_coordinate_at
        hν ht hMU hMV U V hUcont hVcont hU hV i j x r).differentiableAt
  · have hDerivEq :
        deriv
          (fun r : ℝ =>
            h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
              ν t U V i
              (x + r • h3FourierAxisDirection (h3AxisOfFin3 j)))
          =
        fun r : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
            ν t U V i j
            (x + r • h3FourierAxisDirection (h3AxisOfFin3 j)) := by
      funext r
      exact
        deriv_h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_coordinate_at
          hν ht hMU hMV U V hUcont hVcont hU hV i j x r
    rw [hDerivEq]
    exact
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel_continuous
        hν ht hMU hMV U V hUcont hVcont hU hV i j).comp (by fun_prop)

end
end Euclidean
end Bridge
end PrimeTensor
