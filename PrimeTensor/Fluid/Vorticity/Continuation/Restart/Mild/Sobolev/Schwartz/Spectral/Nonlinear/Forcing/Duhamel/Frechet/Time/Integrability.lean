import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Assembly
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Time integrability of the full Fréchet derivative of the nonlinear Duhamel path

The preceding Fréchet-assembly checkpoint packages the three coordinate
spatial derivatives into a single real continuous linear map on
`H3FourierPoint3`, and identifies that assembled operator with the genuine
fixed-lag Fréchet derivative.

This file controls that operator in the retarded source-time variable.  The
operator norm is bounded by three copies of the already-established
coordinate derivative majorant, hence remains integrable up to the terminal
Duhamel endpoint.  Consequently the full Fréchet-derivative retarded path is
Bochner integrable, and its time integral is exactly the assembled Duhamel
Fréchet derivative from the preceding file.

The next checkpoint can therefore invoke Mathlib's Fréchet
parametric-integral theorem directly.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingDuhamelFrechetTimeIntegrability
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A coordinate of an `L²` Euclidean vector is bounded by the full Euclidean
norm. -/
theorem norm_h3FourierCoordinate_le_norm
    (h : H3FourierPoint3)
    (a : PrimeTensor.Axis Depth.three) :
    ‖h a‖ ≤ ‖h‖ := by
  have hsq :
      ‖h a‖ ^ 2
        ≤
      ∑ i : PrimeTensor.Axis Depth.three, ‖h i‖ ^ 2 := by
    exact
      Finset.single_le_sum
        (fun i _ => sq_nonneg ‖h i‖)
        (Finset.mem_univ a)

  rw [← EuclideanSpace.norm_sq_eq] at hsq
  nlinarith [norm_nonneg (h a), norm_nonneg h]

/-- Multiplying one coordinate functional by a complex coefficient has
operator norm at most the coefficient norm. -/
theorem norm_h3FourierCoordinateLiftCLM_le
    (a : PrimeTensor.Axis Depth.three)
    (z : ℂ) :
    ‖h3FourierCoordinateLiftCLM a z‖ ≤ ‖z‖ := by
  apply
    ContinuousLinearMap.opNorm_le_bound
      (h3FourierCoordinateLiftCLM a z)
      (norm_nonneg z)

  intro h
  rw [h3FourierCoordinateLiftCLM_apply, norm_smul]

  calc
    ‖h a‖ * ‖z‖
        ≤
      ‖h‖ * ‖z‖ := by
        exact
          mul_le_mul_of_nonneg_right
            (norm_h3FourierCoordinate_le_norm h a)
            (norm_nonneg z)
    _ = ‖z‖ * ‖h‖ := by ring

/-- The retarded full Fréchet derivative, assembled pointwise in source time
from the three already-constructed coordinate derivative paths. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (s : ℝ) :
    H3FourierPoint3 →L[ℝ] ℂ :=
  h3AssembleCoordinateDerivative
    (fun j : Fin 3 =>
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν t U V i j x s)

/-- Evaluation of the full retarded Fréchet derivative on a canonical axis is
exactly the corresponding scalar coordinate derivative path. -/
@[simp]
theorem h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_axis
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3)
    (s : ℝ) :
    h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
        ν t U V i x s
        (h3FourierAxisDirection (h3AxisOfFin3 j))
      =
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
      ν t U V i j x s := by
  unfold h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
  exact
    h3AssembleCoordinateDerivative_axis
      (fun k : Fin 3 =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν t U V i k x s)
      j

/-- The full Fréchet operator norm costs at most the sum of the three
coordinate derivative bounds.  In dimension three this is exactly three
copies of the established scalar path majorant. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_le
    {ν t MU MV s : ℝ}
    (hν : 0 < ν)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hs : s ∈ Set.Ioo (0 : ℝ) t)
    (hU : ‖U s‖ ≤ MU)
    (hV : ‖V s‖ ≤ MV)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
        ν t U V i x s‖
      ≤
    3 * h3NonlinearForcingHeatFirstDerivativePathMajorant
      ν t MU MV s := by
  unfold h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
  unfold h3AssembleCoordinateDerivative

  calc
    ‖∑ j : Fin 3,
        h3FourierCoordinateLiftCLM
          (h3AxisOfFin3 j)
          (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν t U V i j x s)‖
        ≤
      ∑ j : Fin 3,
        ‖h3FourierCoordinateLiftCLM
          (h3AxisOfFin3 j)
          (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν t U V i j x s)‖ := by
          exact
            norm_sum_le
              Finset.univ
              (fun j =>
                h3FourierCoordinateLiftCLM
                  (h3AxisOfFin3 j)
                  (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
                    ν t U V i j x s))

    _ ≤
      ∑ j : Fin 3,
        ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν t U V i j x s‖ := by
          apply Finset.sum_le_sum
          intro j hj
          exact
            norm_h3FourierCoordinateLiftCLM_le
              (h3AxisOfFin3 j)
              (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
                ν t U V i j x s)

    _ ≤
      ∑ _j : Fin 3,
        h3NonlinearForcingHeatFirstDerivativePathMajorant
          ν t MU MV s := by
          apply Finset.sum_le_sum
          intro j hj
          exact
            norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_le_pathMajorant
              hν hMU hMV U V hs hU hV i j x

    _ =
      3 * h3NonlinearForcingHeatFirstDerivativePathMajorant
        ν t MU MV s := by
          rw [Fin.sum_univ_three]
          ring

set_option maxHeartbeats 1000000 in
/-- The full Fréchet derivative retarded path is Bochner integrable on the
open Duhamel interval.  We prove this structurally as a finite sum of
continuous-linear images of the already-integrable scalar coordinate paths. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_integrableOn_Ioo_of_continuous
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
    (i : Fin 3)
    (x : H3FourierPoint3) :
    IntegrableOn
      (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
        ν t U V i x)
      (Set.Ioo (0 : ℝ) t)
      volume := by
  change
    Integrable
      (fun s : ℝ =>
        ∑ j : Fin 3,
          h3FourierCoordinateLiftCLM
            (h3AxisOfFin3 j)
            (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
              ν t U V i j x s))
      (volume.restrict (Set.Ioo (0 : ℝ) t))

  have hTerm
      (j : Fin 3) :
      Integrable
        (fun s : ℝ =>
          h3FourierCoordinateLiftCLM
            (h3AxisOfFin3 j)
            (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
              ν t U V i j x s))
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    have hScalarInt :
        Integrable
          (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν t U V i j x)
          (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
      change
        IntegrableOn
          (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
            ν t U V i j x)
          (Set.Ioo (0 : ℝ) t)
          volume
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
      exact
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_intervalIntegrable_of_continuous
          hν ht hMU hMV U V hUcont hVcont hU hV i j x

    exact
      (h3FourierCoordinateLiftCLM (h3AxisOfFin3 j)).integrable_comp
        hScalarInt

  exact
    integrable_finsetSum
      (μ := volume.restrict (Set.Ioo (0 : ℝ) t))
      (f :=
        (fun j : Fin 3 =>
          fun s : ℝ =>
            h3FourierCoordinateLiftCLM
              (h3AxisOfFin3 j)
              (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
                ν t U V i j x s) :
          Fin 3 → ℝ → (H3FourierPoint3 →L[ℝ] ℂ)))
      (Finset.univ : Finset (Fin 3))
      (by
        intro j hj
        exact hTerm j)

/-- Interval-integrable form of the preceding Bochner-integrability theorem. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_intervalIntegrable_of_continuous
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
    (i : Fin 3)
    (x : H3FourierPoint3) :
    IntervalIntegrable
      (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
        ν t U V i x)
      volume
      0
      t := by
  rw [
    intervalIntegrable_iff_integrableOn_Ioc_of_le ht,
    integrableOn_Ioc_iff_integrableOn_Ioo
  ]
  exact
    h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_integrableOn_Ioo_of_continuous
      hν ht hMU hMV U V hUcont hVcont hU hV i x

/-- Two real continuous linear maps on `H3FourierPoint3` are equal once they
agree on the three canonical coordinate directions. -/
theorem h3ContinuousLinearMap_ext_axes
    {L M : H3FourierPoint3 →L[ℝ] ℂ}
    (hAxis :
      ∀ j : Fin 3,
        L (h3FourierAxisDirection (h3AxisOfFin3 j))
          =
        M (h3FourierAxisDirection (h3AxisOfFin3 j))) :
    L = M := by
  apply ContinuousLinearMap.ext
  intro x

  rw [h3FourierPoint_eq_sum_axis_components x]
  rw [map_sum, map_sum]
  simp only [map_smul]

  apply Finset.sum_congr rfl
  intro j hj
  rw [hAxis j]

/-- Integrating the full retarded Fréchet derivative in source time gives
exactly the assembled Duhamel Fréchet derivative from the preceding
checkpoint. -/
theorem intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_eq_Duhamel
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
    (i : Fin 3)
    (x : H3FourierPoint3) :
    (∫ s in (0 : ℝ)..t,
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
        ν t U V i x s)
      =
    h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
      ν t U V i x := by
  have hFullInt :
      Integrable
        (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
          ν t U V i x)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    exact
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_integrableOn_Ioo_of_continuous
        hν ht hMU hMV U V hUcont hVcont hU hV i x

  apply h3ContinuousLinearMap_ext_axes
  intro j

  rw [h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel_axis]

  rw [intervalIntegral.integral_of_le ht]
  rw [← restrict_Ioo_eq_restrict_Ioc]

  rw [ContinuousLinearMap.integral_apply hFullInt]

  unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
  rw [intervalIntegral.integral_of_le ht]
  rw [← restrict_Ioo_eq_restrict_Ioc]

  apply integral_congr_ae
  filter_upwards with s
  exact
    h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_axis
      ν t U V i j x s

end
end Euclidean
end Bridge
end PrimeTensor
