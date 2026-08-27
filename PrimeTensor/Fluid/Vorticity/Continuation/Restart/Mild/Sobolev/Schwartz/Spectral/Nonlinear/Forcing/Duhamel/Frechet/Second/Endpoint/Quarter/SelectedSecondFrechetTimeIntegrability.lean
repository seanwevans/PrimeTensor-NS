import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.FixedLagHessian
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.SelectedHessian
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedSecondCoordinateIntegrable
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Time.Integrability
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Selected second-Fréchet retarded path and source-time integrability

The fixed-lag Hessian is now a genuine Fréchet derivative.  This file packages
that Hessian along the selected retarded source-time path and proves the
operator-valued path is genuinely Bochner integrable on the complete Duhamel
interval.

Each rank-one mixed-coordinate Hessian lift has operator norm at most the norm
of its scalar coefficient.  Since there are nine mixed coordinates, the full
retarded Hessian is bounded by nine copies of the already-integrable selected
mixed-second-coordinate majorant.

Finally, integration of the Hessian path is identified with the previously
assembled selected second-Fréchet Duhamel field by evaluating successively on
the three canonical outer and inner coordinate directions.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedSecondFrechetTime
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-
Use the canonical operator-norm structures at both CLM levels.  This keeps the
retarded Hessian in exactly the normed type expected by Bochner integration
and by `ContinuousLinearMap.integrable_comp`.
-/
local instance h3SecondFrechetTimeFirstCLMNormedAddCommGroup :
    NormedAddCommGroup (H3FourierPoint3 →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance h3SecondFrechetTimeFirstCLMNormedSpace :
    NormedSpace ℝ (H3FourierPoint3 →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedSpace

local instance h3SecondFrechetTimeSecondCLMNormedAddCommGroup :
    NormedAddCommGroup
      (H3FourierPoint3 →L[ℝ] (H3FourierPoint3 →L[ℝ] ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance h3SecondFrechetTimeSecondCLMNormedSpace :
    NormedSpace ℝ
      (H3FourierPoint3 →L[ℝ] (H3FourierPoint3 →L[ℝ] ℂ)) :=
  ContinuousLinearMap.toNormedSpace

/-- The retarded second-Fréchet derivative assembled pointwise in source time
from the nine mixed second-coordinate paths. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (s : ℝ) :
    H3FourierPoint3 →L[ℝ]
      (H3FourierPoint3 →L[ℝ] ℂ) :=
  h3AssembleSecondCoordinateDerivative
    (fun j k : Fin 3 =>
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
        ν t U V i j k x s)

/-- Evaluation of the retarded Hessian on canonical outer and inner directions
recovers exactly the corresponding mixed second-coordinate path. -/
@[simp]
theorem h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath_axis_axis
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i j k : Fin 3)
    (x : H3FourierPoint3)
    (s : ℝ) :
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
        ν t U V i x s
        (h3FourierAxisDirection (h3AxisOfFin3 k))
        (h3FourierAxisDirection (h3AxisOfFin3 j))
      =
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
      ν t U V i j k x s := by
  unfold
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
  exact
    h3AssembleSecondCoordinateDerivative_axis_axis
      (fun j k : Fin 3 =>
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν t U V i j k x s)
      j k

/-- A single mixed-coordinate rank-one Hessian lift costs at most the norm of
its scalar coefficient. -/
theorem norm_h3FourierSecondCoordinateLiftCLM_le
    (j k : Fin 3)
    (z : ℂ) :
    ‖h3FourierSecondCoordinateLiftCLM j k z‖ ≤ ‖z‖ := by
  apply
    ContinuousLinearMap.opNorm_le_bound
      (h3FourierSecondCoordinateLiftCLM j k z)
      (norm_nonneg z)

  intro h

  have hEq :
      h3FourierSecondCoordinateLiftCLM j k z h
        =
      h3FourierCoordinateLiftCLM
        (h3AxisOfFin3 j)
        ((h (h3AxisOfFin3 k)) • z) := by
    apply ContinuousLinearMap.ext
    intro q
    simp only [
      h3FourierSecondCoordinateLiftCLM_apply,
      h3FourierCoordinateLiftCLM_apply,
      smul_smul
    ]
    rw [mul_comm]

  rw [hEq]

  calc
    ‖h3FourierCoordinateLiftCLM
        (h3AxisOfFin3 j)
        ((h (h3AxisOfFin3 k)) • z)‖
        ≤
      ‖(h (h3AxisOfFin3 k)) • z‖ :=
        norm_h3FourierCoordinateLiftCLM_le
          (h3AxisOfFin3 j)
          ((h (h3AxisOfFin3 k)) • z)
    _ =
      ‖h (h3AxisOfFin3 k)‖ * ‖z‖ := by
        rw [norm_smul]
    _ ≤
      ‖h‖ * ‖z‖ := by
        exact
          mul_le_mul_of_nonneg_right
            (norm_h3FourierCoordinate_le_norm h (h3AxisOfFin3 k))
            (norm_nonneg z)
    _ =
      ‖z‖ * ‖h‖ := by ring

/-- On every strict selected source-time slice, the full Hessian operator norm
is bounded by nine copies of the scalar mixed-second-coordinate majorant. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath_selectedRestart_le
    {ν A t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : s ∈ Set.Ioo (0 : ℝ) t)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
        ν t W W i x s‖
      ≤
    9 *
      h3SelectedSecondCoordinateDerivativePathMajorant
        ν A t hν U₀ hA hU₀ i s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  unfold
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
  unfold h3AssembleSecondCoordinateDerivative

  calc
    ‖∑ k : Fin 3,
        ∑ j : Fin 3,
          h3FourierSecondCoordinateLiftCLM j k
            (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
              ν t W W i j k x s)‖
        ≤
      ∑ k : Fin 3,
        ‖∑ j : Fin 3,
          h3FourierSecondCoordinateLiftCLM j k
            (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
              ν t W W i j k x s)‖ := by
          exact
            norm_sum_le
              Finset.univ
              (fun k : Fin 3 =>
                ∑ j : Fin 3,
                  h3FourierSecondCoordinateLiftCLM j k
                    (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
                      ν t W W i j k x s))
    _ ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          ‖h3FourierSecondCoordinateLiftCLM j k
            (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
              ν t W W i j k x s)‖ := by
          apply Finset.sum_le_sum
          intro k hk
          exact
            norm_sum_le
              Finset.univ
              (fun j : Fin 3 =>
                h3FourierSecondCoordinateLiftCLM j k
                  (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
                    ν t W W i j k x s))
    _ ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
            ν t W W i j k x s‖ := by
          apply Finset.sum_le_sum
          intro k hk
          apply Finset.sum_le_sum
          intro j hj
          exact
            norm_h3FourierSecondCoordinateLiftCLM_le
              j k
              (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
                ν t W W i j k x s)
    _ ≤
      ∑ _k : Fin 3,
        ∑ _j : Fin 3,
          h3SelectedSecondCoordinateDerivativePathMajorant
            ν A t hν U₀ hA hU₀ i s := by
          apply Finset.sum_le_sum
          intro k hk
          apply Finset.sum_le_sum
          intro j hj
          exact
            norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_le_majorant
              hν U₀ hA hU₀ hs.2 i j k x
    _ =
      9 *
        h3SelectedSecondCoordinateDerivativePathMajorant
          ν A t hν U₀ hA hU₀ i s := by
          simp only [Fin.sum_univ_three]
          ring

set_option maxHeartbeats 1000000 in
/-- The selected retarded Hessian is genuinely Bochner integrable on the open
Duhamel source-time interval.  We prove this structurally as a finite sum of
continuous-linear images of the already-integrable scalar mixed-coordinate
paths. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath_selectedRestart_integrableOn_Ioo
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    IntegrableOn
      (h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
        ν t W W i x)
      (Set.Ioo (0 : ℝ) t)
      volume := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  change
    Integrable
      (fun s : ℝ =>
        ∑ k : Fin 3,
          ∑ j : Fin 3,
            h3FourierSecondCoordinateLiftCLM j k
              (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
                ν t W W i j k x s))
      (volume.restrict (Set.Ioo (0 : ℝ) t))

  have hTerm
      (j k : Fin 3) :
      Integrable
        (fun s : ℝ =>
          h3FourierSecondCoordinateLiftCLM j k
            (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
              ν t W W i j k x s))
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    have hScalarInt :
        Integrable
          (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
            ν t W W i j k x)
          (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
      change
        IntegrableOn
          (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
            ν t W W i j k x)
          (Set.Ioo (0 : ℝ) t)
          volume
      exact
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_integrableOn_Ioo
          hν U₀ hA hU₀ ht htR i j k x

    exact
      (h3FourierSecondCoordinateLiftCLM j k).integrable_comp hScalarInt

  have hInner
      (k : Fin 3) :
      Integrable
        (fun s : ℝ =>
          ∑ j : Fin 3,
            h3FourierSecondCoordinateLiftCLM j k
              (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
                ν t W W i j k x s))
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    exact
      integrable_finsetSum
        (μ := volume.restrict (Set.Ioo (0 : ℝ) t))
        (f :=
          (fun j : Fin 3 =>
            fun s : ℝ =>
              h3FourierSecondCoordinateLiftCLM j k
                (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
                  ν t W W i j k x s) :
            Fin 3 →
              ℝ →
                (H3FourierPoint3 →L[ℝ]
                  (H3FourierPoint3 →L[ℝ] ℂ))))
        (Finset.univ : Finset (Fin 3))
        (by
          intro j hj
          exact hTerm j k)

  exact
    integrable_finsetSum
      (μ := volume.restrict (Set.Ioo (0 : ℝ) t))
      (f :=
        (fun k : Fin 3 =>
          fun s : ℝ =>
            ∑ j : Fin 3,
              h3FourierSecondCoordinateLiftCLM j k
                (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
                  ν t W W i j k x s) :
          Fin 3 →
            ℝ →
              (H3FourierPoint3 →L[ℝ]
                (H3FourierPoint3 →L[ℝ] ℂ))))
      (Finset.univ : Finset (Fin 3))
      (by
        intro k hk
        exact hInner k)

/-- Interval-integrable form of the selected retarded Hessian path. -/
theorem h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath_selectedRestart_intervalIntegrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    IntervalIntegrable
      (h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
        ν t W W i x)
      volume
      0
      t := by
  dsimp only
  rw [
    intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le,
    integrableOn_Ioc_iff_integrableOn_Ioo
  ]
  exact
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath_selectedRestart_integrableOn_Ioo
      hν U₀ hA hU₀ ht htR i x

/-- Two Hessian-valued continuous linear maps agree once their values agree on
the three canonical outer coordinate directions. -/
theorem h3SecondContinuousLinearMap_ext_axes
    {L M :
      H3FourierPoint3 →L[ℝ]
        (H3FourierPoint3 →L[ℝ] ℂ)}
    (hAxis :
      ∀ k : Fin 3,
        L (h3FourierAxisDirection (h3AxisOfFin3 k))
          =
        M (h3FourierAxisDirection (h3AxisOfFin3 k))) :
    L = M := by
  apply ContinuousLinearMap.ext
  intro x

  rw [h3FourierPoint_eq_sum_axis_components x]
  rw [map_sum, map_sum]
  simp only [map_smul]

  apply Finset.sum_congr rfl
  intro k hk
  rw [hAxis k]

/-- Integrating the selected retarded Hessian in source time gives exactly the
assembled selected second-Fréchet Duhamel field. -/
theorem intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath_eq_Duhamel_selectedRestart
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (∫ s in (0 : ℝ)..t,
      h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
        ν t W W i x s)
      =
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
      ν t W W i x := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let P : ℝ →
      (H3FourierPoint3 →L[ℝ]
        (H3FourierPoint3 →L[ℝ] ℂ)) :=
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
      ν t W W i x

  have hFullInt :
      Integrable
        P
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    dsimp only [P]
    exact
      h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath_selectedRestart_integrableOn_Ioo
        hν U₀ hA hU₀ ht htR i x

  apply h3SecondContinuousLinearMap_ext_axes
  intro k

  apply h3ContinuousLinearMap_ext_axes
  intro j

  rw [
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel_axis_axis
  ]

  rw [intervalIntegral.integral_of_le ht.le]
  rw [← restrict_Ioo_eq_restrict_Ioc]

  change
    ((∫ s : ℝ, P s
        ∂(volume.restrict (Set.Ioo (0 : ℝ) t)))
      (h3FourierAxisDirection (h3AxisOfFin3 k)))
      (h3FourierAxisDirection (h3AxisOfFin3 j))
      =
    _

  rw [
    ContinuousLinearMap.integral_apply
      hFullInt
      (h3FourierAxisDirection (h3AxisOfFin3 k))
  ]

  have hOuterInt :
      Integrable
        (fun s : ℝ =>
          P s (h3FourierAxisDirection (h3AxisOfFin3 k)))
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    exact
      (ContinuousLinearMap.apply
        ℝ
        (H3FourierPoint3 →L[ℝ] ℂ)
        (h3FourierAxisDirection (h3AxisOfFin3 k))).integrable_comp
        hFullInt

  rw [
    ContinuousLinearMap.integral_apply
      hOuterInt
      (h3FourierAxisDirection (h3AxisOfFin3 j))
  ]

  unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
  rw [intervalIntegral.integral_of_le ht.le]
  rw [← restrict_Ioo_eq_restrict_Ioc]

  apply integral_congr_ae
  filter_upwards with s

  dsimp only [P]
  exact
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath_axis_axis
      ν t W W i j k x s

end
end Euclidean
end Bridge
end PrimeTensor
