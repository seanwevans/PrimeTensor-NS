import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Time.LaplacianRepresentative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.SelectedSecondFrechetTimeIntegrability

/-!
# Selected Duhamel terminal-time generator integrability

The fixed-lag nonlinear heat time generator is now identified pointwise with
viscosity times the trace of the genuine spatial Hessian.

Along the selected retarded source path, this becomes

    ∂ₜ H_{t-s} F(W(s),W(s))
      = ν * Σⱼ ∂ⱼ∂ⱼ H_{t-s} F(W(s),W(s))

for every strict source slice `s < t`.

The endpoint bootstrap already proves each mixed second-coordinate retarded
path integrable on `(0,t)`.  Hence the terminal-time generator itself is
integrable on `(0,t)` by a finite sum and multiplication by the constant
viscosity.

This is the exact source-time integrability input needed for the diagonal
Duhamel Leibniz derivative.  No new endpoint estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace BigOperators

noncomputable section

noncomputable local instance axisFintypeH3DuhamelTimeGeneratorIntegrability
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Terminal-time heat generator evaluated along an arbitrary retarded
source-time path. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (s : ℝ) : ℂ :=
  h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative
    ν (t - s) (U s) (V s) i x

/-- On every strict retarded slice, the terminal-time generator is viscosity
times the sum of the three diagonal mixed-second-coordinate paths. -/
theorem h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath_eq_viscosity_mul_secondCoordinateTrace
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
        ν t U V i x s
      =
    (ν : ℂ) *
      (∑ j : Fin 3,
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν t U V i j j x s) := by
  have hLag : 0 < t - s :=
    sub_pos.mpr hs

  have hGenerator :=
    congrFun
      (h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative_eq_viscosity_smul_laplacianRepresentative
        ν (t - s) (U s) (V s) i)
      x

  simp only [Pi.smul_apply, smul_eq_mul] at hGenerator

  have hLaplacian :=
    congrFun
      (h3RawFinLerayOuterProductDivergenceHeatLaplacianRepresentative_eq_sum_secondCoordinate
        hν hLag (U s) (V s) i)
      x

  unfold
    h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath

  rw [hGenerator, hLaplacian]

  rfl

/-- Equivalent strict-slice form using the actual retarded Hessian trace. -/
theorem h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath_eq_viscosity_mul_hessianTrace
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
        ν t U V i x s
      =
    (ν : ℂ) *
      (∑ j : Fin 3,
        h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath
            ν t U V i x s
            (h3FourierAxisDirection (h3AxisOfFin3 j))
            (h3FourierAxisDirection (h3AxisOfFin3 j))) := by
  rw [
    h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath_eq_viscosity_mul_secondCoordinateTrace
      hν hs U V i x
  ]

  congr 1

  apply Finset.sum_congr rfl
  intro j hj

  symm
  exact
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeRetardedPath_axis_axis
      ν t U V i j j x s

/-- Along the canonical selected restart path, the terminal-time generator is
genuinely integrable on the complete open Duhamel source interval. -/
theorem h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath_selectedRestart_integrableOn_Ioo
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
      (h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
        ν t W W i x)
      (Set.Ioo (0 : ℝ) t)
      volume := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let T : ℝ → ℂ :=
    fun s =>
      ∑ j : Fin 3,
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν t W W i j j x s

  have hTerm
      (j : Fin 3) :
      Integrable
        (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν t W W i j j x)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    change
      IntegrableOn
        (h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν t W W i j j x)
        (Set.Ioo (0 : ℝ) t)
        volume
    exact
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_integrableOn_Ioo
        hν U₀ hA hU₀ ht htR i j j x

  have hTrace :
      Integrable
        T
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    dsimp only [T]
    exact
      integrable_finsetSum
        (μ := volume.restrict (Set.Ioo (0 : ℝ) t))
        (f :=
          fun j : Fin 3 =>
            h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
              ν t W W i j j x)
        (Finset.univ : Finset (Fin 3))
        (by
          intro j hj
          exact hTerm j)

  have hScaled :
      Integrable
        (fun s : ℝ => (ν : ℂ) * T s)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) :=
    hTrace.const_mul (ν : ℂ)

  apply Integrable.congr hScaled

  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs

  dsimp only [T]

  exact
    (h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath_eq_viscosity_mul_secondCoordinateTrace
      hν hs.2 W W i x).symm

/-- Interval-integrable form of the selected terminal-time generator path. -/
theorem h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath_selectedRestart_intervalIntegrable
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
      (h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
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
    h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath_selectedRestart_integrableOn_Ioo
      hν U₀ hA hU₀ ht htR i x

end

end Euclidean
end Bridge
end PrimeTensor
