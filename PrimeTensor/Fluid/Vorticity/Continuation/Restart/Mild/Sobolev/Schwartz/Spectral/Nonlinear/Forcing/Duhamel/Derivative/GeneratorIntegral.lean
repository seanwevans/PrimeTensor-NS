import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.GeneratorIntegrability
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.SelectedSecondFrechetTimeIntegrability

/-!
# Selected Duhamel terminal-time generator integral

The terminal-time generator path is now genuinely source-time integrable on
`0..t`.  Its strict-slice identity is viscosity times the trace of the
retarded spatial Hessian.

This file integrates that identity and identifies the result with viscosity
times the trace of the already-constructed second-Fréchet Duhamel field:

    ∫₀ᵗ ∂ₜ H_{t-s} N(W(s)) ds = ν Δ D(t).

This is the old-history contribution in the diagonal Duhamel time derivative.
After this checkpoint, the only remaining contribution is the fresh endpoint
forcing term.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace BigOperators

noncomputable section

noncomputable local instance axisFintypeH3DuhamelTimeGeneratorIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Integrating the selected terminal-time generator gives viscosity times the
trace of the complete selected Duhamel Hessian. -/
theorem intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath_eq_viscosity_mul_DuhamelHessianTrace_selectedRestart
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
      h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
        ν t W W i x s)
      =
    (ν : ℂ) *
      (∑ j : Fin 3,
        h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel
            ν t W W i x
            (h3FourierAxisDirection (h3AxisOfFin3 j))
            (h3FourierAxisDirection (h3AxisOfFin3 j))) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let μ : Measure ℝ :=
    volume.restrict (Set.Ioo (0 : ℝ) t)

  let f : Fin 3 → ℝ → ℂ :=
    fun j s =>
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
        ν t W W i j j x s

  have hG :
      Integrable
        (h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
          ν t W W i x)
        μ := by
    dsimp only [μ]
    change
      IntegrableOn
        (h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
          ν t W W i x)
        (Set.Ioo (0 : ℝ) t)
        volume
    exact
      h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath_selectedRestart_integrableOn_Ioo
        hν U₀ hA hU₀ ht htR i x

  have hf (j : Fin 3) :
      Integrable (f j) μ := by
    dsimp only [f, μ]
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
        (fun s : ℝ => ∑ j : Fin 3, f j s)
        μ := by
    exact
      integrable_finsetSum
        (μ := μ)
        (f := f)
        (Finset.univ : Finset (Fin 3))
        (by
          intro j hj
          exact hf j)

  have hEqAE :
      h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
          ν t W W i x
        =ᵐ[μ]
      (fun s : ℝ => (ν : ℂ) * (∑ j : Fin 3, f j s)) := by
    dsimp only [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    dsimp only [f]
    exact
      h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath_eq_viscosity_mul_secondCoordinateTrace
        hν hs.2 W W i x

  have hIntegralEq :
      (∫ s : ℝ,
        h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
          ν t W W i x s ∂μ)
        =
      (ν : ℂ) *
        (∑ j : Fin 3, ∫ s : ℝ, f j s ∂μ) := by
    calc
      (∫ s : ℝ,
        h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
          ν t W W i x s ∂μ)
          =
        ∫ s : ℝ, (ν : ℂ) * (∑ j : Fin 3, f j s) ∂μ := by
          exact integral_congr_ae hEqAE
      _ =
        (ν : ℂ) *
          (∫ s : ℝ, ∑ j : Fin 3, f j s ∂μ) := by
          rw [integral_const_mul]
      _ =
        (ν : ℂ) *
          (∑ j : Fin 3, ∫ s : ℝ, f j s ∂μ) := by
          congr 1
          exact
            integral_finsetSum
              (μ := μ)
              (s := (Finset.univ : Finset (Fin 3)))
              (fun j hj => hf j)

  have hInterval (j : Fin 3) :
      (∫ s : ℝ, f j s ∂μ)
        =
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
        ν t W W i j j x := by
    unfold h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateDuhamel
    rw [intervalIntegral.integral_of_le ht.le]
    rw [← restrict_Ioo_eq_restrict_Ioc]

  rw [intervalIntegral.integral_of_le ht.le]
  rw [← restrict_Ioo_eq_restrict_Ioc]
  change
    (∫ s : ℝ,
      h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRetardedPath
        ν t W W i x s ∂μ)
      = _

  rw [hIntegralEq]

  congr 1

  apply Finset.sum_congr rfl
  intro j hj

  rw [hInterval j]
  symm
  exact
    h3RawFinLerayOuterProductDivergenceHeatSecondFrechetDerivativeDuhamel_axis_axis
      ν t W W i j j x

end

end Euclidean
end Bridge
end PrimeTensor
