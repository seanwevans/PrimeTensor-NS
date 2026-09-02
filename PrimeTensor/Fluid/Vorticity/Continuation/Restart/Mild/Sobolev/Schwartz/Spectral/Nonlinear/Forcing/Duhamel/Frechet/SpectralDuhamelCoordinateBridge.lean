import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.SpectralCoordinateBridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Duhamel.Path
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Spectral H³ Duhamel coordinate derivative as a retarded time integral

`SpectralCoordinateBridge` identifies one positive-lag spectral heat--Leray
kernel after bounded coordinate derivative evaluation with the explicit
classical first-derivative representative.

The Duhamel state itself is the H³-valued Bochner interval integral

    ∫₀ᵗ K(t,s) ds.

This file commutes the bounded coordinate derivative evaluation functional
through that Bochner integral.  For continuous uniformly bounded input paths,

    D_a C¹(Duhamel(t))(x)
      =
    ∫₀ᵗ D_a K(t,s,x) ds.

The endpoint `s = t` is irrelevant: the spectral Duhamel integrand is defined
to be zero there, while the explicit derivative path has its zero-lag value.
`intervalIntegral.integral_congr_uIoo` compares the two only on the open
interval, where the lag is strictly positive and the fixed-lag bridge applies.

This is the exact representation theorem needed to turn the fresh spectral
remainder in the first-Fréchet quotient split into the literal retarded
derivative integral whose endpoint limit is already closed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3FrechetSpectralDuhamelCoordinateBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- For continuous uniformly bounded spectral paths, coordinate derivative
evaluation of the canonical H³ Duhamel `C¹` representative is exactly the
source-time integral of the explicit retarded first-derivative path. -/
theorem h3SpectralFinHeatLerayDuhamel_C1_fderiv_coordinate_eq_intervalIntegral
    {ν t MU MV : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t)
    (hMU : 0 ≤ MU)
    (hMV : 0 ≤ MV)
    (U V : ℝ → H3SpectralFinVectorState)
    (hUcont : Continuous U)
    (hVcont : Continuous V)
    (hU : ∀ s : ℝ, ‖U s‖ ≤ MU)
    (hV : ∀ s : ℝ, ‖V s‖ ≤ MV)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    (fderiv ℝ
        (h3SpectralScalarC1Representative
          (h3SpectralFinHeatLerayDuhamel
            ν t hν U V i))
        x)
        (h3FourierAxisDirection (h3AxisOfFin3 a))
      =
    ∫ s in (0 : ℝ)..t,
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν t U V i a x s := by
  let E : H3SpectralScalarState →L[ℂ] ℂ :=
    h3SpectralScalarC1CoordinateDerivativeEvaluationCLM a x

  let P : H3SpectralFinVectorState →L[ℂ] H3SpectralScalarState :=
    ContinuousLinearMap.proj (R := ℂ) i

  let EP : H3SpectralFinVectorState →L[ℂ] ℂ :=
    E.comp P

  have hUint :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖U s‖ ≤ MU := by
    intro s hs
    exact hU s

  have hVint :
      ∀ s ∈ Set.Ioc (0 : ℝ) t,
        ‖V s‖ ≤ MV := by
    intro s hs
    exact hV s

  have hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand
          ν t hν U V)
        volume
        0
        t :=
    h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
      hν ht hMU hMV U V
      hUcont hVcont hUint hVint

  have hComm :
      EP
          (∫ s in (0 : ℝ)..t,
            h3SpectralFinHeatLerayDuhamelIntegrand
              ν t hν U V s)
        =
      ∫ s in (0 : ℝ)..t,
        EP
          (h3SpectralFinHeatLerayDuhamelIntegrand
            ν t hν U V s) := by
    symm
    exact EP.intervalIntegral_comp_comm hInt

  have hKernel :
      (∫ s in (0 : ℝ)..t,
        EP
          (h3SpectralFinHeatLerayDuhamelIntegrand
            ν t hν U V s))
        =
      ∫ s in (0 : ℝ)..t,
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν t U V i a x s := by
    apply intervalIntegral.integral_congr_uIoo
    intro s hs

    have hsIoo :
        s ∈ Set.Ioo (0 : ℝ) t := by
      change
        min (0 : ℝ) t < s ∧ s < max (0 : ℝ) t
        at hs
      rw [min_eq_left ht, max_eq_right ht] at hs
      exact hs

    have hlag :
        0 < t - s :=
      sub_pos.mpr hsIoo.2

    simp only [
      h3SpectralFinHeatLerayDuhamelIntegrand,
      dif_pos hlag
    ]

    change
      h3SpectralScalarC1CoordinateDerivativeEvaluationCLM a x
          (h3SpectralFinHeatLerayVelocityApply
            ν (t - s) hν hlag (U s) (V s) i)
        =
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν t U V i a x s

    unfold
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath

    exact
      h3SpectralScalarC1CoordinateDerivativeEvaluationCLM_heatLerayVelocityApply
        hν hlag (U s) (V s) i a x

  rw [
    ← h3SpectralScalarC1CoordinateDerivativeEvaluationCLM_apply
  ]

  change
    E
        (h3SpectralFinHeatLerayDuhamel
          ν t hν U V i)
      =
    ∫ s in (0 : ℝ)..t,
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν t U V i a x s

  unfold h3SpectralFinHeatLerayDuhamel

  change
    EP
        (∫ s in (0 : ℝ)..t,
          h3SpectralFinHeatLerayDuhamelIntegrand
            ν t hν U V s)
      =
    ∫ s in (0 : ℝ)..t,
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν t U V i a x s

  exact hComm.trans hKernel

end

end Euclidean
end Bridge
end PrimeTensor
