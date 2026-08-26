import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Spatial.Derivative

/-!
# Spatial continuity of the nonlinear Duhamel first derivative

The previous checkpoint proves that one coordinate derivative passes through
the full retarded Duhamel time integral.  To promote that coordinatewise
identity to genuine spatial `C¹` regularity, the remaining analytic input is
continuity of the integrated derivative field in the spatial variable.

At each positive heat lag the derivative representative is an inverse Fourier
transform of an `L¹` multiplier, hence is continuous in space.  Its norm is
bounded uniformly in the spatial point by the already-established
`(t - s)^(-1/2)` time majorant.  That majorant is interval integrable, so
parametric dominated convergence gives continuity after integrating in source
time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingDuhamelDerivativeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At every strictly positive heat lag, the classical first coordinate
spatial derivative representative is continuous in the spatial variable. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_continuous_space
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3) :
    Continuous
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ U V i j) := by
  have hInnerNegContinuous :
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          ((-(innerₗ H3FourierPoint3)) p.1) p.2) := by
    change Continuous
      (fun p : H3FourierPoint3 × H3FourierPoint3 =>
        -inner ℝ p.1 p.2)
    exact
      (continuous_inner (𝕜 := ℝ) (E := H3FourierPoint3)).neg

  unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
  change Continuous
    (VectorFourier.fourierIntegral
      Real.fourierChar
      (volume : Measure H3FourierPoint3)
      (-(innerₗ H3FourierPoint3))
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol j ξ *
          h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ U V i ξ))
  exact
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar
      hInnerNegContinuous
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_derivative_integrable
        hν hτ U V i j)

/-- For continuous uniformly bounded spectral paths, the integrated first
coordinate derivative of the nonlinear Duhamel reconstruction is continuous
in space.  The endpoint `s = t` is discarded only as a Lebesgue-null point;
the majorant itself is integrable all the way to the endpoint. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel_continuous
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
    (i j : Fin 3) :
    Continuous
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
        ν t U V i j) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel

  apply intervalIntegral.continuous_of_dominated_interval
    (F := fun x : H3FourierPoint3 =>
      fun s : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν t U V i j x s)
    (bound := h3NonlinearForcingHeatFirstDerivativePathMajorant
      ν t MU MV)

  · intro x
    exact
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_intervalIntegrable_of_continuous
        hν ht hMU hMV U V hUcont hVcont hU hV i j x).def'.aestronglyMeasurable

  · intro x
    filter_upwards [(volume : Measure ℝ).ae_ne t] with s hst hs
    have hsIoc : s ∈ Set.Ioc (0 : ℝ) t := by
      simpa only [uIoc_of_le ht] using hs
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) t := by
      exact ⟨hsIoc.1, lt_of_le_of_ne hsIoc.2 hst⟩
    exact
      norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_le_pathMajorant
        hν hMU hMV U V hsIoo (hU s hsIoo) (hV s hsIoo) i j x

  · exact
      h3NonlinearForcingHeatFirstDerivativePathMajorant_intervalIntegrable
        (MU := MU) (MV := MV) hν ht

  · filter_upwards [(volume : Measure ℝ).ae_ne t] with s hst hs
    have hsIoc : s ∈ Set.Ioc (0 : ℝ) t := by
      simpa only [uIoc_of_le ht] using hs
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) t := by
      exact ⟨hsIoc.1, lt_of_le_of_ne hsIoc.2 hst⟩
    unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
    exact
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_continuous_space
        hν (sub_pos.mpr hsIoo.2) (U s) (V s) i j

end
end Euclidean
end Bridge
end PrimeTensor
