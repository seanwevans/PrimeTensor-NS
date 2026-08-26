import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.C0.Time.Integrability
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Spatial differentiation of the classical nonlinear Duhamel integral

The preceding modules established all three ingredients needed for the
classical differentiation-under-the-time-integral step:

* the zeroth-order retarded reconstruction is Bochner integrable in source
  time at every spatial point;
* its first coordinate derivative is Bochner integrable in source time, with
  the explicit `(t - s)^(-1/2)` majorant; and
* at every positive heat lag, the Fourier-multiplied representative is the
  genuine spatial coordinate derivative of the classical `C³`
  reconstruction.

This file assembles those facts with Mathlib's dominated parametric-integral
theorem.  For continuous uniformly bounded spectral paths, one Euclidean
coordinate derivative passes through the full retarded Duhamel time integral.
In particular, the same statement is available for every near-endpoint tail
by restricting the time interval.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingDuhamelSpatialDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The fixed-lag coordinate derivative identity at an arbitrary point of the
coordinate line.  The earlier theorem was normalized at line parameter zero;
this is its translated form. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Representative_hasDerivAt_coordinate_at
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3)
    (r : ℝ) :
    HasDerivAt
      (fun q : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
          ν τ U V i
          (x + q • h3FourierAxisDirection (h3AxisOfFin3 j)))
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ U V i j
        (x + r • h3FourierAxisDirection (h3AxisOfFin3 j)))
      r := by
  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 j)

  have h0 :
      HasDerivAt
        (fun q : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν τ U V i ((x + r • e) + q • e))
        (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν τ U V i j (x + r • e))
        0 := by
    simpa [e] using
      (h3RawFinLerayOuterProductDivergenceHeatC3Representative_hasDerivAt_coordinate
        hν hτ U V i j (x + r • e))

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
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
          ν τ U V i (x + q • e))
        =ᶠ[𝓝 r]
      ((fun q : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν τ U V i ((x + r • e) + q • e)) ∘
        fun q : ℝ => q - r) := by
    filter_upwards with q
    simp only [Function.comp_apply]
    rw [hPoint q]

  have hTransport := hComp.congr_of_eventuallyEq hFunEq

  have hDerivEq :
      (1 : ℝ) •
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
            ν τ U V i j (x + r • e)
        =
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ U V i j (x + r • e) :=
    one_smul ℝ _

  have hFinal := hTransport.congr_deriv hDerivEq
  simpa only [e] using hFinal

/-- Classical pointwise nonlinear Duhamel reconstruction. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) : ℂ :=
  ∫ s in (0 : ℝ)..t,
    h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
      ν t U V i x s

/-- Time integral of the pointwise first coordinate derivative of the
retarded nonlinear reconstruction. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
    (ν t : ℝ)
    (U V : ℝ → H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3) : ℂ :=
  ∫ s in (0 : ℝ)..t,
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
      ν t U V i j x s

/-- Spatial differentiation passes through the full retarded Duhamel time
integral.  The singular derivative majorant is integrable up to the endpoint,
so no endpoint truncation is required. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_hasDerivAt_coordinate
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
    HasDerivAt
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t U V i
          (x + r • h3FourierAxisDirection (h3AxisOfFin3 j)))
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
        ν t U V i j x)
      0 := by
  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 j)

  let F : ℝ → ℝ → ℂ :=
    fun r s =>
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t U V i (x + r • e) s

  let F' : ℝ → ℝ → ℂ :=
    fun r s =>
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν t U V i j (x + r • e) s

  let bound : ℝ → ℝ :=
    h3NonlinearForcingHeatFirstDerivativePathMajorant ν t MU MV

  have hFInt :
      ∀ r : ℝ,
        Integrable
          (F r)
          (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    intro r
    change
      IntegrableOn
        (h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν t U V i (x + r • e))
        (Set.Ioo (0 : ℝ) t)
        volume
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_intervalIntegrable_of_continuous
        hν ht hMU hMV U V hUcont hVcont hU hV i (x + r • e)

  have hFMeas :
      ∀ᶠ r : ℝ in 𝓝 0,
        AEStronglyMeasurable
          (F r)
          (volume.restrict (Set.Ioo (0 : ℝ) t)) :=
    Filter.Eventually.of_forall fun r => (hFInt r).aestronglyMeasurable

  have hF0Int :
      Integrable
        (F 0)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) :=
    hFInt 0

  have hF'0Int :
      Integrable
        (F' 0)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    change
      IntegrableOn
        (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν t U V i j (x + 0 • e))
        (Set.Ioo (0 : ℝ) t)
        volume
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    simpa using
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_intervalIntegrable_of_continuous
        hν ht hMU hMV U V hUcont hVcont hU hV i j x)

  have hF'0Meas :
      AEStronglyMeasurable
        (F' 0)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) :=
    hF'0Int.aestronglyMeasurable

  have hBoundInt :
      Integrable
        bound
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    change
      IntegrableOn
        (h3NonlinearForcingHeatFirstDerivativePathMajorant ν t MU MV)
        (Set.Ioo (0 : ℝ) t)
        volume
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    exact
      h3NonlinearForcingHeatFirstDerivativePathMajorant_intervalIntegrable
        (MU := MU) (MV := MV) hν ht

  have hBound :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) t)),
        ∀ r ∈ (Set.univ : Set ℝ),
          ‖F' r s‖ ≤ bound s := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    intro r hr
    dsimp [F', bound]
    exact
      norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_le_pathMajorant
        hν hMU hMV U V hs (hU s hs) (hV s hs) i j (x + r • e)

  have hDiff :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) t)),
        ∀ r ∈ (Set.univ : Set ℝ),
          HasDerivAt (F · s) (F' r s) r := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    intro r hr
    dsimp [F, F']
    unfold h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
    unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
    simpa [e] using
      (h3RawFinLerayOuterProductDivergenceHeatC3Representative_hasDerivAt_coordinate_at
        hν (sub_pos.mpr hs.2) (U s) (V s) i j x r)

  have hIntegral :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := (Set.univ : Set ℝ))
      (F := F)
      (F' := F')
      (x₀ := (0 : ℝ))
      (bound := bound)
      (μ := volume.restrict (Set.Ioo (0 : ℝ) t))
      Filter.univ_mem
      hFMeas
      hF0Int
      hF'0Meas
      hBound
      hBoundInt
      hDiff).2

  have hValueIntegral (r : ℝ) :
      (∫ s : ℝ,
          F r s
          ∂(volume.restrict (Set.Ioo (0 : ℝ) t)))
        =
      ∫ s in (0 : ℝ)..t,
        h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν t U V i (x + r • e) s := by
    rw [intervalIntegral.integral_of_le ht]
    rw [← restrict_Ioo_eq_restrict_Ioc]

  have hDerivativeIntegral :
      (∫ s : ℝ,
          F' 0 s
          ∂(volume.restrict (Set.Ioo (0 : ℝ) t)))
        =
      ∫ s in (0 : ℝ)..t,
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν t U V i j x s := by
    rw [intervalIntegral.integral_of_le ht]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    simp [F', e]

  change
    HasDerivAt
      (fun r : ℝ =>
        ∫ s in (0 : ℝ)..t,
          h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
            ν t U V i (x + r • e) s)
      (∫ s in (0 : ℝ)..t,
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν t U V i j x s)
      0

  have hValueFunction :
      (fun r : ℝ =>
        ∫ s in (0 : ℝ)..t,
          h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
            ν t U V i (x + r • e) s)
        =
      (fun r : ℝ =>
        ∫ s : ℝ,
          F r s
          ∂(volume.restrict (Set.Ioo (0 : ℝ) t))) := by
    funext r
    exact (hValueIntegral r).symm

  rw [hValueFunction]
  rw [← hDerivativeIntegral]
  exact hIntegral

/-- Equality form of the differentiation-under-the-time-integral theorem. -/
theorem deriv_h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_coordinate
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
    deriv
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t U V i
          (x + r • h3FourierAxisDirection (h3AxisOfFin3 j)))
      0
      =
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeDuhamel
      ν t U V i j x := by
  exact
    (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_hasDerivAt_coordinate
      hν ht hMU hMV U V hUcont hVcont hU hV i j x).deriv

end

end Euclidean
end Bridge
end PrimeTensor
