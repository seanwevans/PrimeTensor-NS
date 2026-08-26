import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Time.Integrability
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Full Fréchet C¹ regularity of the nonlinear Duhamel reconstruction

The preceding checkpoints assembled the three coordinate derivatives into the
true fixed-lag Fréchet derivative, proved source-time integrability of the full
retarded operator path, identified its time integral with the assembled
Duhamel derivative, and proved continuity of that assembled derivative field.

This file performs the final differentiation-under-the-integral step in the
full spatial variable.  The operator-valued derivative is dominated on the
open source-time interval by three copies of the already-integrable scalar
first-derivative majorant.  Mathlib's Fréchet parametric-integral theorem then
shows that the nonlinear Duhamel reconstruction has the assembled operator as
its genuine Fréchet derivative at every spatial point.  Continuity of that
field immediately upgrades the reconstruction to `ContDiff ℝ 1`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingDuhamelFrechetC1
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The full spatial Fréchet derivative passes through the nonlinear retarded
Duhamel time integral. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_hasFDerivAt
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
    HasFDerivAt
      (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t U V i)
      (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t U V i x)
      x := by
  let F : H3FourierPoint3 → ℝ → ℂ :=
    fun y s =>
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        ν t U V i y s

  let F' : H3FourierPoint3 → ℝ → (H3FourierPoint3 →L[ℝ] ℂ) :=
    fun y s =>
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
        ν t U V i y s

  let bound : ℝ → ℝ :=
    fun s =>
      3 * h3NonlinearForcingHeatFirstDerivativePathMajorant
        ν t MU MV s

  have hFInt :
      ∀ y : H3FourierPoint3,
        Integrable
          (F y)
          (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    intro y
    change
      IntegrableOn
        (h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν t U V i y)
        (Set.Ioo (0 : ℝ) t)
        volume
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_intervalIntegrable_of_continuous
        hν ht hMU hMV U V hUcont hVcont hU hV i y

  have hFMeas :
      ∀ᶠ y : H3FourierPoint3 in 𝓝 x,
        AEStronglyMeasurable
          (F y)
          (volume.restrict (Set.Ioo (0 : ℝ) t)) :=
    Filter.Eventually.of_forall fun y => (hFInt y).aestronglyMeasurable

  have hFxInt :
      Integrable
        (F x)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) :=
    hFInt x

  have hF'xInt :
      Integrable
        (F' x)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    change
      IntegrableOn
        (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
          ν t U V i x)
        (Set.Ioo (0 : ℝ) t)
        volume
    exact
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_integrableOn_Ioo_of_continuous
        hν ht hMU hMV U V hUcont hVcont hU hV i x

  have hF'xMeas :
      AEStronglyMeasurable
        (F' x)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) :=
    hF'xInt.aestronglyMeasurable

  have hMajorantInt :
      Integrable
        (h3NonlinearForcingHeatFirstDerivativePathMajorant ν t MU MV)
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

  have hBoundInt :
      Integrable
        bound
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    simpa [bound] using hMajorantInt.const_mul (3 : ℝ)

  have hBound :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) t)),
        ∀ y ∈ (Set.univ : Set H3FourierPoint3),
          ‖F' y s‖ ≤ bound s := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    intro y hy
    dsimp [F', bound]
    exact
      norm_h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_le
        hν hMU hMV U V hs (hU s hs) (hV s hs) i y

  have hDiff :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) t)),
        ∀ y ∈ (Set.univ : Set H3FourierPoint3),
          HasFDerivAt (F · s) (F' y s) y := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    intro y hy
    dsimp [F, F']
    unfold h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
    unfold h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
    unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
    simpa only [
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRepresentative
    ] using
      h3RawFinLerayOuterProductDivergenceHeatC3Representative_hasFDerivAt
        hν (sub_pos.mpr hs.2) (U s) (V s) i y

  have hIntegral :=
    (hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := (Set.univ : Set H3FourierPoint3))
      (F := F)
      (F' := F')
      (x₀ := x)
      (bound := bound)
      (μ := volume.restrict (Set.Ioo (0 : ℝ) t))
      Filter.univ_mem
      hFMeas
      hFxInt
      hF'xMeas
      hBound
      hBoundInt
      hDiff)

  have hValueIntegral (y : H3FourierPoint3) :
      (∫ s : ℝ,
          F y s
          ∂(volume.restrict (Set.Ioo (0 : ℝ) t)))
        =
      ∫ s in (0 : ℝ)..t,
        h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
          ν t U V i y s := by
    rw [intervalIntegral.integral_of_le ht]
    rw [← restrict_Ioo_eq_restrict_Ioc]

  have hDerivativeIntegral :
      (∫ s : ℝ,
          F' x s
          ∂(volume.restrict (Set.Ioo (0 : ℝ) t)))
        =
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t U V i x := by
    calc
      (∫ s : ℝ,
          F' x s
          ∂(volume.restrict (Set.Ioo (0 : ℝ) t)))
          =
        ∫ s in (0 : ℝ)..t,
          h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
            ν t U V i x s := by
              rw [intervalIntegral.integral_of_le ht]
              rw [← restrict_Ioo_eq_restrict_Ioc]
      _ =
        h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
          ν t U V i x :=
            intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_eq_Duhamel
              hν ht hMU hMV U V hUcont hVcont hU hV i x

  change
    HasFDerivAt
      (fun y : H3FourierPoint3 =>
        ∫ s in (0 : ℝ)..t,
          h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
            ν t U V i y s)
      (h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t U V i x)
      x

  have hValueFunction :
      (fun y : H3FourierPoint3 =>
        ∫ s in (0 : ℝ)..t,
          h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
            ν t U V i y s)
        =
      (fun y : H3FourierPoint3 =>
        ∫ s : ℝ,
          F y s
          ∂(volume.restrict (Set.Ioo (0 : ℝ) t))) := by
    funext y
    exact (hValueIntegral y).symm

  rw [hValueFunction]
  rw [← hDerivativeIntegral]
  exact hIntegral

/-- The full nonlinear Duhamel reconstruction is continuously Fréchet
differentiable in the spatial variable. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_contDiff_one
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
    ContDiff ℝ 1
      (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t U V i) := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine
    ⟨h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t U V i, ?_, ?_⟩
  · exact
      h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel_continuous
        hν ht hMU hMV U V hUcont hVcont hU hV i
  · intro x
    exact
      h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_hasFDerivAt
        hν ht hMU hMV U V hUcont hVcont hU hV i x

end
end Euclidean
end Bridge
end PrimeTensor
