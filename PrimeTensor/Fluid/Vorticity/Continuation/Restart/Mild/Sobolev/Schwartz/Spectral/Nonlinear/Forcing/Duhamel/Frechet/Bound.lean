import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.C1

/-!
# Quantitative bound for the full nonlinear Duhamel Fréchet derivative

The preceding `C1` checkpoint proves that the nonlinear Duhamel reconstruction
is genuinely Fréchet differentiable in the full three-dimensional spatial
variable.  This file records the quantitative estimate carried by that proof.

The retarded full derivative has operator norm bounded by three copies of the
scalar first-derivative majorant.  Integrating this source-time estimate gives

    ‖Dₓ Duhamel(t)‖
      ≤ 3 * ∫₀ᵗ firstDerivativeMajorant(s) ds,

and the previously computed exact majorant integral turns this into an
explicit `sqrt t` estimate.

This is the form needed by the restart/continuation layer: it exposes the
quadratic dependence on the two path bounds and the positive-time
`sqrt t / sqrt ν` gain without hiding either in a qualitative regularity
statement.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingDuhamelFrechetBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The full Duhamel Fréchet derivative is bounded by the time integral of
three copies of the scalar coordinate-derivative majorant. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel_le_integral
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
    ‖h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t U V i x‖
      ≤
    ∫ s in (0 : ℝ)..t,
      3 * h3NonlinearForcingHeatFirstDerivativePathMajorant
        ν t MU MV s := by
  rw [
    ←
      intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_eq_Duhamel
        hν ht hMU hMV U V hUcont hVcont hU hV i x
  ]
  rw [intervalIntegral.integral_of_le ht]
  rw [← restrict_Ioo_eq_restrict_Ioc]

  have hBoundInt :
      Integrable
        (fun s : ℝ =>
          3 * h3NonlinearForcingHeatFirstDerivativePathMajorant
            ν t MU MV s)
        (volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    change
      IntegrableOn
        (fun s : ℝ =>
          3 * h3NonlinearForcingHeatFirstDerivativePathMajorant
            ν t MU MV s)
        (Set.Ioo (0 : ℝ) t)
        volume
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    exact
      (h3NonlinearForcingHeatFirstDerivativePathMajorant_intervalIntegrable
        (MU := MU) (MV := MV) hν ht).const_mul (3 : ℝ)

  have hBoundAE :
      ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) t)),
        ‖h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath
            ν t U V i x s‖
          ≤
        3 * h3NonlinearForcingHeatFirstDerivativePathMajorant
          ν t MU MV s := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    exact
      norm_h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeRetardedPath_le
        hν hMU hMV U V hs (hU s hs) (hV s hs) i x

  have hSet :=
    MeasureTheory.norm_integral_le_of_norm_le hBoundInt hBoundAE
  simpa only [
    intervalIntegral.integral_of_le ht,
    ← restrict_Ioo_eq_restrict_Ioc
  ] using hSet

/-- Closed-form version of the full Duhamel Fréchet derivative estimate.

The bound is quadratic in the two uniform path bounds and gains one
`sqrt t / sqrt ν` factor from the heat kernel. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel_le
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
    ‖h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t U V i x‖
      ≤
    3 *
      ((2 * Real.pi) *
        (2 * (Real.sqrt (ν / 3))⁻¹ * Real.sqrt t *
          h3NonlinearForcingL1Coefficient * MU * MV)) := by
  calc
    ‖h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel
        ν t U V i x‖
        ≤
      ∫ s in (0 : ℝ)..t,
        3 * h3NonlinearForcingHeatFirstDerivativePathMajorant
          ν t MU MV s :=
      norm_h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel_le_integral
        hν ht hMU hMV U V hUcont hVcont hU hV i x
    _ =
      3 *
        (∫ s in (0 : ℝ)..t,
          h3NonlinearForcingHeatFirstDerivativePathMajorant
            ν t MU MV s) := by
      rw [intervalIntegral.integral_const_mul]
    _ =
      3 *
        ((2 * Real.pi) *
          (2 * (Real.sqrt (ν / 3))⁻¹ * Real.sqrt t *
            h3NonlinearForcingL1Coefficient * MU * MV)) := by
      rw [
        h3NonlinearForcingHeatFirstDerivativePathMajorant_integral
          (MU := MU) (MV := MV) hν ht
      ]

/-- The same explicit estimate stated directly for Mathlib's `fderiv` of the
nonlinear Duhamel reconstruction. -/
theorem norm_fderiv_h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_le
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
    ‖fderiv ℝ
        (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
          ν t U V i)
        x‖
      ≤
    3 *
      ((2 * Real.pi) *
        (2 * (Real.sqrt (ν / 3))⁻¹ * Real.sqrt t *
          h3NonlinearForcingL1Coefficient * MU * MV)) := by
  rw [
    (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel_hasFDerivAt
      hν ht hMU hMV U V hUcont hVcont hU hV i x).fderiv
  ]
  exact
    norm_h3RawFinLerayOuterProductDivergenceHeatFrechetDerivativeDuhamel_le
      hν ht hMU hMV U V hUcont hVcont hU hV i x

end
end Euclidean
end Bridge
end PrimeTensor
