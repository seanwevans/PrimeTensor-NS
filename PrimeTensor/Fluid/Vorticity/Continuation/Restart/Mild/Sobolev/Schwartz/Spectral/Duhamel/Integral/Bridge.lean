import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Physical.Control
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability.Closure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exact physical Bochner bridge for the heat--Leray Duhamel term

The previous checkpoint proves pointwise physical closure of the strict
retarded integrand and a physical norm bound for the complete Duhamel term.
To transport the nonlinear realization through time integration we first need
an exact representation theorem: decoding must commute with the Bochner
interval integral.

This file packages the finite-vector complex spectral decoder as a contractive
complex continuous linear map.  Mathlib's
`ContinuousLinearMap.intervalIntegral_comp_comm` then gives the desired
identity directly:

    decode (∫ s, K(s)) = ∫ s, decode (K(s)).

No measurable-selection or closure-under-integral claim is made yet.  This is
the exact linear bridge on which that next step can safely be built.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzDuhamelIntegralBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Complex linearity of exact deweighting and decoding -/

@[simp]
theorem h3SpectralScalarRawFourierL2_smul_complex
    (c : ℂ)
    (G : H3SpectralScalarState) :
    h3SpectralScalarRawFourierL2 (c • G)
      = c • h3SpectralScalarRawFourierL2 G := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarRawFourierL2_ae (c • G),
    h3SpectralScalarRawFourierL2_ae G,
    MeasureTheory.Lp.coeFn_smul c G,
    MeasureTheory.Lp.coeFn_smul c (h3SpectralScalarRawFourierL2 G)
  ] with ξ hLeft hG hIn hOut
  rw [hLeft, hOut]
  change
    h3SpectralScalarRawFourier (c • G) ξ
      = c • (h3SpectralScalarRawFourierL2 G : H3FourierPoint3 → ℂ) ξ
  rw [hG]
  unfold h3SpectralScalarRawFourier
  rw [hIn]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

@[simp]
theorem h3SpectralScalarDecodeComplexL2_smul_complex
    (c : ℂ)
    (G : H3SpectralScalarState) :
    h3SpectralScalarDecodeComplexL2 (c • G)
      = c • h3SpectralScalarDecodeComplexL2 G := by
  unfold h3SpectralScalarDecodeComplexL2
  rw [h3SpectralScalarRawFourierL2_smul_complex]
  exact
    (MeasureTheory.Lp.fourierTransformₗᵢ H3FourierPoint3 ℂ).symm.map_smul c
      (h3SpectralScalarRawFourierL2 G)

@[simp]
theorem h3SpectralFinVectorDecodeComplexL2_add
    (U V : H3SpectralFinVectorState) :
    h3SpectralFinVectorDecodeComplexL2 (U + V)
      =
    h3SpectralFinVectorDecodeComplexL2 U +
      h3SpectralFinVectorDecodeComplexL2 V := by
  funext i
  simp only [
    h3SpectralFinVectorDecodeComplexL2_apply,
    Pi.add_apply,
    h3SpectralScalarDecodeComplexL2_add
  ]

@[simp]
theorem h3SpectralFinVectorDecodeComplexL2_smul_complex
    (c : ℂ)
    (U : H3SpectralFinVectorState) :
    h3SpectralFinVectorDecodeComplexL2 (c • U)
      = c • h3SpectralFinVectorDecodeComplexL2 U := by
  funext i
  simp only [
    h3SpectralFinVectorDecodeComplexL2_apply,
    Pi.smul_apply,
    h3SpectralScalarDecodeComplexL2_smul_complex
  ]

/-- Exact finite-vector spectral decoding as a complex linear map. -/
noncomputable def h3SpectralFinVectorDecodeComplexL2LinearMap :
    H3SpectralFinVectorState →ₗ[ℂ] H3ComplexPhysicalFinVectorL2 where
  toFun := h3SpectralFinVectorDecodeComplexL2
  map_add' := h3SpectralFinVectorDecodeComplexL2_add
  map_smul' := h3SpectralFinVectorDecodeComplexL2_smul_complex

/-- Exact finite-vector spectral decoding as a contractive complex continuous
linear map. -/
noncomputable def h3SpectralFinVectorDecodeComplexL2CLM :
    H3SpectralFinVectorState →L[ℂ] H3ComplexPhysicalFinVectorL2 :=
  h3SpectralFinVectorDecodeComplexL2LinearMap.mkContinuous
    1
    (fun W => by
      change ‖h3SpectralFinVectorDecodeComplexL2 W‖ ≤ 1 * ‖W‖
      simpa using norm_h3SpectralFinVectorDecodeComplexL2_le W)

@[simp]
theorem h3SpectralFinVectorDecodeComplexL2CLM_apply
    (W : H3SpectralFinVectorState) :
    h3SpectralFinVectorDecodeComplexL2CLM W
      = h3SpectralFinVectorDecodeComplexL2 W :=
  rfl

/-! ## Commutation with Bochner interval integration -/

/-- Exact finite-vector spectral decoding commutes with every genuinely
Bochner-integrable interval integral. -/
theorem h3SpectralFinVectorDecodeComplexL2_intervalIntegral
    {a b : ℝ}
    (F : ℝ → H3SpectralFinVectorState)
    (hF : IntervalIntegrable F volume a b) :
    h3SpectralFinVectorDecodeComplexL2
        (∫ s in a..b, F s)
      =
    ∫ s in a..b, h3SpectralFinVectorDecodeComplexL2 (F s) := by
  symm
  exact
    h3SpectralFinVectorDecodeComplexL2CLM.intervalIntegral_comp_comm hF

/-- The decoded spectral heat--Leray Duhamel term is exactly the physical
Bochner interval integral of the decoded retarded integrand. -/
theorem h3SpectralFinHeatLerayDuhamel_decodeComplexL2_eq_intervalIntegral
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V)
        volume
        0
        t) :
    h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamel ν t hν U V)
      =
    ∫ s in (0 : ℝ)..t,
      h3SpectralFinVectorDecodeComplexL2
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V s) := by
  unfold h3SpectralFinHeatLerayDuhamel
  exact
    h3SpectralFinVectorDecodeComplexL2_intervalIntegral
      (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V)
      hInt

/-- Physical-space name for the exact decoded heat--Leray Duhamel integral. -/
noncomputable def h3PhysicalFinHeatLerayDuhamel
    (ν t : ℝ)
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState) :
    H3ComplexPhysicalFinVectorL2 :=
  ∫ s in (0 : ℝ)..t,
    h3SpectralFinVectorDecodeComplexL2
      (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V s)

/-- Under the genuine interval-integrability hypothesis, the physical Duhamel
integral is exactly the decoder of the spectral Duhamel integral. -/
theorem h3PhysicalFinHeatLerayDuhamel_eq_decodeComplexL2
    {ν t : ℝ}
    (hν : 0 < ν)
    (U V : ℝ → H3SpectralFinVectorState)
    (hInt :
      IntervalIntegrable
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν U V)
        volume
        0
        t) :
    h3PhysicalFinHeatLerayDuhamel ν t hν U V
      =
    h3SpectralFinVectorDecodeComplexL2
      (h3SpectralFinHeatLerayDuhamel ν t hν U V) := by
  symm
  exact
    h3SpectralFinHeatLerayDuhamel_decodeComplexL2_eq_intervalIntegral
      hν U V hInt

end

end Euclidean
end Bridge
end PrimeTensor
