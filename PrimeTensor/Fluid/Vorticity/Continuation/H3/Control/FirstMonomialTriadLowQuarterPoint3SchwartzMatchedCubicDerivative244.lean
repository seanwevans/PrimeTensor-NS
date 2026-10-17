import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzCompactWeightedPhysicalBridge244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadFourier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Derivative
import Mathlib.Analysis.Fourier.LpSpace

/-!
# Exact third-derivative matching for compact weighted physical Schwartz realizations

The weighted-frequency compact approximation from the previous checkpoint
is deweighted to a complex Schwartz Fourier spectrum `S`, then inverted and
real-projected to the *actual* real Schwartz function `ψ`.

This module proves two substantive Schwartz/Fourier intertwinements:

* Real-part projection COMMUTES with all ordered directional Schwartz
  derivatives (not merely with the zeroth order `L²` embedding).
* With the project's exact `2πi` Fourier convention, the `L²` physical cubic
  multiplier reconstructed from the matched weighted state is exactly the
  `L²` embedding of the third derivative of its own real Schwartz inverse.

Thus there is no extra 'derivative matching' hypothesis for a smooth compact
weighted approximant. All three ordered directions are arbitrary, with
repetitions allowed.

No Schwartz solenoidality or E₂/E₃ Cauchy theorem is asserted here; the final
finite-vector and second-order bridges are separate obligations.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean Filter Topology FourierTransform
open scoped ENNReal SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeMatchedCubicDerivative244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Schwartz real-part projection commutes with *literal* directional
 differentiation. This is proved from the Frechet chain rule, rather than
 assuming an unproved commutation property. -/
theorem h3ComplexSchwartzRealPart_lineDeriv244
    (F : SchwartzMap V3 ℂ) (v : V3) :
    ∂_{v} (h3ComplexSchwartzRealPart F) =
      h3ComplexSchwartzRealPart (∂_{v} F) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change
    (fderiv ℝ (fun y : V3 => Complex.reCLM (F y)) x) v =
      Complex.reCLM ((∂_{v} F) x)
  have hComp :
      HasFDerivAt (fun y : V3 => Complex.reCLM (F y))
        (Complex.reCLM.comp (fderiv ℝ (F : V3 → ℂ) x)) x := by
    exact Complex.reCLM.hasFDerivAt.comp x (F.hasFDerivAt x)
  rw [hComp.fderiv, ContinuousLinearMap.comp_apply]
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- All 27 ordered second derivatives commute with real projection. -/
theorem h3ComplexSchwartzRealPart_secondDerivative244
    (F : SchwartzMap V3 ℂ) (a b : A3) :
    ∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b} (h3ComplexSchwartzRealPart F)) =
    h3ComplexSchwartzRealPart
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b} F)) := by
  simp only [h3ComplexSchwartzRealPart_lineDeriv244]

/-- All 81 ordered third derivatives commute with real projection. -/
theorem h3ComplexSchwartzRealPart_thirdDerivative244
    (F : SchwartzMap V3 ℂ) (a b c : A3) :
    ∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b}
        (∂_{h3FourierAxisDirection c} (h3ComplexSchwartzRealPart F))) =
    h3ComplexSchwartzRealPart
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c} F))) := by
  simp only [h3ComplexSchwartzRealPart_lineDeriv244]

/-- The real Schwartz inverse of a complex Fourier Schwartz packet has the
 literal third derivative obtained by real-projecting the complex derivative
 of the SAME inverse packet. -/
theorem h3RawSchwartzPhysicalRealInverse_thirdDerivative244
    (S : SchwartzMap V3 ℂ) (a b c : A3) :
    ∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b}
        (∂_{h3FourierAxisDirection c}
          (h3RawSchwartzPhysicalRealInverse244 S))) =
    h3ComplexSchwartzRealPart
      (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c} (𝓕⁻ S)))) := by
  exact h3ComplexSchwartzRealPart_thirdDerivative244 (𝓕⁻ S) a b c

/-- One physical axis derivative has exactly the project's coordinate
 Fourier symbol; this fixes orientation, sign, and the `2π` factor. -/
theorem h3Schwartz_fourier_axisDerivative_apply244
    (F : SchwartzMap V3 ℂ) (a : A3) (ξ : V3) :
    𝓕 (∂_{h3FourierAxisDirection a} F) ξ =
      h3FourierDerivativeSymbol (h3ClassicalizationFinOfAxis a) ξ *
        𝓕 F ξ := by
  rw [h3Schwartz_fourier_lineDeriv_apply]
  simp only [inner_h3FourierAxisDirection,
    h3FourierDerivativeSymbol,
    h3AxisOfFin3_h3ClassicalizationFinOfAxis]

/-- Complete quadratic Schwartz multiplier, including repeated axes. -/
theorem h3Schwartz_fourier_secondDerivative_apply244
    (F : SchwartzMap V3 ℂ) (a b : A3) (ξ : V3) :
    𝓕 (∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b} F)) ξ =
    h3FourierDerivativeSymbol2
        (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b) ξ * 𝓕 F ξ := by
  rw [h3Schwartz_fourier_axisDerivative_apply244,
    h3Schwartz_fourier_axisDerivative_apply244]
  unfold h3FourierDerivativeSymbol2
  ring

/-- Complete cubic Schwartz multiplier, including all 81 ordered velocity
 component/axis combinations. -/
theorem h3Schwartz_fourier_thirdDerivative_apply244
    (F : SchwartzMap V3 ℂ) (a b c : A3) (ξ : V3) :
    𝓕 (∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b}
        (∂_{h3FourierAxisDirection c} F))) ξ =
    h3FourierDerivativeSymbol3
        (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b)
        (h3ClassicalizationFinOfAxis c) ξ * 𝓕 F ξ := by
  rw [h3Schwartz_fourier_axisDerivative_apply244,
    h3Schwartz_fourier_axisDerivative_apply244,
    h3Schwartz_fourier_axisDerivative_apply244]
  unfold h3FourierDerivativeSymbol3
  ring

/-- The third derivative of an inverse Schwartz packet has Fourier amplitude
 equal to the literal cubic symbol times the ORIGINAL packet. -/
theorem h3Schwartz_fourier_thirdOfInverse_apply244
    (S : SchwartzMap V3 ℂ) (a b c : A3) (ξ : V3) :
    𝓕 (∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b}
        (∂_{h3FourierAxisDirection c} (𝓕⁻ S)))) ξ =
    h3FourierDerivativeSymbol3
        (h3ClassicalizationFinOfAxis a)
        (h3ClassicalizationFinOfAxis b)
        (h3ClassicalizationFinOfAxis c) ξ * S ξ := by
  rw [h3Schwartz_fourier_thirdDerivative_apply244,
    FourierTransform.fourier_fourierInv_eq]

/-- On ANY weighted spectral scalar state F whose deweighted Fourier L²
 representation is exactly the Schwartz packet S, the actual cubic Fourier
 L² multiplier package equals the Fourier L² class of the literal third
 derivative of `𝓕⁻ S`. -/
theorem h3SpectralScalarRawThirdCoordinateFourierL2_schwartzDerivative244
    (F : H3SpectralScalarState) (S : SchwartzMap V3 ℂ)
    (hRaw : h3SpectralScalarRawFourierL2 F =
      S.toLp 2 (volume : Measure V3)) (a b c : A3) :
    h3SpectralScalarRawThirdCoordinateFourierL2 a b c F =
      (𝓕 (∂_{h3FourierAxisDirection a}
        (∂_{h3FourierAxisDirection b}
          (∂_{h3FourierAxisDirection c} (𝓕⁻ S))))).toLp
            2 (volume : Measure V3) := by
  have hRawAE :
      h3SpectralScalarRawFourier F =ᵐ[volume]
        (S : V3 → ℂ) := by
    have h := h3SpectralScalarRawFourierL2_ae F
    rw [hRaw] at h
    exact h.symm.trans (S.coeFn_toLp 2 (volume : Measure V3))
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarRawThirdCoordinateFourierL2_ae a b c F,
    hRawAE,
    (𝓕 (∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b}
        (∂_{h3FourierAxisDirection c} (𝓕⁻ S))))).coeFn_toLp
          2 (volume : Measure V3)
  ] with ξ hCubic hRawAt hDerivative
  rw [hCubic, hDerivative, hRawAt]
  rw [h3Schwartz_fourier_thirdOfInverse_apply244]
  unfold h3FourierDerivativeSymbol3
  ring

/-- The central hard-math bridge: the existing canonical PHYSICAL real cubic
 L² reconstruction is EXACTLY the third derivative of the MATCHED real
 Schwartz inverse, after the canonical Euclidean-to-Point3 carrier transport.
 No additional derivative identification hypothesis is required. -/
theorem h3SpectralScalarRawThirdCoordinatePhysicalL2_realSchwartzDerivative244
    (F : H3SpectralScalarState) (S : SchwartzMap V3 ℂ)
    (hRaw : h3SpectralScalarRawFourierL2 F =
      S.toLp 2 (volume : Measure V3)) (a b c : A3) :
    h3SpectralScalarRawThirdCoordinatePhysicalL2 a b c F =
      h3FromFourierRealL2
        ((∂_{h3FourierAxisDirection a}
          (∂_{h3FourierAxisDirection b}
            (∂_{h3FourierAxisDirection c}
              (h3RawSchwartzPhysicalRealInverse244 S)))).toLp
                2 (volume : Measure V3)) := by
  let D : SchwartzMap V3 ℂ :=
    ∂_{h3FourierAxisDirection a}
      (∂_{h3FourierAxisDirection b}
        (∂_{h3FourierAxisDirection c} (𝓕⁻ S)))
  have hFourier :
      h3SpectralScalarRawThirdCoordinateFourierL2 a b c F =
        (𝓕 D).toLp 2 (volume : Measure V3) := by
    exact h3SpectralScalarRawThirdCoordinateFourierL2_schwartzDerivative244
      F S hRaw a b c
  have hInv :
      (MeasureTheory.Lp.fourierTransformₗᵢ V3 ℂ).symm
        ((𝓕 D).toLp 2 (volume : Measure V3)) =
      D.toLp 2 (volume : Measure V3) := by
    change 𝓕⁻ ((𝓕 D).toLp 2 (volume : Measure V3)) =
      D.toLp 2 (volume : Measure V3)
    simpa only [FourierTransform.fourierInv_fourier_eq] using
      (SchwartzMap.toLp_fourierInv_eq (𝓕 D))
  unfold h3SpectralScalarRawThirdCoordinatePhysicalL2
  rw [hFourier, hInv]
  rw [h3RealPartFourierL2_schwartz_toLp244 D]
  rw [h3RawSchwartzPhysicalRealInverse_thirdDerivative244]

/-- Smooth-compact density may be chosen with FULL third-derivative matching,
 not merely matching of the zeroth physical L² velocity. Every axis triple
 is handled by the SAME F and the SAME genuine real Schwartz ψ. -/
theorem exists_h3SmoothCompactWeighted_realSchwartzExactThird244
    (G : H3SpectralScalarState) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : H3SpectralScalarState,
    ∃ ψ : SchwartzMap V3 ℝ,
      ‖G - F‖ < ε ∧
      h3SpectralScalarDecodeRealL2 F =
        ψ.toLp 2 (volume : Measure V3) ∧
      (∀ a b c : A3,
        h3SpectralScalarRawThirdCoordinatePhysicalL2 a b c F =
          h3FromFourierRealL2
            ((∂_{h3FourierAxisDirection a}
              (∂_{h3FourierAxisDirection b}
                (∂_{h3FourierAxisDirection c} ψ))).toLp
                  2 (volume : Measure V3))) := by
  obtain ⟨F, ⟨g, hg, hcompact, hsmooth⟩, hClose⟩ :=
    exists_h3SmoothCompact_spectralApprox_norm G hε
  let S : SchwartzMap V3 ℂ :=
    h3SmoothCompactDeweightedSchwartz g hcompact hsmooth
  let ψ : SchwartzMap V3 ℝ := h3RawSchwartzPhysicalRealInverse244 S
  have hRaw :
      h3SpectralScalarRawFourierL2 F =
        S.toLp 2 (volume : Measure V3) := by
    exact h3SpectralScalarRawFourierL2_eq_deweightedSchwartz_toLp
      F g hg hcompact hsmooth
  have hDecode :
      h3SpectralScalarDecodeRealL2 F =
        ψ.toLp 2 (volume : Measure V3) := by
    change h3RealPartFourierL2
      ((MeasureTheory.Lp.fourierTransformₗᵢ V3 ℂ).symm
        (h3SpectralScalarRawFourierL2 F)) =
          (h3RawSchwartzPhysicalRealInverse244 S).toLp
            2 (volume : Measure V3)
    rw [hRaw]
    have hInv :
        (MeasureTheory.Lp.fourierTransformₗᵢ V3 ℂ).symm
          (S.toLp 2 (volume : Measure V3)) =
        (𝓕⁻ S).toLp 2 (volume : Measure V3) := by
      change 𝓕⁻ (S.toLp 2 (volume : Measure V3)) =
        (𝓕⁻ S).toLp 2 (volume : Measure V3)
      exact SchwartzMap.toLp_fourierInv_eq S
    rw [hInv]
    exact h3RealPartFourierL2_schwartz_toLp244 (𝓕⁻ S)
  refine ⟨F, ψ, hClose, hDecode, ?_⟩
  intro a b c
  exact h3SpectralScalarRawThirdCoordinatePhysicalL2_realSchwartzDerivative244
    F S hRaw a b c

end
end PrimeTensor.FirstMonomialTriad
