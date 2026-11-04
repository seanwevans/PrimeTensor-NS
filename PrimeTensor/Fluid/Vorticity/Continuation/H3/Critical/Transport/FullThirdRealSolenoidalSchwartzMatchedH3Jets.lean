import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdRealSolenoidalSchwartzH3Density
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzMatchedSecondFamily244
import Mathlib.Tactic

/-!
# Exact second and third derivative jets for the solenoidal Schwartz H³ density

The preceding constructive density theorem supplies one sequence of genuine
real, exactly divergence-free Schwartz velocities with weighted Fourier
representatives converging in H³. This module identifies the scalar zeroth,
second and third *literal Schwartz derivatives* with the canonical real
physical spectral L² reconstructions of those same weighted states.

The proof first deweights an a.e. Fourier representative, taking care not to
identify an L² class pointwise. Fourier inversion on Schwartz space then
identifies the recovered real physical function with the original real
Schwartz field. Existing exact second/third derivative realization lemmas
apply without new derivative-compatibility assumptions. Finally, the proven
continuity of all 27 quadratic and all 81 cubic L² jet families transfers
weighted H³ convergence of the very same solenoidal sequence.

This is strong density for the spatial H³ graph. It does not assert a new
Navier--Stokes continuation estimate or automatically transfer any nonlinear
quartic functional beyond the limits already established elsewhere.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Filter Topology PrimeTensor.Bridge.Euclidean FourierTransform
open scoped ENNReal BigOperators SchwartzMap FourierTransform LineDeriv

noncomputable section
set_option maxHeartbeats 1600000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev Freq244 := A3 → ℝ
private abbrev CPol244 := A3 → ℂ

noncomputable local instance axisFintypeMatchedSolenoidalJets244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Deweight an actual weighted Fourier L² representative of a real
Schwartz function. This is an identity of L² classes, not of arbitrarily
chosen pointwise L² representatives. -/
theorem thirdFullWeightedRealSchwartz_rawFourier_eq244
    (F : H3SpectralScalarState) (ψ : SchwartzMap V3 ℝ)
    (hWeighted : (F : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
        𝓕 (h3SchwartzComplexify ψ) ξ)) :
    h3SpectralScalarRawFourierL2 F =
      (𝓕 (h3SchwartzComplexify ψ)).toLp
        2 (volume : Measure V3) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    h3SpectralScalarRawFourierL2_ae F,
    hWeighted,
    (𝓕 (h3SchwartzComplexify ψ)).coeFn_toLp
      2 (volume : Measure V3)
  ] with ξ hRaw hWeight hSchwartz
  rw [hRaw, hSchwartz]
  change h3SobolevFrequencyWeightInvComplex ξ * F ξ = _
  rw [hWeight]
  calc
    h3SobolevFrequencyWeightInvComplex ξ *
        ((h3SobolevFrequencyWeight ξ : ℂ) *
          𝓕 (h3SchwartzComplexify ψ) ξ) =
      ((h3SobolevFrequencyWeight ξ : ℂ) *
        h3SobolevFrequencyWeightInvComplex ξ) *
          𝓕 (h3SchwartzComplexify ψ) ξ := by ring
    _ = 𝓕 (h3SchwartzComplexify ψ) ξ := by
      rw [h3SobolevFrequencyWeight_mul_invComplex, one_mul]

/-- Fourier inversion followed by real-part projection fixes each actual
real Schwartz function, exactly rather than almost everywhere. -/
theorem thirdFullRawRealSchwartzInverse_fourier_complexify_eq244
    (ψ : SchwartzMap V3 ℝ) :
    h3RawSchwartzPhysicalRealInverse244
      (𝓕 (h3SchwartzComplexify ψ)) = ψ := by
  unfold h3RawSchwartzPhysicalRealInverse244
  rw [FourierTransform.fourierInv_fourier_eq]
  ext x
  simp only [h3ComplexSchwartzRealPart_apply,
    h3SchwartzComplexify_apply, Complex.ofReal_re]

/-- A single weighted Schwartz Fourier-representative identity enforces
literal physical L² equality for the velocity, every ordered second jet,
and every ordered third jet. The Fourier and physical derivatives use the
project's actual 2π-normalized multiplier convention. -/
theorem thirdFullWeightedRealSchwartz_exactSecondThirdJets244
    (F : H3SpectralScalarState) (ψ : SchwartzMap V3 ℝ)
    (hWeighted : (F : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
        𝓕 (h3SchwartzComplexify ψ) ξ)) :
    h3SpectralScalarDecodeRealL2 F =
      ψ.toLp 2 (volume : Measure V3) ∧
    (∀ a b : A3,
      h3SpectralScalarRawSecondCoordinatePhysicalL2_244 a b F =
        h3FromFourierRealL2
          ((∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b} ψ)).toLp
              2 (volume : Measure V3))) ∧
    (∀ a b c : A3,
      h3SpectralScalarRawThirdCoordinatePhysicalL2 a b c F =
        h3FromFourierRealL2
          ((∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b}
              (∂_{h3FourierAxisDirection c} ψ))).toLp
                2 (volume : Measure V3))) := by
  let S : SchwartzMap V3 ℂ := 𝓕 (h3SchwartzComplexify ψ)
  have hRaw : h3SpectralScalarRawFourierL2 F =
      S.toLp 2 (volume : Measure V3) :=
    thirdFullWeightedRealSchwartz_rawFourier_eq244 F ψ hWeighted
  have hInverse : h3RawSchwartzPhysicalRealInverse244 S = ψ :=
    thirdFullRawRealSchwartzInverse_fourier_complexify_eq244 ψ
  have hFourierInv :
      (MeasureTheory.Lp.fourierTransformₗᵢ V3 ℂ).symm
        (S.toLp 2 (volume : Measure V3)) =
      (𝓕⁻ S).toLp 2 (volume : Measure V3) := by
    change 𝓕⁻ (S.toLp 2 (volume : Measure V3)) =
      (𝓕⁻ S).toLp 2 (volume : Measure V3)
    exact SchwartzMap.toLp_fourierInv_eq S
  have hDecode : h3SpectralScalarDecodeRealL2 F =
      ψ.toLp 2 (volume : Measure V3) := by
    change h3RealPartFourierL2
      ((MeasureTheory.Lp.fourierTransformₗᵢ V3 ℂ).symm
        (h3SpectralScalarRawFourierL2 F)) = _
    rw [hRaw, hFourierInv]
    have hReal := h3RealPartFourierL2_schwartz_toLp244 (𝓕⁻ S)
    change h3RealPartFourierL2 ((𝓕⁻ S).toLp
      2 (volume : Measure V3)) =
      (h3RawSchwartzPhysicalRealInverse244 S).toLp
        2 (volume : Measure V3) at hReal
    rw [hReal, hInverse]
  refine ⟨hDecode, ?_, ?_⟩
  · intro a b
    have hSecond :=
      h3SpectralScalarRawSecondCoordinatePhysicalL2_realSchwartzDerivative244
        F S hRaw a b
    rw [hInverse] at hSecond
    exact hSecond
  · intro a b c
    have hThird :=
      h3SpectralScalarRawThirdCoordinatePhysicalL2_realSchwartzDerivative244
        F S hRaw a b c
    rw [hInverse] at hThird
    exact hThird

/-- One and the same ACTUAL real, divergence-free Schwartz sequence has
matched physical derivatives in all 27+81 ordered slots and converges in
the full second/third real physical L² jet topology. The only assumptions
are the real-data Hermitian condition and spectral incompressibility of the
target. In particular, no matching or Schwartz-density witness is assumed. -/
theorem exists_thirdFullRealSolenoidalSchwartzMatchedH3Jets244
    (target : H3SpectralVelocityState)
    (hDiv : H3SpectralFinDivergenceFree target)
    (hReal : H3SpectralVelocityRawHermitian target) :
    ∃ (V : ℕ → H3SpectralVelocityState)
      (Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ),
      Tendsto V atTop (𝓝 target) ∧
      (∀ (n : ℕ) (x : V3), ∑ j : A3,
        fderiv ℝ (h3SchwartzComplexify
          (Ψ n (h3ClassicalizationFinOfAxis j))) x
            (h3FourierAxisDirection j) = 0) ∧
      (∀ n j,
        (V n j : V3 → ℂ) =ᵐ[volume]
          (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
            𝓕 (h3SchwartzComplexify (Ψ n j)) ξ)) ∧
      (∀ n j,
        h3SpectralVelocityDecodeRealL2 (V n) j =
          (Ψ n j).toLp 2 (volume : Measure V3)) ∧
      (∀ n j a b,
        h3SpectralVelocitySecondPhysicalJetFamily244 (V n) j a b =
          h3FromFourierRealL2
            ((∂_{h3FourierAxisDirection a}
              (∂_{h3FourierAxisDirection b} (Ψ n j))).toLp
                2 (volume : Measure V3))) ∧
      (∀ n j a b c,
        h3SpectralVelocityThirdPhysicalJetFamily244 (V n) j a b c =
          h3FromFourierRealL2
            ((∂_{h3FourierAxisDirection a}
              (∂_{h3FourierAxisDirection b}
                (∂_{h3FourierAxisDirection c} (Ψ n j)))).toLp
                  2 (volume : Measure V3))) ∧
      Tendsto (fun n => h3SpectralVelocityDecodeRealL2 (V n))
        atTop (𝓝 (h3SpectralVelocityDecodeRealL2 target)) ∧
      Tendsto (fun n => h3SpectralVelocitySecondPhysicalJetFamily244 (V n))
        atTop (𝓝 (h3SpectralVelocitySecondPhysicalJetFamily244 target)) ∧
      Tendsto (fun n => h3SpectralVelocityThirdPhysicalJetFamily244 (V n))
        atTop (𝓝 (h3SpectralVelocityThirdPhysicalJetFamily244 target)) ∧
      CauchySeq V := by
  obtain ⟨Φ, χ, hχsmooth, hχcompact,
    hLimit, hFourier, hPhysical, _hDecode, hCauchy⟩ :=
    exists_thirdFullRealSolenoidalPhysicalSchwartzH3Density244
      target hDiv hReal
  let V : ℕ → H3SpectralVelocityState := fun n =>
    h3FullThirdRadialRecoveryVelocity244 n
      (h3SpectralFinLerayApply
        (h3SchwartzSpectralVelocityRealization244 (Φ n)))
  let Ψ : ℕ → Fin 3 → SchwartzMap V3 ℝ := fun n j =>
    thirdFullRegularizedPhysicalSchwartzAt244 n (χ n)
      (thirdFullDeweightedCompactAxisProfile244 (Φ n))
      (hχsmooth n) (hχcompact n)
      (thirdFullDeweightedCompactAxisProfile_contDiff244 (Φ n))
      (h3AxisOfFin3 j)
  have hV : Tendsto V atTop (𝓝 target) := hLimit
  have hAE (n : ℕ) (j : Fin 3) :
      (V n j : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          𝓕 (h3SchwartzComplexify (Ψ n j)) ξ) :=
    hFourier n j
  have hDivExact (n : ℕ) (x : V3) :
      (∑ j : A3,
        fderiv ℝ (h3SchwartzComplexify
          (Ψ n (h3ClassicalizationFinOfAxis j))) x
            (h3FourierAxisDirection j)) = 0 := by
    simpa only [Ψ, h3AxisOfFin3_h3ClassicalizationFinOfAxis] using
      hPhysical n x
  have hMatched (n : ℕ) (j : Fin 3) :
      h3SpectralScalarDecodeRealL2 (V n j) =
        (Ψ n j).toLp 2 (volume : Measure V3) ∧
      (∀ a b : A3,
        h3SpectralScalarRawSecondCoordinatePhysicalL2_244 a b (V n j) =
          h3FromFourierRealL2
            ((∂_{h3FourierAxisDirection a}
              (∂_{h3FourierAxisDirection b} (Ψ n j))).toLp
                2 (volume : Measure V3))) ∧
      (∀ a b c : A3,
        h3SpectralScalarRawThirdCoordinatePhysicalL2 a b c (V n j) =
          h3FromFourierRealL2
            ((∂_{h3FourierAxisDirection a}
              (∂_{h3FourierAxisDirection b}
                (∂_{h3FourierAxisDirection c} (Ψ n j)))).toLp
                  2 (volume : Measure V3))) :=
    thirdFullWeightedRealSchwartz_exactSecondThirdJets244
      (V n j) (Ψ n j) (hAE n j)
  have hDecoderExact (n : ℕ) (j : Fin 3) :
      h3SpectralVelocityDecodeRealL2 (V n) j =
        (Ψ n j).toLp 2 (volume : Measure V3) :=
    (hMatched n j).1
  have hSecondExact (n : ℕ) (j : Fin 3) (a b : A3) :
      h3SpectralVelocitySecondPhysicalJetFamily244 (V n) j a b =
        h3FromFourierRealL2
          ((∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b} (Ψ n j))).toLp
              2 (volume : Measure V3)) :=
    (hMatched n j).2.1 a b
  have hThirdExact (n : ℕ) (j : Fin 3) (a b c : A3) :
      h3SpectralVelocityThirdPhysicalJetFamily244 (V n) j a b c =
        h3FromFourierRealL2
          ((∂_{h3FourierAxisDirection a}
            (∂_{h3FourierAxisDirection b}
              (∂_{h3FourierAxisDirection c} (Ψ n j)))).toLp
                2 (volume : Measure V3)) :=
    (hMatched n j).2.2 a b c
  exact ⟨V, Ψ, hV, hDivExact, hAE,
    hDecoderExact, hSecondExact, hThirdExact,
    h3SpectralVelocityDecodeRealL2_tendsto_of_weighted244 hV,
    h3SpectralVelocitySecondPhysicalJetFamily_tendsto_of_weighted244 hV,
    h3SpectralVelocityThirdPhysicalJetFamily_tendsto_of_weighted244 hV,
    hCauchy⟩

end
end PrimeTensor.FirstMonomialTriad
