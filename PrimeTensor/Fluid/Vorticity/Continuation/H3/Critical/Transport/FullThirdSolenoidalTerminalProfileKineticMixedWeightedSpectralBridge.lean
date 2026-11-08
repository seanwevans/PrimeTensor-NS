import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticMixedYoungConvolution
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalPhysicalMomentBridge
import Mathlib.Tactic

/-!
# Actual weighted-H3 input estimates for the native mixed low-maximum sixth flux

The exact sixth-power polarization telescope has three mixed terms. The mixed
Young inequality bounds one such term by two squared Fourier-L2 amplitudes and
one Fourier-L1 amplitude, but those quantities must come from the *actual*
Schwartz Fourier representatives of weighted-H3 spectral velocities.

This module discharges both moment hypotheses quantitatively. For any complex
three-component Schwartz velocity v with exact weighted spectral representatives
G_j = W3 * Fourier(v_j) almost everywhere, its genuine vector Fourier amplitude
A_v satisfies

  integral A_v^2 <= sum_j ||G_j||^2,
  integral A_v   <= C0 * sum_j ||G_j||,

where C0 is the already formalized Sobolev deweighting constant. In particular,
if every ||G_j|| <= K, then these become 3 K^2 and 3 C0 K.

For *three distinct* Schwartz profiles the preceding exact mixed sixth-flux
Young estimate consequently has a weighted-H3 three-input bound, with the free
reciprocal scaling retained. The assumptions that the mixed *six-dimensional*
budget is globally integrable and the mixed flux is integrable on LowMax are
still stated explicitly. This file does not infer their integrability from
weak convergence, nor claim a terminal-uniform H3 bound.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology FourierTransform
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private abbrev WA3 := PrimeTensor.Axis Depth.three
private abbrev WV3 := H3FourierPoint3
private abbrev WPair := WV3 × WV3

noncomputable local instance axisFintypeKineticWeightedMixed244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact *complex* three-component Fourier polarization of a Schwartz
field. No absolute values or imaginary-part projection enter this profile. -/
noncomputable def thirdFullKineticSchwartzPolarization244
    (v : WA3 → SchwartzMap WV3 ℂ) (ξ : WV3) : WA3 → ℂ :=
  h3SchwartzTriadPolarization v (WithLp.ofLp ξ)

/-- The native mixed-Young amplitude is literally the old Schwartz
triad amplitude when instantiated on its exact Fourier polarization. -/
theorem thirdFullKineticSchwartzPolarization_amplitude244
    (v : WA3 → SchwartzMap WV3 ℂ) (ξ : WV3) :
    thirdFullKineticPolarAmplitude244
      (thirdFullKineticSchwartzPolarization244 v) ξ =
    h3TriadSpectralAmplitude v ξ := rfl

/-- The true complex Schwartz Fourier amplitude is integrable, and so is
its square, with no additional raw-moment hypothesis. -/
theorem thirdFullKineticSchwartzPolarization_moments_integrable244
    (v : WA3 → SchwartzMap WV3 ℂ) :
    Integrable (thirdFullKineticPolarAmplitude244
      (thirdFullKineticSchwartzPolarization244 v)) volume ∧
    Integrable (fun ξ : WV3 =>
      thirdFullKineticPolarAmplitude244
        (thirdFullKineticSchwartzPolarization244 v) ξ ^ 2) volume := by
  constructor
  · change Integrable (fun ξ : WV3 => h3TriadSpectralAmplitude v ξ) volume
    have h := h3TriadSpectralAmplitude_integrable_pow_mul v 0
    have hEq :
        (fun ξ : WV3 => ‖ξ‖ ^ 0 * h3TriadSpectralAmplitude v ξ) =
          (fun ξ : WV3 => h3TriadSpectralAmplitude v ξ) := by
      funext ξ
      simp only [pow_zero, one_mul]
    rwa [hEq] at h
  · change Integrable (fun ξ : WV3 => h3TriadSpectralAmplitude v ξ ^ 2) volume
    have h := h3TriadSpectralAmplitude_integrable_pow_mul_sq v 0
    have hEq :
        (fun ξ : WV3 => ‖ξ‖ ^ 0 * h3TriadSpectralAmplitude v ξ ^ 2) =
          (fun ξ : WV3 => h3TriadSpectralAmplitude v ξ ^ 2) := by
      funext ξ
      simp only [pow_zero, one_mul]
    rwa [hEq] at h

/-- Quantitative *zeroth* Fourier-L1 mass for the SAME Schwartz transform
represented by a weighted-H3 scalar state. This is the actual Holder
representative and the native Sobolev deweighting constant C0. -/
theorem thirdFullKineticWeightedSchwartz_scalarFourierL1_le244
    (G : H3SpectralScalarState) (f : SchwartzMap WV3 ℂ)
    (hG : (G : WV3 → ℂ) =ᵐ[volume]
      (fun ξ : WV3 => (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 f) ξ)) :
    (∫ ξ : WV3, ‖(𝓕 f) ξ‖ ∂volume) ≤
      h3SobolevDeweightingConstant * ‖G‖ := by
  have hRaw := thirdFullWeightedSchwartz_rawFourier_ae244 G f hG
  have hHolder := h3SpectralScalarRawFourierHolderL1_ae G
  calc
    (∫ ξ : WV3, ‖(𝓕 f) ξ‖ ∂volume) =
        ‖h3SpectralScalarRawFourierHolderL1 G‖ := by
      rw [L1.norm_eq_integral_norm]
      apply integral_congr_ae
      filter_upwards [hRaw, hHolder] with ξ hξ hHoldξ
      rw [hξ, ← hHoldξ]
    _ ≤ h3SobolevDeweightingConstant * ‖G‖ :=
      norm_h3SpectralScalarRawFourierHolderL1_le G

/-- The genuine three-component raw Fourier L1 amplitude is bounded by
the SAME three weighted-H3 scalar coordinate norms. No independent Fourier
L1 bound is assumed. -/
theorem thirdFullKineticWeightedSchwartz_vectorFourierL1_le244
    (v : WA3 → SchwartzMap WV3 ℂ)
    (G : WA3 → H3SpectralScalarState)
    (hG : ∀ j : WA3, (G j : WV3 → ℂ) =ᵐ[volume]
      (fun ξ : WV3 =>
        (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ)) :
    (∫ ξ : WV3,
      thirdFullKineticPolarAmplitude244
        (thirdFullKineticSchwartzPolarization244 v) ξ ∂volume) ≤
      ∑ j : WA3, h3SobolevDeweightingConstant * ‖G j‖ := by
  have hIntCoord (j : WA3) :
      Integrable (fun ξ : WV3 => ‖(𝓕 (v j)) ξ‖) volume := by
    have h := (𝓕 (v j)).integrable_pow_mul volume 0
    have hEq :
        (fun ξ : WV3 => ‖ξ‖ ^ 0 * ‖(𝓕 (v j)) ξ‖) =
          (fun ξ : WV3 => ‖(𝓕 (v j)) ξ‖) := by
      funext ξ
      simp only [pow_zero, one_mul]
    rwa [hEq] at h
  have hMajor : Integrable
      (fun ξ : WV3 => ∑ j : WA3, ‖(𝓕 (v j)) ξ‖) volume :=
    integrable_finsetSum Finset.univ (fun j _ => hIntCoord j)
  have hAmp : Integrable
      (thirdFullKineticPolarAmplitude244
        (thirdFullKineticSchwartzPolarization244 v)) volume :=
    (thirdFullKineticSchwartzPolarization_moments_integrable244 v).1
  calc
    (∫ ξ : WV3,
        thirdFullKineticPolarAmplitude244
          (thirdFullKineticSchwartzPolarization244 v) ξ ∂volume) ≤
      ∫ ξ : WV3, ∑ j : WA3, ‖(𝓕 (v j)) ξ‖ ∂volume := by
        apply integral_mono hAmp hMajor
        intro ξ
        simpa only [thirdFullKineticSchwartzPolarization_amplitude244]
          using h3TriadSpectralAmplitude_le_sum v ξ
    _ = ∑ j : WA3, ∫ ξ : WV3, ‖(𝓕 (v j)) ξ‖ ∂volume := by
      simpa using (integral_finsetSum (μ := (volume : Measure WV3))
        (Finset.univ : Finset WA3) (fun j _ => hIntCoord j))
    _ ≤ ∑ j : WA3, h3SobolevDeweightingConstant * ‖G j‖ :=
      Finset.sum_le_sum (fun j _ =>
        thirdFullKineticWeightedSchwartz_scalarFourierL1_le244
          (G j) (v j) (hG j))

/-- The *squared* amplitude is not controlled by Fourier-L1 alone; the
actual Plancherel contraction of the three weighted representatives supplies
this independent L2 estimate. -/
theorem thirdFullKineticWeightedSchwartz_vectorFourierL2_le244
    (v : WA3 → SchwartzMap WV3 ℂ)
    (G : WA3 → H3SpectralScalarState)
    (hG : ∀ j : WA3, (G j : WV3 → ℂ) =ᵐ[volume]
      (fun ξ : WV3 =>
        (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ)) :
    (∫ ξ : WV3,
      thirdFullKineticPolarAmplitude244
        (thirdFullKineticSchwartzPolarization244 v) ξ ^ 2 ∂volume) ≤
      ∑ j : WA3, ‖G j‖ ^ 2 := by
  simpa only [thirdFullKineticSchwartzPolarization_amplitude244,
    thirdFullBudgetFourierMass244, thirdFullBudgetMomentAmplitude244]
    using (thirdFullWeightedSchwartz_vectorMoments_le244 v G hG).1

/-- If the three weighted spectral coordinates are bounded by K, the
actual physical Fourier input has both required Young moments: 3 K^2 in
L2 and 3 C0 K in L1. No separate raw Fourier moments are inserted. -/
theorem thirdFullKineticWeightedSchwartz_vectorMoments_le244
    (v : WA3 → SchwartzMap WV3 ℂ)
    (G : WA3 → H3SpectralScalarState)
    (hG : ∀ j : WA3, (G j : WV3 → ℂ) =ᵐ[volume]
      (fun ξ : WV3 =>
        (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (K : ℝ) (hK : 0 ≤ K) (hBound : ∀ j : WA3, ‖G j‖ ≤ K) :
    (∫ ξ : WV3,
      thirdFullKineticPolarAmplitude244
        (thirdFullKineticSchwartzPolarization244 v) ξ ^ 2 ∂volume) ≤
        3 * K ^ 2 ∧
    (∫ ξ : WV3,
      thirdFullKineticPolarAmplitude244
        (thirdFullKineticSchwartzPolarization244 v) ξ ∂volume) ≤
        3 * h3SobolevDeweightingConstant * K := by
  have hC : 0 ≤ h3SobolevDeweightingConstant :=
    h3SobolevDeweightingConstant_nonneg
  constructor
  · calc
      _ ≤ ∑ j : WA3, ‖G j‖ ^ 2 :=
        thirdFullKineticWeightedSchwartz_vectorFourierL2_le244 v G hG
      _ ≤ ∑ _j : WA3, K ^ 2 :=
        Finset.sum_le_sum (fun j _ =>
          (sq_le_sq₀ (norm_nonneg (G j)) hK).mpr (hBound j))
      _ = 3 * K ^ 2 := by rw [axis_sum_three]; ring
  · calc
      _ ≤ ∑ j : WA3, h3SobolevDeweightingConstant * ‖G j‖ :=
        thirdFullKineticWeightedSchwartz_vectorFourierL1_le244 v G hG
      _ ≤ ∑ _j : WA3, h3SobolevDeweightingConstant * K :=
        Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hBound j) hC)
      _ = 3 * h3SobolevDeweightingConstant * K := by
        rw [axis_sum_three]
        ring

/-- The preceding estimates apply directly to the *native finite-vector*
weighted-H3 spectral state, without substituting three independent ceilings.
The product finite-vector norm already dominates every coordinate. -/
theorem thirdFullKineticWeightedSchwartz_velocityMoments_le244
    (v : WA3 → SchwartzMap WV3 ℂ)
    (V : H3SpectralVelocityState)
    (hRep : ∀ j : WA3,
      (V (h3ClassicalizationFinOfAxis j) : WV3 → ℂ) =ᵐ[volume]
        (fun ξ : WV3 =>
          (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ)) :
    (∫ ξ : WV3,
      thirdFullKineticPolarAmplitude244
        (thirdFullKineticSchwartzPolarization244 v) ξ ^ 2 ∂volume) ≤
        3 * ‖V‖ ^ 2 ∧
    (∫ ξ : WV3,
      thirdFullKineticPolarAmplitude244
        (thirdFullKineticSchwartzPolarization244 v) ξ ∂volume) ≤
        3 * h3SobolevDeweightingConstant * ‖V‖ := by
  let G : WA3 → H3SpectralScalarState :=
    fun j => V (h3ClassicalizationFinOfAxis j)
  have hBound (j : WA3) : ‖G j‖ ≤ ‖V‖ :=
    h3SpectralFinVector_coordinate_norm_le V
      (h3ClassicalizationFinOfAxis j)
  exact thirdFullKineticWeightedSchwartz_vectorMoments_le244
    v G hRep ‖V‖ (norm_nonneg V) hBound

/-- THREE distinct genuine Schwartz polarizations, each represented by its
own weighted-H3 spectral velocity, satisfy an explicit mixed sixth-flux
bound with no additional *Fourier moment* assumptions. The prior mixed
six-dimensional integrability contracts remain explicit; they are NOT
inferred from pointwise spectral convergence. -/
theorem thirdFullKinetic_lowMax_mixedSchwartzFlux_le_weightedH3_244
    (R : ℕ)
    (v w h : WA3 → SchwartzMap WV3 ℂ)
    (Gv Gw Gh : WA3 → H3SpectralScalarState)
    (hv : ∀ j : WA3, (Gv j : WV3 → ℂ) =ᵐ[volume]
      (fun ξ : WV3 =>
        (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : WA3, (Gw j : WV3 → ℂ) =ᵐ[volume]
      (fun ξ : WV3 =>
        (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ))
    (hh : ∀ j : WA3, (Gh j : WV3 → ℂ) =ᵐ[volume]
      (fun ξ : WV3 =>
        (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (h j)) ξ))
    (Kv Kw Kh : ℝ)
    (hKv : 0 ≤ Kv) (hKw : 0 ≤ Kw) (hKh : 0 ≤ Kh)
    (hbv : ∀ j : WA3, ‖Gv j‖ ≤ Kv)
    (hbw : ∀ j : WA3, ‖Gw j‖ ≤ Kw)
    (hbh : ∀ j : WA3, ‖Gh j‖ ≤ Kh)
    (hFlux : IntegrableOn
      (thirdFullKineticMixedPolarSixthFlux244
        (thirdFullKineticSchwartzPolarization244 v)
        (thirdFullKineticSchwartzPolarization244 w)
        (thirdFullKineticSchwartzPolarization244 h))
      (thirdFullHighMaxSet244 R)ᶜ (volume.prod volume))
    (hBudget : Integrable
      (thirdFullKineticMixedPolarSixthBudget244
        (thirdFullKineticSchwartzPolarization244 v)
        (thirdFullKineticSchwartzPolarization244 w)
        (thirdFullKineticSchwartzPolarization244 h))
      (volume.prod volume))
    (scale : ℝ) (hscale : 0 < scale) :
    (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      ‖thirdFullKineticMixedPolarSixthFlux244
        (thirdFullKineticSchwartzPolarization244 v)
        (thirdFullKineticSchwartzPolarization244 w)
        (thirdFullKineticSchwartzPolarization244 h) z‖
        ∂volume.prod volume) ≤
    (9 * (2 * ((R : ℝ) + 1)) ^ 7) *
      (((scale ^ 2 * (3 * Kv ^ 2) +
        scale⁻¹ ^ 2 * (3 * Kh ^ 2)) / 2) *
        (3 * h3SobolevDeweightingConstant * Kw)) := by
  let P := thirdFullKineticSchwartzPolarization244 v
  let Q := thirdFullKineticSchwartzPolarization244 w
  let W := thirdFullKineticSchwartzPolarization244 h
  let ρ : ℝ := 2 * ((R : ℝ) + 1)
  let A : ℝ := ∫ ξ : WV3, thirdFullKineticPolarAmplitude244 P ξ ^ 2 ∂volume
  let B : ℝ := ∫ ξ : WV3, thirdFullKineticPolarAmplitude244 W ξ ^ 2 ∂volume
  let D : ℝ := ∫ ξ : WV3, thirdFullKineticPolarAmplitude244 Q ξ ∂volume
  have hPInt : Integrable (fun ξ : WV3 => thirdFullKineticPolarAmplitude244 P ξ ^ 2)
      volume := (thirdFullKineticSchwartzPolarization_moments_integrable244 v).2
  have hWInt : Integrable (fun ξ : WV3 => thirdFullKineticPolarAmplitude244 W ξ ^ 2)
      volume := (thirdFullKineticSchwartzPolarization_moments_integrable244 h).2
  have hQInt : Integrable (thirdFullKineticPolarAmplitude244 Q) volume :=
    (thirdFullKineticSchwartzPolarization_moments_integrable244 w).1
  have hA : A ≤ 3 * Kv ^ 2 :=
    (thirdFullKineticWeightedSchwartz_vectorMoments_le244
      v Gv hv Kv hKv hbv).1
  have hB : B ≤ 3 * Kh ^ 2 :=
    (thirdFullKineticWeightedSchwartz_vectorMoments_le244
      h Gh hh Kh hKh hbh).1
  have hD : D ≤ 3 * h3SobolevDeweightingConstant * Kw :=
    (thirdFullKineticWeightedSchwartz_vectorMoments_le244
      w Gw hw Kw hKw hbw).2
  have hA0 : 0 ≤ A := integral_nonneg (fun ξ => sq_nonneg _)
  have hB0 : 0 ≤ B := integral_nonneg (fun ξ => sq_nonneg _)
  have hD0 : 0 ≤ D := integral_nonneg
    (fun ξ => thirdFullKineticPolarAmplitude_nonneg244 Q ξ)
  have hOuter :
      (scale ^ 2 * A + scale⁻¹ ^ 2 * B) / 2 ≤
      (scale ^ 2 * (3 * Kv ^ 2) +
        scale⁻¹ ^ 2 * (3 * Kh ^ 2)) / 2 := by
    have hFirst := mul_le_mul_of_nonneg_left hA (sq_nonneg scale)
    have hLast := mul_le_mul_of_nonneg_left hB (sq_nonneg scale⁻¹)
    linarith only [hFirst, hLast]
  have hOuter0 : 0 ≤ (scale ^ 2 * (3 * Kv ^ 2) +
      scale⁻¹ ^ 2 * (3 * Kh ^ 2)) / 2 := by positivity
  have hProduct :
      ((scale ^ 2 * A + scale⁻¹ ^ 2 * B) / 2) * D ≤
      ((scale ^ 2 * (3 * Kv ^ 2) +
        scale⁻¹ ^ 2 * (3 * Kh ^ 2)) / 2) *
        (3 * h3SobolevDeweightingConstant * Kw) :=
    mul_le_mul hOuter hD hD0 hOuter0
  have hCoeff : 0 ≤ 9 * ρ ^ 7 := by
    dsimp only [ρ]
    positivity
  have hYoung := thirdFullKinetic_lowMax_mixedFlux_le_scaledL2L2L1244
    R P Q W hFlux hBudget hPInt hWInt hQInt scale hscale
  change (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      ‖thirdFullKineticMixedPolarSixthFlux244 P Q W z‖
        ∂volume.prod volume) ≤
      (9 * ρ ^ 7) *
        (((scale ^ 2 * (3 * Kv ^ 2) +
          scale⁻¹ ^ 2 * (3 * Kh ^ 2)) / 2) *
          (3 * h3SobolevDeweightingConstant * Kw))
  calc
    _ ≤ (9 * ρ ^ 7) *
      (((scale ^ 2 * A + scale⁻¹ ^ 2 * B) / 2) * D) := hYoung
    _ ≤ _ := mul_le_mul_of_nonneg_left hProduct hCoeff


/-- The same three-input bound stated only with the genuine physical H3
finite-vector spectral state norms. All independent coordinate ceilings have
been discharged by the finite-vector coordinate norm lemma. -/
theorem thirdFullKinetic_lowMax_mixedSchwartzFlux_le_spectralVelocities244
    (R : ℕ)
    (v w h : WA3 → SchwartzMap WV3 ℂ)
    (V W H : H3SpectralVelocityState)
    (hv : ∀ j : WA3,
      (V (h3ClassicalizationFinOfAxis j) : WV3 → ℂ) =ᵐ[volume]
        (fun ξ : WV3 =>
          (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (v j)) ξ))
    (hw : ∀ j : WA3,
      (W (h3ClassicalizationFinOfAxis j) : WV3 → ℂ) =ᵐ[volume]
        (fun ξ : WV3 =>
          (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (w j)) ξ))
    (hh : ∀ j : WA3,
      (H (h3ClassicalizationFinOfAxis j) : WV3 → ℂ) =ᵐ[volume]
        (fun ξ : WV3 =>
          (h3SobolevFrequencyWeight ξ : ℂ) * (𝓕 (h j)) ξ))
    (hFlux : IntegrableOn
      (thirdFullKineticMixedPolarSixthFlux244
        (thirdFullKineticSchwartzPolarization244 v)
        (thirdFullKineticSchwartzPolarization244 w)
        (thirdFullKineticSchwartzPolarization244 h))
      (thirdFullHighMaxSet244 R)ᶜ (volume.prod volume))
    (hBudget : Integrable
      (thirdFullKineticMixedPolarSixthBudget244
        (thirdFullKineticSchwartzPolarization244 v)
        (thirdFullKineticSchwartzPolarization244 w)
        (thirdFullKineticSchwartzPolarization244 h))
      (volume.prod volume))
    (scale : ℝ) (hscale : 0 < scale) :
    (∫ z in (thirdFullHighMaxSet244 R)ᶜ,
      ‖thirdFullKineticMixedPolarSixthFlux244
        (thirdFullKineticSchwartzPolarization244 v)
        (thirdFullKineticSchwartzPolarization244 w)
        (thirdFullKineticSchwartzPolarization244 h) z‖
        ∂volume.prod volume) ≤
    (9 * (2 * ((R : ℝ) + 1)) ^ 7) *
      (((scale ^ 2 * (3 * ‖V‖ ^ 2) +
        scale⁻¹ ^ 2 * (3 * ‖H‖ ^ 2)) / 2) *
        (3 * h3SobolevDeweightingConstant * ‖W‖)) := by
  let Gv : WA3 → H3SpectralScalarState :=
    fun j => V (h3ClassicalizationFinOfAxis j)
  let Gw : WA3 → H3SpectralScalarState :=
    fun j => W (h3ClassicalizationFinOfAxis j)
  let Gh : WA3 → H3SpectralScalarState :=
    fun j => H (h3ClassicalizationFinOfAxis j)
  have hBoundV (j : WA3) : ‖Gv j‖ ≤ ‖V‖ :=
    h3SpectralFinVector_coordinate_norm_le V (h3ClassicalizationFinOfAxis j)
  have hBoundW (j : WA3) : ‖Gw j‖ ≤ ‖W‖ :=
    h3SpectralFinVector_coordinate_norm_le W (h3ClassicalizationFinOfAxis j)
  have hBoundH (j : WA3) : ‖Gh j‖ ≤ ‖H‖ :=
    h3SpectralFinVector_coordinate_norm_le H (h3ClassicalizationFinOfAxis j)
  exact thirdFullKinetic_lowMax_mixedSchwartzFlux_le_weightedH3_244
    R v w h Gv Gw Gh hv hw hh
    ‖V‖ ‖W‖ ‖H‖ (norm_nonneg V) (norm_nonneg W) (norm_nonneg H)
    hBoundV hBoundW hBoundH hFlux hBudget scale hscale

end
end PrimeTensor.FirstMonomialTriad
