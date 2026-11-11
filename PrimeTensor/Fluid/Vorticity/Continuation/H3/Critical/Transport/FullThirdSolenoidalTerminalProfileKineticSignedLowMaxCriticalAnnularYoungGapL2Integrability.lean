import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularYoungGapLocalization
import Mathlib.Tactic

/-!
# Intrinsic L² integrability of the actual bounded-band critical Young gap

The accepted annular integral theorem has three explicit fixed-time
IntegrableOn premises. Here they are discharged from the already constructed
strict-time Fourier L² states. In particular, the *actual* Young residual
N+2qz is the L² representative N-2L, with L=-qz the physical spectral
Laplacian. This requires no separate sixth-frequency velocity moment.

A bounded-frequency multiplier q³ preserves local square integrability.
The integrated theorem consequently needs only the actual strict-time H³
path and the measurable, bounded q-band assumptions. This does not supply
a terminal-uniform q-bound: the bound grows like max(hi,0)^3 and the
rate-width penalty remains visible.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeAnnularYoungL2Integrability244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceAnnularYoungL2Integrability244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- On any measurable bounded q-band, the cubic frequency weight preserves
square integrability of an arbitrary Fourier L² state. The maximum handles
vacuous empty bands whose supplied upper cutoff may be negative. -/
theorem thirdFullKinetic_bandWeightedFourierSquare_integrableOn244
    (F : H3FourierComplexL2) (S : Set H3FourierPoint3)
    (hS : MeasurableSet S) (hi : ℝ)
    (hUpper : ∀ ξ ∈ S, h3FourierGradientSquare ξ ≤ hi) :
    IntegrableOn (fun ξ : H3FourierPoint3 =>
      h3FourierGradientSquare ξ ^ 3 * ‖(F : H3FourierPoint3 → ℂ) ξ‖ ^ 2)
      S volume := by
  let M : ℝ := max hi 0
  have hM : 0 ≤ M := le_max_right hi 0
  have hFull : Integrable (fun ξ : H3FourierPoint3 => ‖F ξ‖ ^ 2)
      (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp F).integrable_norm_pow (by norm_num)
  have hMajor : IntegrableOn (fun ξ : H3FourierPoint3 =>
      M ^ 3 * ‖F ξ‖ ^ 2) S volume :=
    hFull.integrableOn.const_mul _
  have hQMeas : Measurable
      (fun ξ : H3FourierPoint3 => h3FourierGradientSquare ξ) := by
    unfold h3FourierGradientSquare
    measurability
  have hMeas : AEStronglyMeasurable
      (fun ξ : H3FourierPoint3 =>
        h3FourierGradientSquare ξ ^ 3 * ‖F ξ‖ ^ 2)
      ((volume : Measure H3FourierPoint3).restrict S) := by
    exact ((hQMeas.aestronglyMeasurable.pow 3).mul
      ((MeasureTheory.Lp.aestronglyMeasurable F).norm.pow 2)).restrict
  refine Integrable.mono' hMajor hMeas ?_
  filter_upwards [ae_restrict_mem hS] with ξ hξ
  have hq : 0 ≤ h3FourierGradientSquare ξ :=
    h3FourierGradientSquare_nonneg ξ
  have hqM : h3FourierGradientSquare ξ ≤ M :=
    (hUpper ξ hξ).trans (le_max_left hi 0)
  have hPow : h3FourierGradientSquare ξ ^ 3 ≤ M ^ 3 :=
    pow_le_pow_left₀ hq hqM 3
  have hNonneg : 0 ≤
      h3FourierGradientSquare ξ ^ 3 * ‖F ξ‖ ^ 2 :=
    mul_nonneg (pow_nonneg hq 3) (sq_nonneg _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hNonneg] using
    (mul_le_mul_of_nonneg_right hPow (sq_nonneg (‖F ξ‖)))

/-- Quantitative cubic multiplier cost on the same band. No hidden
frequency-uniform bound is introduced. -/
theorem thirdFullKinetic_bandWeightedFourierSquare_bound244
    (F : H3FourierComplexL2) (S : Set H3FourierPoint3)
    (hS : MeasurableSet S) (hi : ℝ)
    (hUpper : ∀ ξ ∈ S, h3FourierGradientSquare ξ ≤ hi) :
    (∫ ξ in S,
      h3FourierGradientSquare ξ ^ 3 * ‖(F : H3FourierPoint3 → ℂ) ξ‖ ^ 2
        ∂volume) ≤
      (max hi 0) ^ 3 * (∫ ξ in S, ‖(F : H3FourierPoint3 → ℂ) ξ‖ ^ 2
        ∂volume) := by
  let M : ℝ := max hi 0
  have hM : 0 ≤ M := le_max_right hi 0
  have hLeft := thirdFullKinetic_bandWeightedFourierSquare_integrableOn244
    F S hS hi hUpper
  have hRight : IntegrableOn (fun ξ : H3FourierPoint3 =>
      M ^ 3 * ‖F ξ‖ ^ 2) S volume :=
    ((MeasureTheory.Lp.memLp F).integrable_norm_pow
      (by norm_num)).integrableOn.const_mul _
  have hDom : ∀ᵐ ξ ∂((volume : Measure H3FourierPoint3).restrict S),
      h3FourierGradientSquare ξ ^ 3 * ‖F ξ‖ ^ 2 ≤
        M ^ 3 * ‖F ξ‖ ^ 2 := by
    filter_upwards [ae_restrict_mem hS] with ξ hξ
    have hq : 0 ≤ h3FourierGradientSquare ξ :=
      h3FourierGradientSquare_nonneg ξ
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hq
        ((hUpper ξ hξ).trans (le_max_left hi 0)) 3)
      (sq_nonneg _)
  have hIntegral := integral_mono_ae hLeft hRight hDom
  rw [integral_const_mul] at hIntegral
  exact hIntegral

/-- The actual projected momentum/velocity constant-rate residual is
square-integrable on every measurable Fourier band, without a q-moment. -/
theorem thirdFullPhysical_actualAnnularError_integrableOn244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (j : Fin 3) (lo hi : ℝ)
    (S : Set H3FourierPoint3) :
    IntegrableOn (fun ξ : H3FourierPoint3 =>
      ‖(h3CriticalActualProjectedFourierSource hH3 j t :
          H3FourierPoint3 → ℂ) ξ -
        (((lo + hi) / 2 : ℝ) : ℂ) *
          h3SpectralScalarRawFourierL2
            ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ‖ ^ 2)
      S volume := by
  let R : H3FourierComplexL2 :=
    h3CriticalActualProjectedFourierSource hH3 j t
  let Z : H3FourierComplexL2 :=
    h3SpectralScalarRawFourierL2
      ((h3AuditActualSpectralVelocityTotal hH3 t) j)
  let rate : ℂ := ((lo + hi) / 2 : ℝ)
  let E : H3FourierComplexL2 := R - rate • Z
  have hBase : IntegrableOn (fun ξ : H3FourierPoint3 => ‖E ξ‖ ^ 2)
      S volume :=
    ((MeasureTheory.Lp.memLp E).integrable_norm_pow (by norm_num)).integrableOn
  have hAE : (fun ξ : H3FourierPoint3 => ‖E ξ‖ ^ 2)
      =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => ‖R ξ - rate * Z ξ‖ ^ 2) := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub R (rate • Z),
      MeasureTheory.Lp.coeFn_smul rate Z] with ξ hSub hSmul
    rw [hSub]
    simp only [Pi.sub_apply]
    rw [hSmul]
    simp only [Pi.smul_apply, smul_eq_mul]
  change IntegrableOn
    (fun ξ : H3FourierPoint3 => ‖R ξ - rate * Z ξ‖ ^ 2) S volume
  exact hBase.congr (ae_restrict_of_ae (s := S) hAE)

/-- The actual Fourier Young residual is the L² field N-2L, where N is
the genuine Leray convolution forcing and L=-qz is the spectral Laplacian.
Therefore its q³-weighted square is integrable on any bounded q-band. -/
theorem thirdFullPhysical_actualAnnularGap_integrableOn244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (j : Fin 3) (hi : ℝ)
    (S : Set H3FourierPoint3) (hS : MeasurableSet S)
    (hUpper : ∀ ξ ∈ S, h3FourierGradientSquare ξ ≤ hi) :
    IntegrableOn (fun ξ : H3FourierPoint3 =>
      h3FourierGradientSquare ξ ^ 3 *
        ‖h3RawFinLerayOuterProductDivergence
          (h3AuditActualSpectralVelocityTotal hH3 t)
          (h3AuditActualSpectralVelocityTotal hH3 t) j ξ +
          2 * ((h3FourierGradientSquare ξ : ℂ) *
            h3SpectralScalarRawFourierL2
              ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ)‖ ^ 2)
      S volume := by
  let U : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 t
  let L : H3FourierComplexL2 :=
    h3SpectralScalarLaplacianRawFourierL2 (U j)
  let N : H3FourierComplexL2 :=
    h3RawFinLerayOuterProductDivergenceFourierL2 U U j
  let G : H3FourierComplexL2 := N - (2 : ℂ) • L
  have hBase := thirdFullKinetic_bandWeightedFourierSquare_integrableOn244
    G S hS hi hUpper
  have hLap : (L : H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ => -(h3FourierGradientSquare ξ : ℂ) *
        h3SpectralScalarRawFourierL2 (U j) ξ) := by
    dsimp only [L]
    exact h3SpectralScalarLaplacianRawFourierL2_ae_eq_gradientSquare_mul_raw (U j)
  have hN : (N : H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ => h3RawFinLerayOuterProductDivergence U U j ξ) := by
    dsimp only [N]
    unfold h3RawFinLerayOuterProductDivergenceFourierL2
    exact MeasureTheory.MemLp.coeFn_toLp
      (h3RawFinLerayOuterProductDivergence_memLp2 U U j)
  have hG : (G : H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ => h3RawFinLerayOuterProductDivergence U U j ξ +
        2 * ((h3FourierGradientSquare ξ : ℂ) *
          h3SpectralScalarRawFourierL2 (U j) ξ)) := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub N ((2 : ℂ) • L),
      MeasureTheory.Lp.coeFn_smul (2 : ℂ) L,
      hLap, hN] with ξ hSub hSmul hLapξ hNξ
    rw [hSub]
    simp only [Pi.sub_apply]
    rw [hSmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hLapξ, hNξ]
    ring
  have hAE : (fun ξ : H3FourierPoint3 =>
      h3FourierGradientSquare ξ ^ 3 * ‖G ξ‖ ^ 2)
      =ᵐ[((volume : Measure H3FourierPoint3).restrict S)]
      (fun ξ => h3FourierGradientSquare ξ ^ 3 *
        ‖h3RawFinLerayOuterProductDivergence U U j ξ +
          2 * ((h3FourierGradientSquare ξ : ℂ) *
            h3SpectralScalarRawFourierL2 (U j) ξ)‖ ^ 2) := by
    filter_upwards [ae_restrict_of_ae (s := S) hG] with ξ hξ
    rw [hξ]
  change IntegrableOn
    (fun ξ : H3FourierPoint3 => h3FourierGradientSquare ξ ^ 3 *
      ‖h3RawFinLerayOuterProductDivergence U U j ξ +
        2 * ((h3FourierGradientSquare ξ : ℂ) *
          h3SpectralScalarRawFourierL2 (U j) ξ)‖ ^ 2) S volume
  exact hBase.congr hAE

/-- The genuine raw velocity Fourier L² representative has integrable
square mass on any set; no band bound is required for this one. -/
theorem thirdFullPhysical_actualAnnularMass_integrableOn244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (j : Fin 3) (S : Set H3FourierPoint3) :
    IntegrableOn (fun ξ : H3FourierPoint3 =>
      ‖h3SpectralScalarRawFourierL2
        ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ‖ ^ 2)
      S volume := by
  exact ((MeasureTheory.Lp.memLp
    (h3SpectralScalarRawFourierL2
      ((h3AuditActualSpectralVelocityTotal hH3 t) j))).integrable_norm_pow
      (by norm_num)).integrableOn

/-- All three former fixed-band integrability premises are derived from
the actual Fourier L² states and the bounded multiplier, not postulated.
This result says nothing about control as the outer cutoff hi diverges. -/
theorem thirdFullPhysical_actualAnnularYoungGap_integral_auto244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ} (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (j : Fin 3) (lo hi : ℝ) (hLo : 0 ≤ lo)
    (S : Set H3FourierPoint3) (hS : MeasurableSet S)
    (hBand : ∀ ξ ∈ S,
      lo ≤ h3FourierGradientSquare ξ ∧ h3FourierGradientSquare ξ ≤ hi)
    : lo ^ 3 * (∫ ξ in S,
      ‖(h3CriticalActualProjectedFourierSource hH3 j t :
          H3FourierPoint3 → ℂ) ξ -
        (((lo + hi) / 2 : ℝ) : ℂ) *
          h3SpectralScalarRawFourierL2
            ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ‖ ^ 2 ∂volume) ≤
    2 * (∫ ξ in S,
      h3FourierGradientSquare ξ ^ 3 *
        ‖h3RawFinLerayOuterProductDivergence
          (h3AuditActualSpectralVelocityTotal hH3 t)
          (h3AuditActualSpectralVelocityTotal hH3 t) j ξ +
          2 * ((h3FourierGradientSquare ξ : ℂ) *
            h3SpectralScalarRawFourierL2
              ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ)‖ ^ 2 ∂volume) +
    (2 * hi ^ 3 * ((hi - lo) / 2) ^ 2) *
      (∫ ξ in S,
        ‖h3SpectralScalarRawFourierL2
          ((h3AuditActualSpectralVelocityTotal hH3 t) j) ξ‖ ^ 2 ∂volume) := by
  have hError := thirdFullPhysical_actualAnnularError_integrableOn244
    hH3 t j lo hi S
  have hGap := thirdFullPhysical_actualAnnularGap_integrableOn244
    hH3 t j hi S hS (fun ξ hξ => (hBand ξ hξ).2)
  have hMass := thirdFullPhysical_actualAnnularMass_integrableOn244
    hH3 t j S
  exact thirdFullPhysical_actualAnnularYoungGap_integral244
    hH3 t ht j lo hi hLo S hS hBand hError hGap hMass

end
end PrimeTensor.FirstMonomialTriad
