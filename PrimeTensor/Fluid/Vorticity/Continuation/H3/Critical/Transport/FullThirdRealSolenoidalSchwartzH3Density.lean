import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdRegularizedPhysicalLerayWeightedL2Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Compact.Deweighting
import Mathlib.Tactic

/-!
# Real solenoidal Schwartz density in the actual weighted H³ state

The compact Hermitian approximants are initially smooth in the weighted
Hilbert Fourier carrier. The exact reciprocal H³ weight, pulled back through
the canonical PiLp coordinate equivalence, produces smooth compact raw-axis
profiles with pointwise Hermitian reflection. The previously established
physical Leray L² bridge then identifies the Fourier transforms of genuinely
real, divergence-free Schwartz fields with the regularized projected states.

The final theorem has no free profile, smoothness, cutoff, approximation, or
representative hypothesis: only the target's Fourier incompressibility and
real-data Hermitian reality remain. All Fourier representative equalities are
stated almost everywhere, while physical divergence vanishes pointwise.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Filter Topology Set PrimeTensor.Bridge.Euclidean
open scoped ENNReal BigOperators ContDiff SchwartzMap FourierTransform ComplexConjugate

noncomputable section
set_option maxHeartbeats 1800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3
private abbrev Freq244 := A3 → ℝ
private abbrev CPol244 := A3 → ℂ

noncomputable local instance axisFintypeRealPhysicalH3Density244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Build the raw Fourier polarization from a *weighted* compact spectral
Schwartz vector on the exact three-axis carrier. No Leray projection is used
in this definition. -/
noncomputable def thirdFullDeweightedCompactAxisProfile244
    (Φ : Fin 3 → SchwartzMap V3 ℂ) (η : Freq244) (a : A3) : ℂ :=
  h3SobolevFrequencyWeightInvComplex
    ((WithLp.toLp 2 : Freq244 → V3) η) *
    Φ (h3ClassicalizationFinOfAxis a)
      ((WithLp.toLp 2 : Freq244 → V3) η)

/-- Transporting the exact reciprocal weight through the PiLp equivalence
preserves smoothness componentwise, hence for the entire polarization. -/
theorem thirdFullDeweightedCompactAxisProfile_contDiff244
    (Φ : Fin 3 → SchwartzMap V3 ℂ) :
    ContDiff ℝ ∞ (thirdFullDeweightedCompactAxisProfile244 Φ) := by
  have hToLp : ContDiff ℝ ∞
      (WithLp.toLp 2 : Freq244 → V3) := PiLp.contDiff_toLp
  have hWeight : ContDiff ℝ ∞
      (fun η : Freq244 => h3SobolevFrequencyWeightInvComplex
        ((WithLp.toLp 2 : Freq244 → V3) η)) :=
    contDiff_h3SobolevFrequencyWeightInvComplex.comp hToLp
  apply contDiff_pi'
  intro a
  have hComponent : ContDiff ℝ ∞
      (fun η : Freq244 =>
        Φ (h3ClassicalizationFinOfAxis a)
          ((WithLp.toLp 2 : Freq244 → V3) η)) :=
    ((Φ (h3ClassicalizationFinOfAxis a)).smooth (⊤ : ℕ∞)).comp hToLp
  change ContDiff ℝ ∞ (fun η : Freq244 =>
    h3SobolevFrequencyWeightInvComplex
      ((WithLp.toLp 2 : Freq244 → V3) η) *
    Φ (h3ClassicalizationFinOfAxis a)
      ((WithLp.toLp 2 : Freq244 → V3) η))
  exact hWeight.mul hComponent

/-- For a finite three-component output, compact support of each component
implies compact support of the whole vector-valued function. -/
private theorem thirdFullCompactSupport_fin3_vector244
    (f : Freq244 → (Fin 3 → ℂ))
    (hf : ∀ j : Fin 3, HasCompactSupport (fun η => f η j)) :
    HasCompactSupport f := by
  let K : Set Freq244 :=
    tsupport (fun η => f η (0 : Fin 3)) ∪
      (tsupport (fun η => f η (1 : Fin 3)) ∪
        tsupport (fun η => f η (2 : Fin 3)))
  have hK : IsCompact K :=
    (hf 0).isCompact.union ((hf 1).isCompact.union (hf 2).isCompact)
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro η hη
  have hNonzero : ∃ j : Fin 3, f η j ≠ 0 := by
    by_contra hNo
    apply hη
    funext j
    by_contra hj
    exact hNo ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hNonzero
  fin_cases j
  · exact Or.inl (subset_tsupport _ hj)
  · exact Or.inr (Or.inl (subset_tsupport _ hj))
  · exact Or.inr (Or.inr (subset_tsupport _ hj))

/-- The deweighted axis profile has compact support when each input weighted
Schwartz component has compact Fourier support. -/
theorem thirdFullDeweightedCompactAxisProfile_hasCompactSupport244
    (Φ : Fin 3 → SchwartzMap V3 ℂ)
    (hΦ : ∀ j : Fin 3, HasCompactSupport (Φ j : V3 → ℂ)) :
    HasCompactSupport (thirdFullDeweightedCompactAxisProfile244 Φ) := by
  let f : Freq244 → (Fin 3 → ℂ) := fun η j =>
    thirdFullDeweightedCompactAxisProfile244 Φ η (h3AxisOfFin3 j)
  have hf (j : Fin 3) : HasCompactSupport (fun η : Freq244 => f η j) := by
    have hPulled : HasCompactSupport
        (fun η : Freq244 =>
          Φ j ((WithLp.toLp 2 : Freq244 → V3) η)) := by
      let e : Freq244 ≃ₜ V3 :=
        (PiLp.continuousLinearEquiv 2 ℝ
          (fun _ : A3 => ℝ)).symm.toHomeomorph
      have he : ∀ η : Freq244,
          e η = (WithLp.toLp 2 : Freq244 → V3) η := by
        intro η
        ext a
        rfl
      have hPulledE : HasCompactSupport (fun η : Freq244 => Φ j (e η)) :=
        (hΦ j).comp_homeomorph e
      have hFunctions :
          (fun η : Freq244 => Φ j (e η)) =
          (fun η : Freq244 => Φ j ((WithLp.toLp 2 : Freq244 → V3) η)) := by
        funext η
        rw [he η]
      rw [← hFunctions]
      exact hPulledE
    have hMul : HasCompactSupport (fun η : Freq244 =>
        h3SobolevFrequencyWeightInvComplex
          ((WithLp.toLp 2 : Freq244 → V3) η) *
        Φ j ((WithLp.toLp 2 : Freq244 → V3) η)) :=
      hPulled.mul_left
    simpa only [f, thirdFullDeweightedCompactAxisProfile244,
      h3ClassicalizationFinOfAxis_h3AxisOfFin3] using hMul
  have hfCompact : HasCompactSupport f :=
    thirdFullCompactSupport_fin3_vector244 f hf
  have hMapped : HasCompactSupport
      (fun η : Freq244 => fun a : A3 =>
        f η (h3ClassicalizationFinOfAxis a)) :=
    hfCompact.comp_left
      (g := fun z : Fin 3 → ℂ =>
        fun a : A3 => z (h3ClassicalizationFinOfAxis a))
      (by funext a; simp)
  have hEq :
      (fun η : Freq244 => fun a : A3 =>
        f η (h3ClassicalizationFinOfAxis a)) =
      thirdFullDeweightedCompactAxisProfile244 Φ := by
    funext η a
    simp only [f, thirdFullDeweightedCompactAxisProfile244,
      h3AxisOfFin3_h3ClassicalizationFinOfAxis]
  simpa only [hEq] using hMapped

/-- The reciprocal H³ weight is even, and so does not disturb the Fourier
Hermitian involution when applied to pointwise Hermitian input Schwartz data. -/
theorem thirdFullDeweightedCompactAxisProfile_hermitian244
    (Φ : Fin 3 → SchwartzMap V3 ℂ)
    (hΦ : ∀ (j : Fin 3) (ξ : V3),
      Φ j (-ξ) = conj (Φ j ξ)) :
    H3ComplexHermitianPolarizationProfile244
      (thirdFullDeweightedCompactAxisProfile244 Φ) := by
  intro η
  funext a
  have hNeg :
      (WithLp.toLp 2 : Freq244 → V3) (fun j => -η j) =
      -((WithLp.toLp 2 : Freq244 → V3) η) := by
    ext j
    rfl
  have hInvEven (ξ : V3) :
      h3SobolevFrequencyWeightInvComplex (-ξ) =
      h3SobolevFrequencyWeightInvComplex ξ := by
    simp only [h3SobolevFrequencyWeightInvComplex,
      h3SobolevFrequencyWeightInv, h3SobolevFrequencyWeight_neg]
  have hInvReal (ξ : V3) :
      conj (h3SobolevFrequencyWeightInvComplex ξ) =
      h3SobolevFrequencyWeightInvComplex ξ := by
    simpa only [h3SobolevFrequencyWeightInvComplex] using
      (Complex.conj_ofReal (h3SobolevFrequencyWeightInv ξ))
  change
    h3SobolevFrequencyWeightInvComplex
      ((WithLp.toLp 2 : Freq244 → V3) (fun j => -η j)) *
      Φ (h3ClassicalizationFinOfAxis a)
        ((WithLp.toLp 2 : Freq244 → V3) (fun j => -η j)) =
    conj (h3SobolevFrequencyWeightInvComplex
      ((WithLp.toLp 2 : Freq244 → V3) η) *
      Φ (h3ClassicalizationFinOfAxis a)
        ((WithLp.toLp 2 : Freq244 → V3) η))
  rw [hNeg, hInvEven,
    hΦ (h3ClassicalizationFinOfAxis a), map_mul, hInvReal]

/-- The weight-deweight cancellation is *pointwise*, and the bundled input
Schwartz class has the required a.e. representative in each Fin coordinate. -/
theorem thirdFullDeweightedCompactAxisProfile_weighted_ae244
    (Φ : Fin 3 → SchwartzMap V3 ℂ) (i : Fin 3) :
    (h3SchwartzSpectralVelocityRealization244 Φ i : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
        thirdFullDeweightedCompactAxisProfile244 Φ
          (WithLp.ofLp ξ) (h3AxisOfFin3 i)) := by
  have hRep := (Φ i).coeFn_toLp 2 (volume : Measure V3)
  filter_upwards [hRep] with ξ hAt
  have hAt' :
      (h3SchwartzSpectralVelocityRealization244 Φ i : V3 → ℂ) ξ =
      Φ i ξ := hAt
  rw [hAt']
  have hCancel :
      (h3SobolevFrequencyWeight ξ : ℂ) *
        (h3SobolevFrequencyWeightInvComplex ξ * Φ i ξ) = Φ i ξ := by
    rw [← mul_assoc, h3SobolevFrequencyWeight_mul_invComplex, one_mul]
  simpa [thirdFullDeweightedCompactAxisProfile244,
    h3ClassicalizationFinOfAxis_h3AxisOfFin3] using hCancel.symm

/-- Compact Hermitian weighted spectral Schwartz vectors may be chosen with
pointwise (not only a.e.) conjugate-reflection reality. -/
theorem exists_thirdFullPointwiseHermitianCompactVelocityApprox244
    (target : H3SpectralVelocityState)
    (hReal : H3SpectralVelocityRawHermitian target)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Φ : Fin 3 → SchwartzMap V3 ℂ,
      (∀ j, HasCompactSupport (Φ j : V3 → ℂ)) ∧
      (∀ j ξ, Φ j (-ξ) = conj (Φ j ξ)) ∧
      ‖target - h3SchwartzSpectralVelocityRealization244 Φ‖ < ε := by
  have hHerm := h3SpectralVelocityRawHermitian_to_hermitian hReal
  have hSmall : 0 < ε / 2 := by positivity
  have hApprox (j : Fin 3) :
      ∃ S : SchwartzMap V3 ℂ,
        HasCompactSupport (S : V3 → ℂ) ∧
        (∀ ξ, S (-ξ) = conj (S ξ)) ∧
        ‖target j - S.toLp 2 (volume : Measure V3)‖ < ε / 2 :=
    exists_h3HermitianSmoothCompactSpectralApprox244
      (target j) (hHerm j) hSmall
  choose Φ hCompact hReality hError using hApprox
  refine ⟨Φ, hCompact, hReality, ?_⟩
  have hBound : ‖target - h3SchwartzSpectralVelocityRealization244 Φ‖ ≤
      ε / 2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro j
    simpa only [Pi.sub_apply, h3SchwartzSpectralVelocityRealization_apply244]
      using le_of_lt (hError j)
  linarith

/-- A constructive moving sequence of compact, pointwise Hermitian weighted
Schwartz vectors converging to every real-data spectral velocity target. -/
theorem exists_thirdFullPointwiseHermitianCompactVelocitySequence244
    (target : H3SpectralVelocityState)
    (hReal : H3SpectralVelocityRawHermitian target) :
    ∃ Φ : ℕ → Fin 3 → SchwartzMap V3 ℂ,
      (∀ n j, HasCompactSupport (Φ n j : V3 → ℂ)) ∧
      (∀ n j ξ, Φ n j (-ξ) = conj (Φ n j ξ)) ∧
      Tendsto (fun n => h3SchwartzSpectralVelocityRealization244 (Φ n))
        atTop (𝓝 target) := by
  classical
  have hPos (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hChoose (n : ℕ) :
      ∃ Φ : Fin 3 → SchwartzMap V3 ℂ,
        (∀ j, HasCompactSupport (Φ j : V3 → ℂ)) ∧
        (∀ j ξ, Φ j (-ξ) = conj (Φ j ξ)) ∧
        ‖target - h3SchwartzSpectralVelocityRealization244 Φ‖ <
          (1 : ℝ) / ((n : ℝ) + 1) :=
    exists_thirdFullPointwiseHermitianCompactVelocityApprox244
      target hReal (hPos n)
  choose Φ hCompact hReality hClose using hChoose
  have hRadius : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hConverges : Tendsto
      (fun n => h3SchwartzSpectralVelocityRealization244 (Φ n))
      atTop (𝓝 target) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hRadius) ε hε
    refine ⟨N, ?_⟩
    intro n hn
    have hSmall : (1 : ℝ) / ((n : ℝ) + 1) < ε := by
      have h := hN n hn
      simpa only [Real.dist_eq, sub_zero,
        abs_of_pos (hPos n)] using h
    calc
      dist (h3SchwartzSpectralVelocityRealization244 (Φ n)) target =
          ‖target - h3SchwartzSpectralVelocityRealization244 (Φ n)‖ := by
            rw [dist_eq_norm, norm_sub_rev]
      _ < (1 : ℝ) / ((n : ℝ) + 1) := hClose n
      _ < ε := hSmall
  exact ⟨Φ, hCompact, hReality, hConverges⟩

/-- Density by actual real, physically solenoidal Schwartz velocities in the
canonical weighted H³ spectral state. Every representative equality is a.e.;
physical divergence is exactly zero at every spatial point. -/
theorem exists_thirdFullRealSolenoidalPhysicalSchwartzH3Density244
    (target : H3SpectralVelocityState)
    (hDiv : H3SpectralFinDivergenceFree target)
    (hReal : H3SpectralVelocityRawHermitian target) :
    ∃ Φ : ℕ → Fin 3 → SchwartzMap V3 ℂ,
    ∃ χ : ℕ → Freq244 → ℝ,
    ∃ (hχsmooth : ∀ n, ContDiff ℝ ∞ (χ n)),
    ∃ (hχcompact : ∀ n, HasCompactSupport (χ n)),
      Tendsto (fun n => h3FullThirdRadialRecoveryVelocity244 n
          (h3SpectralFinLerayApply
            (h3SchwartzSpectralVelocityRealization244 (Φ n))))
        atTop (𝓝 target) ∧
      (∀ (n : ℕ) (i : Fin 3),
        (h3FullThirdRadialRecoveryVelocity244 n
          (h3SpectralFinLerayApply
            (h3SchwartzSpectralVelocityRealization244 (Φ n))) i : V3 → ℂ)
          =ᵐ[volume]
          (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
            𝓕 (h3SchwartzComplexify
              (thirdFullRegularizedPhysicalSchwartzAt244 n (χ n)
                (thirdFullDeweightedCompactAxisProfile244 (Φ n))
                (hχsmooth n) (hχcompact n)
                (thirdFullDeweightedCompactAxisProfile_contDiff244 (Φ n))
                (h3AxisOfFin3 i))) ξ)) ∧
      (∀ (n : ℕ) (x : V3), ∑ j : A3,
        fderiv ℝ (h3SchwartzComplexify
          (thirdFullRegularizedPhysicalSchwartzAt244 n (χ n)
            (thirdFullDeweightedCompactAxisProfile244 (Φ n))
            (hχsmooth n) (hχcompact n)
            (thirdFullDeweightedCompactAxisProfile_contDiff244 (Φ n)) j))
          x (h3FourierAxisDirection j) = 0) ∧
      Tendsto (fun n => h3SpectralVelocityDecodeRealL2
        (h3FullThirdRadialRecoveryVelocity244 n
          (h3SpectralFinLerayApply
            (h3SchwartzSpectralVelocityRealization244 (Φ n)))))
        atTop (𝓝 (h3SpectralVelocityDecodeRealL2 target)) ∧
      CauchySeq (fun n => h3FullThirdRadialRecoveryVelocity244 n
        (h3SpectralFinLerayApply
          (h3SchwartzSpectralVelocityRealization244 (Φ n)))) := by
  obtain ⟨Φ, hCompact, hHerm, hConv⟩ :=
    exists_thirdFullPointwiseHermitianCompactVelocitySequence244
      target hReal
  have hUcompact (n : ℕ) : HasCompactSupport
      (thirdFullDeweightedCompactAxisProfile244 (Φ n)) :=
    thirdFullDeweightedCompactAxisProfile_hasCompactSupport244
      (Φ n) (hCompact n)
  have hUsmooth (n : ℕ) : ContDiff ℝ ∞
      (thirdFullDeweightedCompactAxisProfile244 (Φ n)) :=
    thirdFullDeweightedCompactAxisProfile_contDiff244 (Φ n)
  have hUherm (n : ℕ) : H3ComplexHermitianPolarizationProfile244
      (thirdFullDeweightedCompactAxisProfile244 (Φ n)) :=
    thirdFullDeweightedCompactAxisProfile_hermitian244 (Φ n) (hHerm n)
  have hGweighted (n : ℕ) (j : Fin 3) :
      (h3SchwartzSpectralVelocityRealization244 (Φ n) j : V3 → ℂ)
        =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
        thirdFullDeweightedCompactAxisProfile244 (Φ n)
          (WithLp.ofLp ξ) (h3AxisOfFin3 j)) :=
    thirdFullDeweightedCompactAxisProfile_weighted_ae244 (Φ n) j
  obtain ⟨χ, hχsmooth, hχcompact, hLimit, hFourier, hPhysical,
      hDecode, hCauchy⟩ :=
    exists_thirdFullPhysicalSchwartzMoving_lerayWeighted_completion244
      target hDiv
      (fun n => h3SchwartzSpectralVelocityRealization244 (Φ n))
      hConv
      (fun n => thirdFullDeweightedCompactAxisProfile244 (Φ n))
      hUcompact hUsmooth hUherm hGweighted
  exact ⟨Φ, χ, hχsmooth, hχcompact,
    hLimit, hFourier, hPhysical, hDecode, hCauchy⟩

end
end PrimeTensor.FirstMonomialTriad
