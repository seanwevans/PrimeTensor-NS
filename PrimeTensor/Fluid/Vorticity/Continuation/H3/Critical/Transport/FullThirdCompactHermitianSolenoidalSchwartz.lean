import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdHermitianTransverseCutoff
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdAxisRealSchwartz244
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic

/-!
# Constructive compact-Fourier real solenoidal Schwartz realization

Given ANY smooth complex vector profile U on the actual positive-depth 3-axis
frequency carrier, and ANY smooth compactly supported real cutoff chi, form

  G(xi) = chi(xi) (|xi|^2 U(xi) - (xi dot U(xi)) xi).

This is already pointwise transverse. Hermitianize by adding the conjugate
reflection at -xi. The result is a genuine vector-valued Schwartz map with
compact Fourier support, pointwise Fourier divergence zero, and exact Hermitian
symmetry. Transport its coordinates to the Euclidean Fourier Hilbert carrier,
invert the Schwartz Fourier transform, and take their real parts. Fourier
inversion and the existing Hermitian-to-real theorem identify the real
physical Schwartz field EXACTLY with the prescribed Fourier profile.

Unlike the earlier polynomial-only theorem, this package constructs actual
real, spatially divergence-free Schwartz velocity components. A full density
statement for the weighted H3 solenoidal subspace still requires quantitative
annular frequency cutoffs, their approximation estimates, and preservation of
the prescribed matched-derivative reconstruction; those are not asserted here.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators Topology ContDiff SchwartzMap FourierTransform ComplexConjugate LineDeriv

noncomputable section
set_option maxHeartbeats 1200000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev CPol244 := A3 → ℂ
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeCompactHermitianSchwartz244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Smooth polynomial projection and compact scalar localization -/

private theorem thirdFullComplexFrequencyCoord_contDiff244 (j : A3) :
    ContDiff ℝ ∞ (fun ξ : Freq244 => (ξ j : ℂ)) := by
  exact Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ j)

/-- The complete complex transverse numerator is a smooth profile whenever
its (possibly frequency-dependent) vector input is smooth. -/
theorem thirdFullComplexTransverseNumerator_contDiff244
    (U : Freq244 → CPol244) (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (fun ξ : Freq244 =>
      thirdFullComplexTransverseNumerator244 ξ (U ξ)) := by
  have hRadiusReal : ContDiff ℝ ∞
      (fun ξ : Freq244 => thirdTriadAxisDot244 ξ ξ) := by
    change ContDiff ℝ ∞ (fun ξ : Freq244 =>
      ∑ j : A3, ξ j * ξ j)
    exact ContDiff.sum (s := Finset.univ)
      (fun j _ => (contDiff_apply ℝ ℝ j).mul (contDiff_apply ℝ ℝ j))
  have hRadius : ContDiff ℝ ∞
      (fun ξ : Freq244 => (thirdTriadAxisDot244 ξ ξ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hRadiusReal
  have hMixed : ContDiff ℝ ∞
      (fun ξ : Freq244 => mixedDot ξ (U ξ)) := by
    change ContDiff ℝ ∞ (fun ξ : Freq244 =>
      ∑ j : A3, (ξ j : ℂ) * (U ξ) j)
    exact ContDiff.sum (s := Finset.univ)
      (fun j _ => (thirdFullComplexFrequencyCoord_contDiff244 j).mul
        ((contDiff_apply ℝ ℂ j).comp hU))
  apply contDiff_pi'
  intro j
  have hj : ContDiff ℝ ∞ (fun ξ : Freq244 => (U ξ) j) :=
    (contDiff_apply ℝ ℂ j).comp hU
  change ContDiff ℝ ∞ (fun ξ : Freq244 =>
    (thirdTriadAxisDot244 ξ ξ : ℂ) * (U ξ) j -
      mixedDot ξ (U ξ) * (ξ j : ℂ))
  exact (hRadius.mul hj).sub
    (hMixed.mul (thirdFullComplexFrequencyCoord_contDiff244 j))

/-- Smooth real cutoff times smooth complex transverse numerator is smooth. -/
theorem thirdFullComplexCutoffTransverseProfile_contDiff244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχ : ContDiff ℝ ∞ χ) (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (thirdFullComplexCutoffTransverseProfile244 χ U) := by
  have hχc : ContDiff ℝ ∞ (fun ξ : Freq244 => (χ ξ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hχ
  have hN := thirdFullComplexTransverseNumerator_contDiff244 U hU
  apply contDiff_pi'
  intro j
  have hNj : ContDiff ℝ ∞ (fun ξ : Freq244 =>
      thirdFullComplexTransverseNumerator244 ξ (U ξ) j) :=
    (contDiff_apply ℝ ℂ j).comp hN
  change ContDiff ℝ ∞ (fun ξ : Freq244 =>
      (χ ξ : ℂ) * thirdFullComplexTransverseNumerator244 ξ (U ξ) j)
  exact hχc.mul hNj

/-- Compact support is inherited solely from the real cutoff, even when
U has no compact support and the transverse numerator grows polynomially. -/
theorem thirdFullComplexCutoffTransverseProfile_hasCompactSupport244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχ : HasCompactSupport χ) :
    HasCompactSupport (thirdFullComplexCutoffTransverseProfile244 χ U) := by
  have hs := hχ.smul_right
    (f' := fun ξ : Freq244 => thirdFullComplexTransverseNumerator244 ξ (U ξ))
  convert hs using 1
  funext ξ j
  change (χ ξ : ℂ) * thirdFullComplexTransverseNumerator244 ξ (U ξ) j =
    ((χ ξ : ℝ) • thirdFullComplexTransverseNumerator244 ξ (U ξ)) j
  simp only [Pi.smul_apply, Complex.real_smul]

/-! ## Hermitianization in the genuine smooth compact Fourier category -/

/-- Unconditional Hermitianization, with no even-cutoff or reality assumption
on the input. Exact transverse projection is done BEFORE reflection. -/
noncomputable def thirdFullCompactHermitianTransverseProfile244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244) : Freq244 → CPol244 :=
  thirdFullAxisHermitianize244
    (thirdFullComplexCutoffTransverseProfile244 χ U)

/-- The constructed Fourier profile is exactly transverse everywhere. -/
theorem thirdFullCompactHermitianTransverseProfile_divergence244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244) (ξ : Freq244) :
    mixedDot ξ (thirdFullCompactHermitianTransverseProfile244 χ U ξ) = 0 := by
  change thirdFullAxisComplexDot244 ξ
    (thirdFullAxisHermitianize244
      (thirdFullComplexCutoffTransverseProfile244 χ U) ξ) = 0
  apply thirdFullAxisHermitianize_solenoidal244
  intro η
  change mixedDot η (thirdFullComplexCutoffTransverseProfile244 χ U η) = 0
  exact thirdFullComplexCutoffTransverseProfile_divergence244 χ U η

/-- Frequency reflection and complex conjugation agree pointwise. -/
theorem thirdFullCompactHermitianTransverseProfile_reality244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244) (ξ : Freq244) :
    thirdFullCompactHermitianTransverseProfile244 χ U (-ξ) =
      fun j => star (thirdFullCompactHermitianTransverseProfile244 χ U ξ j) := by
  exact thirdFullAxisHermitianize_reality244
    (thirdFullComplexCutoffTransverseProfile244 χ U) ξ

/-- Smoothness of both the transverse polynomial and its conjugate reflection. -/
theorem thirdFullCompactHermitianTransverseProfile_contDiff244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχ : ContDiff ℝ ∞ χ) (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (thirdFullCompactHermitianTransverseProfile244 χ U) := by
  exact thirdFullAxisHermitianize_contDiff244 _
    (thirdFullComplexCutoffTransverseProfile_contDiff244 χ U hχ hU)

/-- Hermitianization retains compact support, including both reflected sides. -/
theorem thirdFullCompactHermitianTransverseProfile_hasCompactSupport244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχ : HasCompactSupport χ) :
    HasCompactSupport (thirdFullCompactHermitianTransverseProfile244 χ U) := by
  exact thirdFullAxisHermitianize_hasCompactSupport244 _
    (thirdFullComplexCutoffTransverseProfile_hasCompactSupport244 χ U hχ)

/-- If a cutoff is zero at both a frequency and its reflection, then the
resulting Hermitian solenoidal packet is zero at that frequency. -/
theorem thirdFullCompactHermitianTransverseProfile_zero_of_cutoff_pair_zero244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244) (ξ : Freq244)
    (hχ : χ ξ = 0) (hχneg : χ (-ξ) = 0) :
    thirdFullCompactHermitianTransverseProfile244 χ U ξ = 0 := by
  have h0 := thirdFullComplexCutoffTransverseProfile_zero_of_cutoff_zero244
    χ U ξ hχ
  have hNeg := thirdFullComplexCutoffTransverseProfile_zero_of_cutoff_zero244
    χ U (-ξ) hχneg
  funext j
  change thirdFullComplexCutoffTransverseProfile244 χ U ξ j +
    star (thirdFullComplexCutoffTransverseProfile244 χ U (-ξ) j) = 0
  rw [congrFun h0 j, congrFun hNeg j]
  simp

/-- The transverse numerator vanishes at zero even for an arbitrary cutoff,
and Hermitianization does not add a zero-frequency artifact. -/
theorem thirdFullCompactHermitianTransverseProfile_at_zero244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244) :
    thirdFullCompactHermitianTransverseProfile244 χ U 0 = 0 := by
  funext j
  have h0 :
      thirdFullComplexCutoffTransverseProfile244 χ U (0 : Freq244) j = 0 := by
    simpa only [show (0 : Freq244) = (fun _ => (0 : ℝ)) from rfl]
      using congrFun
        (thirdFullComplexCutoffTransverseProfile_at_zero244 χ U) j
  change thirdFullComplexCutoffTransverseProfile244 χ U 0 j +
    star (thirdFullComplexCutoffTransverseProfile244 χ U (-0) j) = 0
  simpa only [neg_zero, h0, star_zero, add_zero]

/-- The construction packages as a genuine smooth, compactly supported
VECTOR Schwartz map on the actual axis frequency carrier. -/
noncomputable def thirdFullCompactHermitianTransverseSchwartz244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) :
    𝓢(Freq244, CPol244) :=
  (thirdFullCompactHermitianTransverseProfile_hasCompactSupport244 χ U hχcompact).toSchwartzMap
    (thirdFullCompactHermitianTransverseProfile_contDiff244 χ U hχsmooth hUsmooth)

@[simp]
theorem thirdFullCompactHermitianTransverseSchwartz_apply244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) (ξ : Freq244) :
    thirdFullCompactHermitianTransverseSchwartz244
      χ U hχsmooth hχcompact hUsmooth ξ =
        thirdFullCompactHermitianTransverseProfile244 χ U ξ := rfl

/-! ## Exact Hilbert-carrier Fourier and real physical Schwartz reconstruction -/

/-- The actual `H3FourierPoint3` frequency component, transported without
changing its finite-axis order. -/
noncomputable def thirdFullCompactHermitianHilbertComponent244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) (j : A3) :
    𝓢(V3, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : A3 => ℝ))
    ((SchwartzMap.postcompCLM (𝕜 := ℝ)
      (ContinuousLinearMap.proj j : CPol244 →L[ℝ] ℂ))
      (thirdFullCompactHermitianTransverseSchwartz244
        χ U hχsmooth hχcompact hUsmooth))

@[simp]
theorem thirdFullCompactHermitianHilbertComponent_apply244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) (j : A3) (ξ : V3) :
    thirdFullCompactHermitianHilbertComponent244
      χ U hχsmooth hχcompact hUsmooth j ξ =
        thirdFullCompactHermitianTransverseProfile244 χ U (WithLp.ofLp ξ) j := by
  change thirdFullCompactHermitianTransverseSchwartz244
      χ U hχsmooth hχcompact hUsmooth (WithLp.ofLp ξ) j = _
  rfl

/-- Pointwise Hermitian symmetry of the genuine Euclidean Fourier Schwartz
component (not only an `L²`-a.e. symmetry). -/
theorem thirdFullCompactHermitianHilbertComponent_reality244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) (j : A3) (ξ : V3) :
    thirdFullCompactHermitianHilbertComponent244
      χ U hχsmooth hχcompact hUsmooth j (-ξ) =
    star (thirdFullCompactHermitianHilbertComponent244
      χ U hχsmooth hχcompact hUsmooth j ξ) := by
  simp only [thirdFullCompactHermitianHilbertComponent_apply244, WithLp.ofLp_neg]
  exact congrFun (thirdFullCompactHermitianTransverseProfile_reality244
    χ U (WithLp.ofLp ξ)) j

/-- Exact physical complex Schwartz inverse transform of each component. -/
noncomputable def thirdFullCompactHermitianInverseSchwartz244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) (j : A3) :
    𝓢(V3, ℂ) :=
  𝓕⁻ (thirdFullCompactHermitianHilbertComponent244
    χ U hχsmooth hχcompact hUsmooth j)

/-- There is no limit or distributional gap in the inverse Fourier bridge. -/
theorem thirdFullCompactHermitianInverseSchwartz_fourier244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) (j : A3) :
    𝓕 (thirdFullCompactHermitianInverseSchwartz244
      χ U hχsmooth hχcompact hUsmooth j) =
    thirdFullCompactHermitianHilbertComponent244
      χ U hχsmooth hχcompact hUsmooth j :=
  FourierTransform.fourier_fourierInv_eq _

/-- Hermitian Fourier reality forces the actual Schwartz inverse transform
to be real at every physical point. -/
theorem thirdFullCompactHermitianInverseSchwartz_im_zero244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) (j : A3) (x : V3) :
    (thirdFullCompactHermitianInverseSchwartz244
      χ U hχsmooth hχcompact hUsmooth j x).im = 0 := by
  exact lowNormalQuarterAxisHermitianSchwartz_fourierInv_im_zero
    (thirdFullCompactHermitianHilbertComponent244
      χ U hχsmooth hχcompact hUsmooth j)
    (thirdFullCompactHermitianHilbertComponent_reality244
      χ U hχsmooth hχcompact hUsmooth j) x

/-- The ACTUAL real physical Schwartz velocity produced from arbitrary smooth
complex Fourier input by compact transverse localization and reflection. -/
noncomputable def thirdFullCompactRealSolenoidalSchwartz244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) :
    A3 → 𝓢(V3, ℝ) :=
  fun j => (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM)
    (thirdFullCompactHermitianInverseSchwartz244
      χ U hχsmooth hχcompact hUsmooth j)

/-- Complexification of the REAL Schwartz component reproduces the entire
complex inverse Schwartz function, not merely an `L²` class. -/
theorem thirdFullCompactRealSolenoidalSchwartz_complexify244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) (j : A3) :
    h3SchwartzComplexify
      (thirdFullCompactRealSolenoidalSchwartz244
        χ U hχsmooth hχcompact hUsmooth j) =
    thirdFullCompactHermitianInverseSchwartz244
      χ U hχsmooth hχcompact hUsmooth j := by
  ext x
  change (((thirdFullCompactHermitianInverseSchwartz244
      χ U hχsmooth hχcompact hUsmooth j x).re : ℝ) : ℂ) =
    thirdFullCompactHermitianInverseSchwartz244
      χ U hχsmooth hχcompact hUsmooth j x
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simp only [Complex.ofReal_im]
    exact (thirdFullCompactHermitianInverseSchwartz_im_zero244
      χ U hχsmooth hχcompact hUsmooth j x).symm

/-- EXACT reconstruction of the prescribed compact Hermitian transverse
Fourier component from the real physical Schwartz velocity. -/
theorem thirdFullCompactRealSolenoidalSchwartz_fourier244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) (j : A3) :
    𝓕 (h3SchwartzComplexify
      (thirdFullCompactRealSolenoidalSchwartz244
        χ U hχsmooth hχcompact hUsmooth j)) =
    thirdFullCompactHermitianHilbertComponent244
      χ U hχsmooth hχcompact hUsmooth j := by
  rw [thirdFullCompactRealSolenoidalSchwartz_complexify244]
  exact thirdFullCompactHermitianInverseSchwartz_fourier244
    χ U hχsmooth hχcompact hUsmooth j

/-- The entire complex Fourier transform of the ACTUAL real Schwartz
velocity is pointwise identical to the prescribed Hermitian transverse field. -/
theorem thirdFullCompactRealSolenoidalSchwartz_fourier_vector244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) (ξ : V3) :
    (fun j : A3 => 𝓕 (h3SchwartzComplexify
      (thirdFullCompactRealSolenoidalSchwartz244
        χ U hχsmooth hχcompact hUsmooth j)) ξ) =
    thirdFullCompactHermitianTransverseProfile244 χ U (WithLp.ofLp ξ) := by
  funext j
  rw [thirdFullCompactRealSolenoidalSchwartz_fourier244,
    thirdFullCompactHermitianHilbertComponent_apply244]

/-- The real physical Schwartz velocity has zero Fourier divergence at
EVERY frequency. -/
theorem thirdFullCompactRealSolenoidalSchwartz_fourier_divergence244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) (ξ : V3) :
    mixedDot (WithLp.ofLp ξ)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullCompactRealSolenoidalSchwartz244
          χ U hχsmooth hχcompact hUsmooth j)) ξ) = 0 := by
  rw [thirdFullCompactRealSolenoidalSchwartz_fourier_vector244]
  exact thirdFullCompactHermitianTransverseProfile_divergence244 χ U _

/-- FULL physical divergence-free identity, for the real Schwartz velocity
at every spatial point. This is proved by Fourier-transform injectivity and
the exact finite-axis Schwartz divergence multiplier. -/
theorem thirdFullCompactRealSolenoidalSchwartz_physical_divergence244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) :
    ∀ x : V3,
      ∑ j : A3,
        fderiv ℝ
          (h3SchwartzComplexify
            (thirdFullCompactRealSolenoidalSchwartz244
              χ U hχsmooth hχcompact hUsmooth j))
          x (h3FourierAxisDirection j) = 0 := by
  let F : A3 → 𝓢(V3, ℂ) := fun j =>
    h3SchwartzComplexify (thirdFullCompactRealSolenoidalSchwartz244
      χ U hχsmooth hχcompact hUsmooth j)
  have hFourierZero : 𝓕 (h3SchwartzDivergence F) = 0 := by
    ext ξ
    rw [h3SchwartzDivergence_fourier F (WithLp.ofLp ξ)]
    have hDiv : mixedDot (WithLp.ofLp ξ)
        (h3SchwartzTriadPolarization F (WithLp.ofLp ξ)) = 0 := by
      change mixedDot (WithLp.ofLp ξ)
        (fun j : A3 => 𝓕 (F j) ξ) = 0
      exact thirdFullCompactRealSolenoidalSchwartz_fourier_divergence244
        χ U hχsmooth hχcompact hUsmooth ξ
    rw [hDiv]
    simp
  have hPhysicalZero : h3SchwartzDivergence F = 0 := by
    have h := congrArg
      (fun G : 𝓢(V3, ℂ) => (𝓕⁻ G : 𝓢(V3, ℂ)))
      hFourierZero
    simpa using h
  intro x
  have hx := congrArg (fun G : 𝓢(V3, ℂ) => G x) hPhysicalZero
  simpa only [h3SchwartzDivergence_apply, zero_apply] using hx

/-- On EVERY momentum-conserving triad from the physical real field's exact
Fourier transform, the complete full-third symbol equals the uncorrected
sixth-power flux: the longitudinal defect vanishes identically. -/
theorem thirdFullCompactRealSolenoidalSchwartz_six_eq_flux244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (_hχsmooth : ContDiff ℝ ∞ χ) (_hχcompact : HasCompactSupport χ)
    (_hUsmooth : ContDiff ℝ ∞ U)
    (p q r : Freq244) (hm : ∀ j, p j + q j + r j = 0) :
    thirdFullComplexSixSymbol244 p q r
      (thirdFullCompactHermitianTransverseProfile244 χ U p)
      (thirdFullCompactHermitianTransverseProfile244 χ U q)
      (thirdFullCompactHermitianTransverseProfile244 χ U r) =
    thirdFullComplexSixthPowerFlux244 p q r
      (thirdFullCompactHermitianTransverseProfile244 χ U p)
      (thirdFullCompactHermitianTransverseProfile244 χ U q)
      (thirdFullCompactHermitianTransverseProfile244 χ U r) := by
  rw [thirdFullComplexSix_eq_flux_add_longitudinal244 p q r _ _ _ hm]
  have hDefect : thirdFullComplexLongitudinalFluxDefect244 p q r
      (thirdFullCompactHermitianTransverseProfile244 χ U p)
      (thirdFullCompactHermitianTransverseProfile244 χ U q)
      (thirdFullCompactHermitianTransverseProfile244 χ U r) = 0 :=
    thirdFullComplexLongitudinalFluxDefect_zero_of_solenoidal244
      p q r _ _ _
      (thirdFullCompactHermitianTransverseProfile_divergence244 χ U p)
      (thirdFullCompactHermitianTransverseProfile_divergence244 χ U q)
      (thirdFullCompactHermitianTransverseProfile_divergence244 χ U r)
  rw [hDefect]
  ring

/-- The complete six-orbit / sixth-power identity evaluated on the Fourier
transforms of the CONSTRUCTED REAL PHYSICAL SCHWARTZ VELOCITY. This removes the
longitudinal term without importing an abstract solenoidal approximation axiom. -/
theorem thirdFullCompactRealSolenoidalSchwartz_physical_six_eq_flux244
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U)
    (p q r : V3)
    (hm : ∀ j : A3,
      (WithLp.ofLp p) j + (WithLp.ofLp q) j + (WithLp.ofLp r) j = 0) :
    thirdFullComplexSixSymbol244
      (WithLp.ofLp p) (WithLp.ofLp q) (WithLp.ofLp r)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullCompactRealSolenoidalSchwartz244
          χ U hχsmooth hχcompact hUsmooth j)) p)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullCompactRealSolenoidalSchwartz244
          χ U hχsmooth hχcompact hUsmooth j)) q)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullCompactRealSolenoidalSchwartz244
          χ U hχsmooth hχcompact hUsmooth j)) r) =
    thirdFullComplexSixthPowerFlux244
      (WithLp.ofLp p) (WithLp.ofLp q) (WithLp.ofLp r)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullCompactRealSolenoidalSchwartz244
          χ U hχsmooth hχcompact hUsmooth j)) p)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullCompactRealSolenoidalSchwartz244
          χ U hχsmooth hχcompact hUsmooth j)) q)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullCompactRealSolenoidalSchwartz244
          χ U hχsmooth hχcompact hUsmooth j)) r) := by
  have hp := thirdFullCompactRealSolenoidalSchwartz_fourier_vector244
    χ U hχsmooth hχcompact hUsmooth p
  have hq := thirdFullCompactRealSolenoidalSchwartz_fourier_vector244
    χ U hχsmooth hχcompact hUsmooth q
  have hr := thirdFullCompactRealSolenoidalSchwartz_fourier_vector244
    χ U hχsmooth hχcompact hUsmooth r
  rw [hp, hq, hr]
  exact thirdFullCompactRealSolenoidalSchwartz_six_eq_flux244
    χ U hχsmooth hχcompact hUsmooth _ _ _ hm

end
end PrimeTensor.FirstMonomialTriad
