import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdRegularizedSolenoidalDiagonalDensity
import Mathlib.Tactic

/-!
# Exact weighted-Fourier identification for real solenoidal Schwartz recovery

The earlier modules constructed actual real divergence-free Schwartz velocities
from a smooth complex profile `U` and compact smooth real window `χ`, and
proved strong weighted-H³ convergence for the regularized Leray spectral
states. These are different constructions until their Fourier encodings are
identified.

This file proves an exact bridge, at the same positive scale `δ_n=1/(n+1)`:

  W₃(ξ) 𝓕(u_n,j)(ξ) = R_n(ξ) W₃(ξ) U_j(ξ)

provided (1) `U` is pointwise Hermitian and transverse, (2) `χ` is even, and
(3) `χ=1` at every frequency where the chosen input component is nonzero.
The final statement identifies the genuine bundled Fourier-L² class of
`R_n F_j` with the *weighted* Fourier transform of the actual real Schwartz
velocity, under the explicit hypothesis `F_j = W₃ U_j` almost everywhere.

No weighted-L² element is assumed to be pointwise smooth. In particular,
this theorem does NOT yet prove that an arbitrary spectral input `F` admits
such a smooth, compact, pointwise solenoidal representative `U`, or construct
a cutoff flat on its support. Those are separate density/selection steps.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Filter Topology PrimeTensor.Bridge.Euclidean
open scoped ENNReal SchwartzMap FourierTransform ComplexConjugate ContDiff

noncomputable section
set_option maxHeartbeats 1200000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev Freq244 := A3 → ℝ
private abbrev CPol244 := A3 → ℂ
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypePhysicalWeightedBridge244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At scale `n`, use the positive, nonsingular physical Schwartz recovery,
with precisely the same parameter as the weighted spectral multiplier. -/
noncomputable def thirdFullRegularizedPhysicalSchwartzAt244
    (n : ℕ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) :
    A3 → 𝓢(V3, ℝ) :=
  thirdFullRegularizedRealSolenoidalSchwartz244
    (h3FullThirdRegularizationScale244 n)
    (h3FullThirdRegularizationScale_pos244 n)
    χ U hχsmooth hχcompact hUsmooth

/-- Every physical Schwarz field in this family is exactly divergence-free
at every spatial point, not merely almost everywhere in Fourier space. -/
theorem thirdFullRegularizedPhysicalSchwartzAt_divergence244
    (n : ℕ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U) :
    ∀ x : V3, ∑ j : A3,
      fderiv ℝ (h3SchwartzComplexify
        (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
          hχsmooth hχcompact hUsmooth j))
        x (h3FourierAxisDirection j) = 0 := by
  exact thirdFullRegularizedRealSolenoidalSchwartz_physical_divergence244
    (h3FullThirdRegularizationScale244 n)
    (h3FullThirdRegularizationScale_pos244 n)
    χ U hχsmooth hχcompact hUsmooth

/-- At every frequency, the Fourier transform of the ACTUAL real field is
the exact regularized transverse profile, with no a.e. weakening. -/
theorem thirdFullRegularizedPhysicalSchwartzAt_fourier_exact244
    (n : ℕ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U)
    (hχeven : ∀ ξ, χ (fun j => -ξ j) = χ ξ)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (hUdiv : ∀ ξ, mixedDot ξ (U ξ) = 0)
    (ξ : V3) (j : A3) :
    𝓕 (h3SchwartzComplexify
      (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
        hχsmooth hχcompact hUsmooth j)) ξ =
      ((χ (WithLp.ofLp ξ) *
        h3FullThirdRadialRecoveryFactor244 n ξ : ℝ) : ℂ) *
        U (WithLp.ofLp ξ) j := by
  change 𝓕 (h3SchwartzComplexify
      (thirdFullRegularizedRealSolenoidalSchwartz244
        (h3FullThirdRegularizationScale244 n)
        (h3FullThirdRegularizationScale_pos244 n)
        χ U hχsmooth hχcompact hUsmooth j)) ξ = _
  rw [thirdFullRegularizedRealSolenoidalSchwartz_fourier_exact244
      (h3FullThirdRegularizationScale244 n)
      (h3FullThirdRegularizationScale_pos244 n)
      χ U hχsmooth hχcompact hUsmooth
      hχeven hUherm hUdiv ξ j]
  rw [h3FullThirdRadialRecoveryFactor_eq_axis244 n ξ]

/-- The EXACT weighted Fourier amplitude of the real Schwartz field has
the same Sobolev multiplier as the canonical spectral H³ encoder. -/
theorem thirdFullRegularizedPhysicalSchwartzAt_fourier_weighted244
    (n : ℕ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U)
    (hχeven : ∀ ξ, χ (fun j => -ξ j) = χ ξ)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (hUdiv : ∀ ξ, mixedDot ξ (U ξ) = 0)
    (ξ : V3) (j : A3) :
    (h3SobolevFrequencyWeight ξ : ℂ) *
      𝓕 (h3SchwartzComplexify
        (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
          hχsmooth hχcompact hUsmooth j)) ξ =
      ((χ (WithLp.ofLp ξ) *
          h3FullThirdRadialRecoveryFactor244 n ξ : ℝ) : ℂ) *
        ((h3SobolevFrequencyWeight ξ : ℂ) * U (WithLp.ofLp ξ) j) := by
  rw [thirdFullRegularizedPhysicalSchwartzAt_fourier_exact244
    n χ U hχsmooth hχcompact hUsmooth hχeven hUherm hUdiv ξ j]
  ring

/-- A cutoff which is one wherever the chosen Fourier component is nonzero
has NO effect on that component. This is the exact support hypothesis which
a later cutoff-selection theorem must discharge. -/
theorem thirdFullRegularizedPhysicalSchwartzAt_fourier_no_cutoff244
    (n : ℕ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U)
    (hχeven : ∀ ξ, χ (fun j => -ξ j) = χ ξ)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (hUdiv : ∀ ξ, mixedDot ξ (U ξ) = 0)
    (hχone : ∀ ξ j, U ξ j ≠ 0 → χ ξ = 1)
    (ξ : V3) (j : A3) :
    𝓕 (h3SchwartzComplexify
      (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
        hχsmooth hχcompact hUsmooth j)) ξ =
      (h3FullThirdRadialRecoveryFactor244 n ξ : ℂ) *
        U (WithLp.ofLp ξ) j := by
  rw [thirdFullRegularizedPhysicalSchwartzAt_fourier_exact244
    n χ U hχsmooth hχcompact hUsmooth hχeven hUherm hUdiv ξ j]
  by_cases hz : U (WithLp.ofLp ξ) j = 0
  · simp only [hz, mul_zero]
  · rw [hχone (WithLp.ofLp ξ) j hz]
    simp only [one_mul]

/-- After removing a cutoff flat on the input support, the weighted Fourier
amplitude is literally the `R_n` multiplier of the weighted input. -/
theorem thirdFullRegularizedPhysicalSchwartzAt_weighted_no_cutoff244
    (n : ℕ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U)
    (hχeven : ∀ ξ, χ (fun j => -ξ j) = χ ξ)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (hUdiv : ∀ ξ, mixedDot ξ (U ξ) = 0)
    (hχone : ∀ ξ j, U ξ j ≠ 0 → χ ξ = 1)
    (ξ : V3) (j : A3) :
    (h3SobolevFrequencyWeight ξ : ℂ) *
      𝓕 (h3SchwartzComplexify
        (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
          hχsmooth hχcompact hUsmooth j)) ξ =
      (h3FullThirdRadialRecoveryFactor244 n ξ : ℂ) *
        ((h3SobolevFrequencyWeight ξ : ℂ) * U (WithLp.ofLp ξ) j) := by
  rw [thirdFullRegularizedPhysicalSchwartzAt_fourier_no_cutoff244
    n χ U hχsmooth hχcompact hUsmooth hχeven hUherm hUdiv
    hχone ξ j]
  ring

/-- EXACT almost-everywhere bridge: the canonical bundled weighted Fourier
`L²` recovery of `F` has as a representative the Sobolev-weighted Fourier
transform of an ACTUAL, REAL, divergence-free Schwartz field.

`hF` identifies the supplied smooth polarization with the original weighted
input `F`, and `hχone` explicitly requires support-flatness of the cutoff.
No global smoothness or representative choice is assumed for `F`. -/
theorem thirdFullRegularizedPhysicalSchwartzAt_weighted_L2_ae244
    (n : ℕ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U)
    (hχeven : ∀ ξ, χ (fun j => -ξ j) = χ ξ)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (hUdiv : ∀ ξ, mixedDot ξ (U ξ) = 0)
    (hχone : ∀ ξ j, U ξ j ≠ 0 → χ ξ = 1)
    (F : H3SpectralScalarState) (j : A3)
    (hF : (F : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
        U (WithLp.ofLp ξ) j)) :
    (h3FullThirdRadialRecoveryL2244 n F : V3 → ℂ) =ᵐ[volume]
      (fun ξ : V3 =>
        (h3SobolevFrequencyWeight ξ : ℂ) *
          𝓕 (h3SchwartzComplexify
            (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
              hχsmooth hχcompact hUsmooth j)) ξ) := by
  have hRep := MeasureTheory.MemLp.coeFn_toLp
    (h3FullThirdRadialRecoveryRaw_memLp244 n F)
  filter_upwards [hRep, hF] with ξ hAt hWeighted
  have hAt' :
      (h3FullThirdRadialRecoveryL2244 n F : V3 → ℂ) ξ =
        h3FullThirdRadialRecoveryRaw244 n F ξ := hAt
  rw [hAt']
  change (h3FullThirdRadialRecoveryFactor244 n ξ : ℂ) * F ξ = _
  rw [hWeighted]
  exact (thirdFullRegularizedPhysicalSchwartzAt_weighted_no_cutoff244
    n χ U hχsmooth hχcompact hUsmooth hχeven hUherm hUdiv
    hχone ξ j).symm

/-- In the project's *actual* `Fin 3` spectral ordering, all three
components of the regularized weighted velocity are represented by the
Sobolev-weighted Fourier transforms of the SAME real physical Schwartz
velocity, transported using `h3AxisOfFin3`. -/
theorem thirdFullRegularizedPhysicalSchwartzAt_velocity_weighted_L2_ae244
    (n : ℕ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U)
    (hχeven : ∀ ξ, χ (fun j => -ξ j) = χ ξ)
    (hUherm : H3ComplexHermitianPolarizationProfile244 U)
    (hUdiv : ∀ ξ, mixedDot ξ (U ξ) = 0)
    (hχone : ∀ ξ j, U ξ j ≠ 0 → χ ξ = 1)
    (F : H3SpectralVelocityState)
    (hF : ∀ i : Fin 3,
      (F i : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          U (WithLp.ofLp ξ) (h3AxisOfFin3 i))) :
    ∀ i : Fin 3,
      (h3FullThirdRadialRecoveryVelocity244 n F i : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          𝓕 (h3SchwartzComplexify
            (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
              hχsmooth hχcompact hUsmooth (h3AxisOfFin3 i))) ξ) := by
  intro i
  exact thirdFullRegularizedPhysicalSchwartzAt_weighted_L2_ae244
    n χ U hχsmooth hχcompact hUsmooth hχeven hUherm hUdiv
    hχone (F i) (h3AxisOfFin3 i) (hF i)

/-- The full-third six-orbit identity is inherited by the ACTUAL real
Schwartz family, at each regularization scale and every momentum triad. -/
theorem thirdFullRegularizedPhysicalSchwartzAt_six_eq_flux244
    (n : ℕ)
    (χ : Freq244 → ℝ) (U : Freq244 → CPol244)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (hUsmooth : ContDiff ℝ ∞ U)
    (p q r : V3)
    (hm : ∀ j : A3,
      (WithLp.ofLp p) j + (WithLp.ofLp q) j + (WithLp.ofLp r) j = 0) :
    thirdFullComplexSixSymbol244 (WithLp.ofLp p) (WithLp.ofLp q) (WithLp.ofLp r)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
          hχsmooth hχcompact hUsmooth j)) p)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
          hχsmooth hχcompact hUsmooth j)) q)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
          hχsmooth hχcompact hUsmooth j)) r) =
    thirdFullComplexSixthPowerFlux244 (WithLp.ofLp p) (WithLp.ofLp q) (WithLp.ofLp r)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
          hχsmooth hχcompact hUsmooth j)) p)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
          hχsmooth hχcompact hUsmooth j)) q)
      (fun j : A3 => 𝓕 (h3SchwartzComplexify
        (thirdFullRegularizedPhysicalSchwartzAt244 n χ U
          hχsmooth hχcompact hUsmooth j)) r) := by
  exact thirdFullRegularizedRealSolenoidalSchwartz_six_eq_flux244
    (h3FullThirdRegularizationScale244 n)
    (h3FullThirdRegularizationScale_pos244 n)
    χ U hχsmooth hχcompact hUsmooth p q r hm

/-- Conditional *moving physical Schwartz* assembly. Once a sequence of
smooth compact, Hermitian, transverse raw inputs is identified with the given
weighted inputs, and cutoffs flat on those supports are supplied, the actual
real divergence-free Schwartz fields represent exactly the same regularized
weighted spectral states. Therefore the resulting weighted states converge,
are Cauchy, and their canonical real physical decoders converge.

The point of the explicit hypotheses is that the missing smooth-solenoidal
compact input and cutoff selection are not silently inferred from an `L²`
Leray image. -/
theorem thirdFullRegularizedPhysicalSchwartzAt_moving_weighted_completion244
    (target : H3SpectralVelocityState)
    (F : ℕ → H3SpectralVelocityState)
    (hFconverges : Tendsto F atTop (𝓝 target))
    (χ : ℕ → Freq244 → ℝ) (U : ℕ → Freq244 → CPol244)
    (hχsmooth : ∀ n, ContDiff ℝ ∞ (χ n))
    (hχcompact : ∀ n, HasCompactSupport (χ n))
    (hUsmooth : ∀ n, ContDiff ℝ ∞ (U n))
    (hχeven : ∀ n ξ, χ n (fun j => -ξ j) = χ n ξ)
    (hUherm : ∀ n, H3ComplexHermitianPolarizationProfile244 (U n))
    (hUdiv : ∀ n ξ, mixedDot ξ (U n ξ) = 0)
    (hχone : ∀ n ξ j, U n ξ j ≠ 0 → χ n ξ = 1)
    (hFweighted : ∀ n i,
      (F n i : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          U n (WithLp.ofLp ξ) (h3AxisOfFin3 i))) :
    Tendsto (fun n => h3FullThirdRadialRecoveryVelocity244 n (F n))
      atTop (𝓝 target) ∧
    (∀ (n : ℕ) (i : Fin 3),
      (h3FullThirdRadialRecoveryVelocity244 n (F n) i : V3 → ℂ) =ᵐ[volume]
        (fun ξ : V3 => (h3SobolevFrequencyWeight ξ : ℂ) *
          𝓕 (h3SchwartzComplexify
            (thirdFullRegularizedPhysicalSchwartzAt244 n (χ n) (U n)
              (hχsmooth n) (hχcompact n) (hUsmooth n)
              (h3AxisOfFin3 i))) ξ)) ∧
    (∀ (n : ℕ) (x : V3), ∑ j : A3,
      fderiv ℝ (h3SchwartzComplexify
        (thirdFullRegularizedPhysicalSchwartzAt244 n (χ n) (U n)
          (hχsmooth n) (hχcompact n) (hUsmooth n) j))
        x (h3FourierAxisDirection j) = 0) ∧
    Tendsto (fun n => h3SpectralVelocityDecodeRealL2
      (h3FullThirdRadialRecoveryVelocity244 n (F n)))
      atTop (𝓝 (h3SpectralVelocityDecodeRealL2 target)) ∧
    CauchySeq (fun n => h3FullThirdRadialRecoveryVelocity244 n (F n)) := by
  have hLimit := h3FullThirdRadialRecoveryVelocity_moving_tendsto244
    target F hFconverges
  have hPhysical (n : ℕ) (i : Fin 3) :=
    thirdFullRegularizedPhysicalSchwartzAt_velocity_weighted_L2_ae244
      n (χ n) (U n) (hχsmooth n) (hχcompact n) (hUsmooth n)
      (hχeven n) (hUherm n) (hUdiv n) (hχone n)
      (F n) (hFweighted n) i
  have hDiv (n : ℕ) : ∀ x : V3, ∑ j : A3,
      fderiv ℝ (h3SchwartzComplexify
        (thirdFullRegularizedPhysicalSchwartzAt244 n (χ n) (U n)
          (hχsmooth n) (hχcompact n) (hUsmooth n) j))
        x (h3FourierAxisDirection j) = 0 :=
    thirdFullRegularizedPhysicalSchwartzAt_divergence244
      n (χ n) (U n) (hχsmooth n) (hχcompact n) (hUsmooth n)
  exact ⟨hLimit, hPhysical, hDiv,
    h3SpectralVelocityDecodeRealL2_tendsto_of_weighted244 hLimit,
    hLimit.cauchySeq⟩

end
end PrimeTensor.FirstMonomialTriad
