import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalWeightedSpectralDensity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Leray.Reality
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Realizability.Bridge
import Mathlib.Tactic

/-!
# Reality-compatible transverse cutoff of the full complex H³ flux

At the honest complex Fourier-polarization level, the quadratic transverse
numerator N_ξ(A) = (ξ·ξ) A - (ξ·A) ξ commutes with the anti-linear
Hermitian reflection (ξ,A) ↦ (-ξ,conj A). Multiplication by any real,
even scalar cutoff preserves this Hermitian symmetry AND exact frequency
solenoidality. Therefore the full six-orbit equals the uncorrected sixth-
power flux on each momentum-conserving triad of these cutoff profiles.

At the actual weighted Fourier L² layer, we also reuse the previously proven
Leray reality theorem: projecting a raw-Hermitian spectral Schwartz input
produces a divergence-free, raw-Hermitian and real-decodable L² state, with the
same quantitative H³ approximation estimate.

The cutoff profile theorems are *pointwise algebraic*: they do not claim that
arbitrary cutoff functions are smooth or that their profiles are Schwartz.
The spectral theorem is conditional on raw-Hermitian input Schwartz density;
that density and annular Schwartz realization are the next analytic tasks.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Filter Topology
open scoped BigOperators SchwartzMap ComplexConjugate

noncomputable section
set_option maxHeartbeats 1800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := H3FourierPoint3

noncomputable local instance axisFintypeHermitianTransverseCutoff244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The real Fourier square radius is unchanged by frequency reflection. -/
private theorem thirdFullAxisSquare_reflected244 (ξ : A3 → ℝ) :
    thirdTriadAxisDot244 (fun i => -ξ i) (fun i => -ξ i) =
      thirdTriadAxisDot244 ξ ξ := by
  unfold thirdTriadAxisDot244
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A real scalar, viewed in the complex Fourier coefficient field, is
fixed by conjugation. Keep this as an atomic rewrite: expanding the complex
star operation inside nested sums can exceed the elaborator recursion limit. -/
private theorem thirdFullConjRealCast244 (t : ℝ) :
    (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := by
  simpa only [starRingEnd_apply] using (Complex.conj_ofReal t)

/-- Reflection of a real frequency and conjugation of a complex polarization
anti-commute with the complex-bilinear frequency contraction. -/
private theorem thirdFullMixedDot_reflectedConj244
    (ξ : A3 → ℝ) (A : A3 → ℂ) :
    mixedDot (fun i => -ξ i) (fun i => star (A i)) =
      -star (mixedDot ξ A) := by
  change (∑ i : A3, ((-ξ i : ℝ) : ℂ) * star (A i)) =
    - (starRingEnd ℂ) (∑ i : A3, (ξ i : ℂ) * A i)
  simp only [Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, thirdFullConjRealCast244 (ξ i)]
  rfl

/-- The *actual complex* transverse polynomial preserves conjugate-reflection
reality, not just the real-polarization special case. -/
theorem thirdFullComplexTransverseNumerator_reality244
    (ξ : A3 → ℝ) (A : A3 → ℂ) :
    thirdFullComplexTransverseNumerator244 (fun i => -ξ i)
        (fun i => star (A i)) =
      fun i => star (thirdFullComplexTransverseNumerator244 ξ A i) := by
  funext i
  change
    (thirdTriadAxisDot244 (fun j => -ξ j) (fun j => -ξ j) : ℂ) *
        star (A i) -
      mixedDot (fun j => -ξ j) (fun j => star (A j)) *
        ((-ξ i : ℝ) : ℂ) =
      (starRingEnd ℂ)
        ((thirdTriadAxisDot244 ξ ξ : ℂ) * A i -
          mixedDot ξ A * (ξ i : ℂ))
  rw [thirdFullAxisSquare_reflected244,
    thirdFullMixedDot_reflectedConj244]
  rw [map_sub, map_mul, map_mul,
    thirdFullConjRealCast244 (thirdTriadAxisDot244 ξ ξ),
    thirdFullConjRealCast244 (ξ i), Complex.ofReal_neg]
  -- The two negatives come from reflecting both frequency factors.
  -- They cancel without commuting either complex scalar product.
  simp only [neg_mul_neg, starRingEnd_apply]

/-- A Hermitian complex-polarization profile on the real axis carrier. -/
def H3ComplexHermitianPolarizationProfile244
    (U : (A3 → ℝ) → (A3 → ℂ)) : Prop :=
  ∀ ξ, U (fun i => -ξ i) = fun j => star (U ξ j)

/-- Localize the exact transverse polynomial with any real frequency cutoff.
Smoothness, support and boundedness are NOT implicit in this definition. -/
noncomputable def thirdFullComplexCutoffTransverseProfile244
    (χ : (A3 → ℝ) → ℝ) (U : (A3 → ℝ) → (A3 → ℂ))
    (ξ : A3 → ℝ) (j : A3) : ℂ :=
  (χ ξ : ℂ) * thirdFullComplexTransverseNumerator244 ξ (U ξ) j

/-- Scalar localization never reintroduces Fourier divergence, even when the
cutoff is not smooth or the original complex profile is not solenoidal. -/
theorem thirdFullComplexCutoffTransverseProfile_divergence244
    (χ : (A3 → ℝ) → ℝ) (U : (A3 → ℝ) → (A3 → ℂ))
    (ξ : A3 → ℝ) :
    mixedDot ξ (thirdFullComplexCutoffTransverseProfile244 χ U ξ) = 0 := by
  calc
    mixedDot ξ (thirdFullComplexCutoffTransverseProfile244 χ U ξ) =
        (χ ξ : ℂ) *
          mixedDot ξ (thirdFullComplexTransverseNumerator244 ξ (U ξ)) := by
      unfold mixedDot thirdFullComplexCutoffTransverseProfile244
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by
      rw [thirdFullComplexTransverseNumerator_divergence244]
      ring

/-- A real even Fourier cutoff and the complex transverse numerator retain
exact pointwise Hermitian reality. This is the required algebra for real
inverse-Fourier Schwartz packets once compact smooth density is established. -/
theorem thirdFullComplexCutoffTransverseProfile_reality244
    (χ : (A3 → ℝ) → ℝ) (U : (A3 → ℝ) → (A3 → ℂ))
    (hχ : ∀ ξ, χ (fun i => -ξ i) = χ ξ)
    (hU : H3ComplexHermitianPolarizationProfile244 U) :
    H3ComplexHermitianPolarizationProfile244
      (thirdFullComplexCutoffTransverseProfile244 χ U) := by
  intro ξ
  funext i
  change
    (χ (fun j => -ξ j) : ℂ) *
        thirdFullComplexTransverseNumerator244 (fun j => -ξ j)
          (U (fun j => -ξ j)) i =
      (starRingEnd ℂ)
        ((χ ξ : ℂ) * thirdFullComplexTransverseNumerator244 ξ (U ξ) i)
  rw [hχ ξ, hU ξ]
  have hN := congrFun
    (thirdFullComplexTransverseNumerator_reality244 ξ (U ξ)) i
  rw [hN]
  rw [map_mul, thirdFullConjRealCast244 (χ ξ)]
  rfl

/-- The localized profile vanishes wherever its scalar window vanishes.
Thus the transverse operation cannot enlarge frequency support. -/
theorem thirdFullComplexCutoffTransverseProfile_zero_of_cutoff_zero244
    (χ : (A3 → ℝ) → ℝ) (U : (A3 → ℝ) → (A3 → ℂ))
    (ξ : A3 → ℝ) (hχ : χ ξ = 0) :
    thirdFullComplexCutoffTransverseProfile244 χ U ξ = fun _ => 0 := by
  funext i
  simp [thirdFullComplexCutoffTransverseProfile244, hχ]

/-- The polynomial localization is defined and vanishes at the origin,
regardless of the cutoff and the input profile. -/
theorem thirdFullComplexCutoffTransverseProfile_at_zero244
    (χ : (A3 → ℝ) → ℝ) (U : (A3 → ℝ) → (A3 → ℂ)) :
    thirdFullComplexCutoffTransverseProfile244 χ U (fun _ => 0) =
      fun _ => 0 := by
  funext i
  simp [thirdFullComplexCutoffTransverseProfile244,
    thirdFullComplexTransverseNumerator_at_zero244]

/-- The longitudinal defect vanishes identically on every frequency triad of
cutoff-projected profiles, without assumptions on the input polarizations. -/
theorem thirdFullComplexCutoffTransverseProfile_defect_zero244
    (χ : (A3 → ℝ) → ℝ) (U : (A3 → ℝ) → (A3 → ℂ))
    (p q r : A3 → ℝ) :
    thirdFullComplexLongitudinalFluxDefect244 p q r
      (thirdFullComplexCutoffTransverseProfile244 χ U p)
      (thirdFullComplexCutoffTransverseProfile244 χ U q)
      (thirdFullComplexCutoffTransverseProfile244 χ U r) = 0 := by
  exact thirdFullComplexLongitudinalFluxDefect_zero_of_solenoidal244
    p q r _ _ _
    (thirdFullComplexCutoffTransverseProfile_divergence244 χ U p)
    (thirdFullComplexCutoffTransverseProfile_divergence244 χ U q)
    (thirdFullComplexCutoffTransverseProfile_divergence244 χ U r)

/-- On every momentum-conserving triad the complete full-third six-symbol
therefore equals its UNCORRECTED sixth-power radial flux, after real cutoff
and transverse projection. No angular or frequency restrictions are hidden. -/
theorem thirdFullComplexCutoffTransverseProfile_six_eq_flux244
    (χ : (A3 → ℝ) → ℝ) (U : (A3 → ℝ) → (A3 → ℂ))
    (p q r : A3 → ℝ)
    (hm : ∀ i, p i + q i + r i = 0) :
    thirdFullComplexSixSymbol244 p q r
      (thirdFullComplexCutoffTransverseProfile244 χ U p)
      (thirdFullComplexCutoffTransverseProfile244 χ U q)
      (thirdFullComplexCutoffTransverseProfile244 χ U r) =
    thirdFullComplexSixthPowerFlux244 p q r
      (thirdFullComplexCutoffTransverseProfile244 χ U p)
      (thirdFullComplexCutoffTransverseProfile244 χ U q)
      (thirdFullComplexCutoffTransverseProfile244 χ U r) := by
  rw [thirdFullComplexSix_eq_flux_add_longitudinal244 p q r _ _ _ hm]
  rw [thirdFullComplexCutoffTransverseProfile_defect_zero244]
  all_goals ring

/-- The previously constructed bounded spectral Leray projection also
preserves the exact deweighted Fourier-reality constraint. -/
theorem h3SchwartzSpectralLerayState_realSolenoidal244
    (Phi : Fin 3 → SchwartzMap V3 ℂ)
    (hPhi : H3SpectralVelocityRawHermitian
      (h3SchwartzSpectralVelocityRealization244 Phi)) :
    H3SpectralFinDivergenceFree (h3SchwartzSpectralLerayState244 Phi) ∧
    H3SpectralVelocityRawHermitian (h3SchwartzSpectralLerayState244 Phi) ∧
    H3SpectralVelocityRealizable (h3SchwartzSpectralLerayState244 Phi) := by
  have hReal : H3SpectralVelocityRawHermitian
      (h3SchwartzSpectralLerayState244 Phi) :=
    h3SpectralFinLerayApply_preserves_rawHermitian hPhi
  exact ⟨h3SchwartzSpectralLerayState_divergenceFree244 Phi,
    hReal, h3SpectralVelocityRawHermitian_realizable hReal⟩

/-- Quantitative real-solenoidal approximation for any raw-Hermitian input
Schwartz spectrum and solenoidal target. The existence of inputs with BOTH
properties is intentionally not assumed as a density theorem here. -/
theorem h3SchwartzSpectralLerayState_realError_le244
    (U : H3SpectralVelocityState)
    (hU : H3SpectralFinDivergenceFree U)
    (Phi : Fin 3 → SchwartzMap V3 ℂ)
    (hPhi : H3SpectralVelocityRawHermitian
      (h3SchwartzSpectralVelocityRealization244 Phi)) :
    ‖U - h3SchwartzSpectralLerayState244 Phi‖ ≤
      6 * ‖U - h3SchwartzSpectralVelocityRealization244 Phi‖ ∧
    H3SpectralFinDivergenceFree (h3SchwartzSpectralLerayState244 Phi) ∧
    H3SpectralVelocityRawHermitian (h3SchwartzSpectralLerayState244 Phi) ∧
    H3SpectralVelocityRealizable (h3SchwartzSpectralLerayState244 Phi) := by
  exact ⟨h3SchwartzSpectralLerayState_error_le244 U hU Phi,
    h3SchwartzSpectralLerayState_realSolenoidal244 Phi hPhi⟩

/-- A convergent Hermitian INPUT Schwartz sequence has a strongly convergent
real-solenoidal Leray image in the exact weighted H³ carrier. The reality
assumption is deliberately retained; arbitrary complex Schwartz density
alone is not enough to supply it. -/
theorem h3SchwartzSpectralLerayState_realSequence244
    (U : H3SpectralVelocityState)
    (hU : H3SpectralFinDivergenceFree U)
    (Phi : ℕ → Fin 3 → SchwartzMap V3 ℂ)
    (hPhi : ∀ n, H3SpectralVelocityRawHermitian
      (h3SchwartzSpectralVelocityRealization244 (Phi n)))
    (hTendsto : Tendsto
      (fun n => h3SchwartzSpectralVelocityRealization244 (Phi n))
      atTop (𝓝 U)) :
    Tendsto (fun n => h3SchwartzSpectralLerayState244 (Phi n))
        atTop (𝓝 U) ∧
    CauchySeq (fun n => h3SchwartzSpectralLerayState244 (Phi n)) ∧
    (∀ n, H3SpectralFinDivergenceFree
        (h3SchwartzSpectralLerayState244 (Phi n)) ∧
      H3SpectralVelocityRawHermitian
        (h3SchwartzSpectralLerayState244 (Phi n)) ∧
      H3SpectralVelocityRealizable
        (h3SchwartzSpectralLerayState244 (Phi n))) := by
  have hFixed : h3SpectralFinLerayApply U = U :=
    h3SpectralFinLerayApply_eq_of_divergenceFree hU
  have hProjected : Tendsto
      (fun n => h3SchwartzSpectralLerayState244 (Phi n))
      atTop (𝓝 (h3SpectralFinLerayApply U)) :=
    (continuous_h3SpectralFinLerayApply.tendsto U).comp hTendsto
  rw [hFixed] at hProjected
  exact ⟨hProjected, hProjected.cauchySeq,
    fun n => h3SchwartzSpectralLerayState_realSolenoidal244 (Phi n) (hPhi n)⟩

end
end PrimeTensor.FirstMonomialTriad
