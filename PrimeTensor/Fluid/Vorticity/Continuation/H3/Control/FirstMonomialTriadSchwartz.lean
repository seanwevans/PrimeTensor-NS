import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Schwartz integrability of the first-monomial triad kernel

Expand the kernel into coordinate monomials. Each term is a product of
Schwartz functions at p, r and -(p+r). The first two factors are integrable;
the third is bounded. No incompressibility is needed for integrability.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory
open scoped BigOperators SchwartzMap

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Multiplication of a scalar Schwartz amplitude by one frequency coordinate. -/
def coordinateSchwartz (i : ι) (f : 𝓢(ι → ℝ, ℂ)) : 𝓢(ι → ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun p : ι → ℝ => p i) f

@[simp] theorem coordinateSchwartz_apply (i : ι) (f : 𝓢(ι → ℝ, ℂ))
    (p : ι → ℝ) : coordinateSchwartz i f p = (p i : ℂ) * f p := by
  have hg : (fun p : ι → ℝ => p i).HasTemperateGrowth :=
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasTemperateGrowth
  simp [coordinateSchwartz, SchwartzMap.smulLeftCLM_apply_apply hg,
    Complex.real_smul]

variable (μ : Measure (ι → ℝ)) [SFinite μ] [μ.HasTemperateGrowth]

/-- Two independent L1 factors and a bounded Schwartz factor on the triad plane. -/
theorem schwartz_triple_integrable (f g h : 𝓢(ι → ℝ, ℂ)) :
    Integrable (fun z : (ι → ℝ) × (ι → ℝ) =>
      (f z.1 * g z.2) * h (middleFrequency z.1 z.2)) (μ.prod μ) := by
  have hf : Integrable f μ := f.integrable
  have hg : Integrable g μ := g.integrable
  have hbound := (hf.norm.mul_prod hg.norm).mul_const (SchwartzMap.seminorm ℝ 0 0 h)
  apply hbound.mono' ?_ (Filter.Eventually.of_forall ?_)
  · apply Continuous.aestronglyMeasurable
    have hmiddle : Continuous (fun z : (ι → ℝ) × (ι → ℝ) =>
        middleFrequency z.1 z.2) := by
      change Continuous (fun z : (ι → ℝ) × (ι → ℝ) => -(z.1 + z.2))
      fun_prop
    exact ((f.continuous.comp continuous_fst).mul
      (g.continuous.comp continuous_snd)).mul (h.continuous.comp hmiddle)
  · intro z
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ h _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Coordinate expansion arranged by the two independent outer frequencies. -/
theorem amplitudeKernel_eq_coordinate_sum (U : (ι → ℝ) → (ι → ℂ))
    (z : (ι → ℝ) × (ι → ℝ)) :
    amplitudeKernel U z =
      ∑ i, ∑ k, ∑ l, ∑ v, ∑ j,
        (((z.1 i : ℂ) * (z.1 k : ℂ) * (z.1 l : ℂ) * U z.1 j) *
          ((z.2 i : ℂ) * (z.2 v : ℂ) * U z.2 j)) *
        (((middleFrequency z.1 z.2 k : ℝ) : ℂ) *
          ((middleFrequency z.1 z.2 l : ℝ) : ℂ) *
          U (middleFrequency z.1 z.2) v) := by
  classical
  symm
  calc
    _ = ∑ i, ∑ k, ∑ l, ∑ v, ∑ j,
        ((z.1 i : ℂ) * (z.2 i : ℂ)) *
        (((z.1 k : ℂ) * (middleFrequency z.1 z.2 k : ℂ)) *
        (((z.1 l : ℂ) * (middleFrequency z.1 z.2 l : ℂ)) *
        (((z.2 v : ℂ) * U (middleFrequency z.1 z.2) v) *
        (U z.1 j * U z.2 j)))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = amplitudeKernel U z := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      unfold amplitudeKernel complexCoefficient mixedDot amplitudeDot dot
      push_cast
      ring

/-- Schwartz regularity discharges the complex integral theorem's L1 premise. -/
theorem amplitudeKernel_integrable_schwartz (U : ι → 𝓢(ι → ℝ, ℂ)) :
    Integrable (amplitudeKernel (fun p i => U i p)) (μ.prod μ) := by
  classical
  have hterm (i k l v j : ι) := schwartz_triple_integrable μ
    (coordinateSchwartz i (coordinateSchwartz k (coordinateSchwartz l (U j))))
    (coordinateSchwartz i (coordinateSchwartz v (U j)))
    (coordinateSchwartz k (coordinateSchwartz l (U v)))
  have hsum : Integrable (fun z : (ι → ℝ) × (ι → ℝ) =>
      ∑ i, ∑ k, ∑ l, ∑ v, ∑ j,
        (((z.1 i : ℂ) * (z.1 k : ℂ) * (z.1 l : ℂ) * U j z.1) *
          ((z.2 i : ℂ) * (z.2 v : ℂ) * U j z.2)) *
        ((middleFrequency z.1 z.2 k : ℂ) *
          (middleFrequency z.1 z.2 l : ℂ) * U v (middleFrequency z.1 z.2)))
      (μ.prod μ) := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro k _
    apply integrable_finsetSum
    intro l _
    apply integrable_finsetSum
    intro v _
    apply integrable_finsetSum
    intro j _
    simpa only [coordinateSchwartz_apply, mul_assoc] using hterm i k l v j
  exact hsum.congr (Filter.Eventually.of_forall (fun z =>
    (amplitudeKernel_eq_coordinate_sum (fun p i => U i p) z).symm))

theorem shellKernel_integrable_schwartz (U : ι → 𝓢(ι → ℝ, ℂ))
    (hDivergence : ∀ q, mixedDot q (fun i => U i q) = 0) :
    Integrable (shellKernel (fun p i => U i p)) (μ.prod μ) :=
  shellKernel_integrable μ _ hDivergence (amplitudeKernel_integrable_schwartz μ U)

/-- Integrated cancellation with no additional kernel-integrability hypothesis. -/
theorem integral_shellKernel_eq_twice_schwartz (U : ι → 𝓢(ι → ℝ, ℂ))
    (hDivergence : ∀ q, mixedDot q (fun i => U i q) = 0) :
    (∫ z, shellKernel (fun p i => U i p) z ∂μ.prod μ) =
      2 * ∫ z, amplitudeKernel (fun p i => U i p) z ∂μ.prod μ :=
  integral_shellKernel_eq_twice μ _ hDivergence (amplitudeKernel_integrable_schwartz μ U)

end
end PrimeTensor.FirstMonomialTriad
