import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterEvenWindow
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Global noncancellation of the weighted sharp quarter-scale triad

The width-dependent even window was constructed in the preceding module.
The signed six-order trilinear kernel of that ACTUAL windowed Schwartz field
is positive on every triple of nonzero window weights for a sufficiently
small width, and zero whenever a weight vanishes.

Here the kernel is shown to be continuous and compactly supported on the
six-dimensional momentum plane. Consequently it is integrable. Its
pointwise nonnegativity, together with strict positivity at the sharp
resonant pair and the positivity of the ambient volume measure on nonempty
open sets, gives a strictly positive FULL Fourier integral.

This is a noncancellation statement for one particular polynomial Fourier
symbol on an explicit divergence-free Hermitian Schwartz field. It is not a
Navier--Stokes singularity or global-regularity theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory Metric Set Filter
open scoped Topology SchwartzMap

noncomputable section

private abbrev IntegralV := Fin 3 → ℝ
private abbrev IntegralPair := IntegralV × IntegralV

/-- The signed six-order kernel of the actual windowed Schwartz field is
continuous on the whole product of the two independent Fourier variables. -/
theorem lowNormalQuarterWindowedSignedKernel_continuous
    (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (lowNormalQuarterWeightedSignedKernel
      (lowNormalQuarterEvenWindow ρ hρ)) := by
  let w : IntegralV → ℝ := lowNormalQuarterEvenWindow ρ hρ
  have hw : Continuous w :=
    (lowNormalQuarterEvenWindow_contDiff ρ hρ).continuous
  have hp : Continuous (fun z : IntegralPair => z.1) := continuous_fst
  have hr : Continuous (fun z : IntegralPair => z.2) := continuous_snd
  have hq : Continuous (fun z : IntegralPair => middleFrequency z.1 z.2) := by
    change Continuous (fun z : IntegralPair =>
      fun d : Fin 3 => -(z.1 d + z.2 d))
    apply continuous_pi
    intro d
    exact (((continuous_apply d).comp hp).add
      ((continuous_apply d).comp hr)).neg
  have hProduct : Continuous (fun z : IntegralPair =>
      w z.1 * w (middleFrequency z.1 z.2) * w z.2 *
        lowNormalQuarterSignedKernel z) :=
    (((hw.comp hp).mul (hw.comp hq)).mul (hw.comp hr)).mul
      lowNormalQuarterSignedKernel_continuous
  have hEq : lowNormalQuarterWeightedSignedKernel w =
      (fun z : IntegralPair =>
        w z.1 * w (middleFrequency z.1 z.2) * w z.2 *
          lowNormalQuarterSignedKernel z) := by
    funext z
    rcases z with ⟨p, r⟩
    exact lowNormalQuarterWeightedSignedKernel_eq w p r
  change Continuous (lowNormalQuarterWeightedSignedKernel w)
  rw [hEq]
  exact hProduct

/-- The signed kernel has compact support in SIX dimensions. Although its
middle-frequency factor depends on both variables, the first and third
window weights already trap the support in a compact product set. -/
theorem lowNormalQuarterWindowedSignedKernel_hasCompactSupport
    (ρ : ℝ) (hρ : 0 < ρ) :
    HasCompactSupport (lowNormalQuarterWeightedSignedKernel
      (lowNormalQuarterEvenWindow ρ hρ)) := by
  let w : IntegralV → ℝ := lowNormalQuarterEvenWindow ρ hρ
  let K : Set IntegralV := tsupport w
  have hK : IsCompact K :=
    lowNormalQuarterEvenWindow_hasCompactSupport ρ hρ
  change HasCompactSupport (lowNormalQuarterWeightedSignedKernel w)
  apply HasCompactSupport.intro (K := K ×ˢ K) (hK.prod hK)
  intro z hz
  rcases z with ⟨p, r⟩
  have hEither : p ∉ K ∨ r ∉ K := by
    by_cases hp : p ∈ K
    · right
      intro hr
      exact hz ⟨hp, hr⟩
    · exact Or.inl hp
  rcases hEither with hp | hr
  · have hwp : w p = 0 := image_eq_zero_of_notMem_tsupport hp
    exact lowNormalQuarterWeightedSignedKernel_zero_of_factor_zero
      w p r (Or.inl hwp)
  · have hwr : w r = 0 := image_eq_zero_of_notMem_tsupport hr
    exact lowNormalQuarterWeightedSignedKernel_zero_of_factor_zero
      w p r (Or.inr (Or.inr hwr))

/-- Compact support and continuity yield global Bochner integrability of
the REAL signed six-permutation Fourier coefficient. -/
theorem lowNormalQuarterWindowedSignedKernel_integrable
    (ρ : ℝ) (hρ : 0 < ρ) :
    Integrable (lowNormalQuarterWeightedSignedKernel
      (lowNormalQuarterEvenWindow ρ hρ)) (volume.prod volume) :=
  (lowNormalQuarterWindowedSignedKernel_continuous ρ hρ).integrable_of_hasCompactSupport
    (lowNormalQuarterWindowedSignedKernel_hasCompactSupport ρ hρ)

/-- A width with strictly positive kernel whenever all three window factors
are nonzero yields pointwise global nonnegativity. The remaining cases
are zero by the exact scalar triple-product identity. -/
theorem lowNormalQuarterWindowedSignedKernel_nonneg_of_positive_triples
    (ρ : ℝ) (hρ : 0 < ρ)
    (hTrip : ∀ p r : IntegralV,
      lowNormalQuarterEvenWindow ρ hρ p ≠ 0 →
      lowNormalQuarterEvenWindow ρ hρ (middleFrequency p r) ≠ 0 →
      lowNormalQuarterEvenWindow ρ hρ r ≠ 0 →
      0 < lowNormalQuarterWeightedSignedKernel
        (lowNormalQuarterEvenWindow ρ hρ) (p, r)) :
    ∀ z : IntegralPair,
      0 ≤ lowNormalQuarterWeightedSignedKernel
        (lowNormalQuarterEvenWindow ρ hρ) z := by
  let w : IntegralV → ℝ := lowNormalQuarterEvenWindow ρ hρ
  rintro ⟨p, r⟩
  change 0 ≤ lowNormalQuarterWeightedSignedKernel w (p, r)
  by_cases hp : w p = 0
  · have hZero := lowNormalQuarterWeightedSignedKernel_zero_of_factor_zero
        w p r (Or.inl hp)
    rw [hZero]
  by_cases hq : w (middleFrequency p r) = 0
  · have hZero := lowNormalQuarterWeightedSignedKernel_zero_of_factor_zero
        w p r (Or.inr (Or.inl hq))
    rw [hZero]
  by_cases hr : w r = 0
  · have hZero := lowNormalQuarterWeightedSignedKernel_zero_of_factor_zero
        w p r (Or.inr (Or.inr hr))
    rw [hZero]
  exact (hTrip p r hp hq hr).le

/-- Unconditional noncancellation: an explicit even-windowed, real-compatible,
solenoidal Schwartz Fourier field has a strictly POSITIVE integrated full
six-permutation first-monomial coefficient on the entire momentum plane. -/
theorem lowNormalQuarterEvenWindow_exists_positive_full_sixOrder_integral :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      ρ ≤ lowNormalSixCenterSeparationRadius (1 / 4 : ℝ) ∧
      0 < ∫ z : IntegralPair,
        lowNormalQuarterWeightedSignedKernel
          (lowNormalQuarterEvenWindow ρ hρ) z ∂(volume.prod volume) := by
  obtain ⟨ρ, hρ, hSmall, hTrip⟩ :=
    lowNormalQuarterEvenWindow_exists_positive_kernel_on_triples
  refine ⟨ρ, hρ, hSmall, ?_⟩
  let w : IntegralV → ℝ := lowNormalQuarterEvenWindow ρ hρ
  let f : IntegralPair → ℝ := lowNormalQuarterWeightedSignedKernel w
  have hCont : Continuous f :=
    lowNormalQuarterWindowedSignedKernel_continuous ρ hρ
  have hInt : Integrable f (volume.prod volume) :=
    lowNormalQuarterWindowedSignedKernel_integrable ρ hρ
  have hPointwise : ∀ z : IntegralPair, 0 ≤ f z :=
    lowNormalQuarterWindowedSignedKernel_nonneg_of_positive_triples ρ hρ hTrip
  have hNonneg : 0 ≤ᵐ[volume.prod volume] f :=
    Filter.Eventually.of_forall hPointwise
  have hCenter : f
      (lowNormalAuditP, lowNormalAuditR (1 / 4 : ℝ)) ≠ 0 :=
    ne_of_gt (lowNormalQuarterEvenWindow_weightedKernel_pos_at_center ρ hρ)
  have hMeasure :
      0 < (volume.prod volume) (Function.support f) :=
    hCont.isOpen_support.measure_pos (volume.prod volume) ⟨_, hCenter⟩
  exact (integral_pos_iff_support_of_nonneg_ae hNonneg hInt).2 hMeasure

/-- The full signed Fourier integral in the preceding theorem is nonzero. -/
theorem lowNormalQuarterEvenWindow_exists_nonzero_full_sixOrder_integral :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      (∫ z : IntegralPair,
        lowNormalQuarterWeightedSignedKernel
          (lowNormalQuarterEvenWindow ρ hρ) z ∂(volume.prod volume)) ≠ 0 := by
  obtain ⟨ρ, hρ, _, hPos⟩ :=
    lowNormalQuarterEvenWindow_exists_positive_full_sixOrder_integral
  exact ⟨ρ, hρ, ne_of_gt hPos⟩

end
end PrimeTensor.FirstMonomialTriad
