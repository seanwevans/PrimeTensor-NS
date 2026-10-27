import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECriticalWidthSourceEscape244
import Mathlib.Tactic

/-!
# Projected PDE source ceilings versus the actual physical source

The previous conditional width-cap theorem forces C(v k)^2 → +∞, where C
is the nonnegative *chosen upper ceiling* for the projected source over a
strict-time window. An arbitrary upper ceiling can grow although the actual
source is small. The escape theorem does NOT automatically imply growth of
‖Laplacian(u) - Leray(u ⊗ u)‖ at the snapshot time.

Here we isolate the exact missing ceiling-efficiency condition. With a fixed
additive overhead on |C| relative to the actual physical projected source,
forced coefficient growth implies physical source-norm growth. Conversely,
if that norm stays bounded, the ceiling's slack must diverge. The physical
conclusions are *conditional* on both the earlier clock regime and the
respective extra efficiency/bounded-source hypothesis.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Divergence of the square of a real-valued chosen source ceiling entails
divergence of its absolute value; no sign restriction is needed. -/
theorem h3Path_sourceCeilingSquareEscape_forces_absEscape244
    (C : ℕ → ℝ)
    (hSquare : Tendsto (fun k : ℕ => C k ^ 2) atTop atTop) :
    Tendsto (fun k : ℕ => |C k|) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro A
  let B : ℝ := max A 0 + 1
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hMax : (0 : ℝ) ≤ max A 0 := le_max_right _ _
    linarith only [hMax]
  have hAB : A ≤ B := by
    dsimp only [B]
    have hMax : A ≤ max A 0 := le_max_left _ _
    linarith only [hMax]
  have hLarge : ∀ᶠ k : ℕ in atTop, B ^ 2 ≤ C k ^ 2 :=
    hSquare.eventually (eventually_ge_atTop (B ^ 2))
  filter_upwards [hLarge] with k hk
  have hAbsNonneg : 0 ≤ |C k| := abs_nonneg _
  have hAbsSq : |C k| ^ 2 = C k ^ 2 := sq_abs (C k)
  have hLargeAbs : B ^ 2 ≤ |C k| ^ 2 := by
    rw [hAbsSq]
    exact hk
  have hCompare : B ≤ |C k| := by
    by_contra hNot
    have hLess : |C k| < B := lt_of_not_ge hNot
    nlinarith only [hB, hAbsNonneg, hLess, hLargeAbs]
  exact hAB.trans hCompare

/-- An efficiently chosen ceiling (bounded additive slack) transmits its
escape to the actual measured source norm. The overhead E need not be zero. -/
theorem h3Path_efficientSourceCeiling_forces_actualNormEscape244
    (C source : ℕ → ℝ) (E : ℝ)
    (hSquare : Tendsto (fun k : ℕ => C k ^ 2) atTop atTop)
    (hEfficient : ∀ᶠ k : ℕ in atTop, |C k| ≤ source k + E) :
    Tendsto source atTop atTop := by
  have hAbs := h3Path_sourceCeilingSquareEscape_forces_absEscape244
    C hSquare
  apply Filter.tendsto_atTop.2
  intro A
  have hLarge : ∀ᶠ k : ℕ in atTop, A + E + 1 ≤ |C k| :=
    hAbs.eventually (eventually_ge_atTop (A + E + 1))
  filter_upwards [hLarge, hEfficient] with k hk hEff
  linarith only [hk, hEff]

/-- If the actual source remains uniformly bounded but the chosen ceiling
square diverges, then the *inefficiency* of that ceiling must diverge.
No actual source-norm blowup is inferred. -/
theorem h3Path_boundedActualSource_forces_ceilingSlackEscape244
    (C source : ℕ → ℝ) (E : ℝ)
    (hSquare : Tendsto (fun k : ℕ => C k ^ 2) atTop atTop)
    (hBound : ∀ᶠ k : ℕ in atTop, source k ≤ E) :
    Tendsto (fun k : ℕ => |C k| - source k) atTop atTop := by
  have hAbs := h3Path_sourceCeilingSquareEscape_forces_absEscape244
    C hSquare
  apply Filter.tendsto_atTop.2
  intro A
  have hLarge : ∀ᶠ k : ℕ in atTop, A + E + 1 ≤ |C k| :=
    hAbs.eventually (eventually_ge_atTop (A + E + 1))
  filter_upwards [hLarge, hBound] with k hk hSource
  linarith only [hk, hSource]

/-- The existing cofinal physical width-cap source-ceiling escape is now
separated into its two legitimate interpretations:

* with bounded additive ceiling overhead, the actual physical Hilbert-L²
  projected source diverges at the same selected snapshot times;
* with bounded actual projected-source norm, the chosen ceiling's slack
  diverges instead.

No minimality/tightness of C is asserted by H³ path admissibility. -/
theorem h3Path_noL2Trace_widthCap_sourceCeilingEfficiencyAlternative244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v m : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k, v k ≤ m k ∧ m k < N (v k) ∧
        0 < h3PathActualBandRawKineticMass244
          ((m k : ℝ) + 1) ((m k : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ η B D E : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            D * (((v k : ℝ) + 1) ^ 9)) →
        (∀ᶠ k : ℕ in atTop,
          |C (v k)| ≤
            ‖h3PathActualProjectedMomentumSource244 hH3 (τ (v k))‖ + E) →
        Tendsto (fun k : ℕ =>
          ‖h3PathActualProjectedMomentumSource244 hH3 (τ (v k))‖)
          atTop atTop) ∧
      (∀ η B D E : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            D * (((v k : ℝ) + 1) ^ 9)) →
        (∀ᶠ k : ℕ in atTop,
          ‖h3PathActualProjectedMomentumSource244 hH3 (τ (v k))‖ ≤ E) →
        Tendsto (fun k : ℕ =>
          |C (v k)| -
            ‖h3PathActualProjectedMomentumSource244 hH3 (τ (v k))‖)
          atTop atTop) := by
  obtain ⟨τ, N, K, C, δ, v, m, hv, hCofinal, hTime,
      hSeparate, hSummable, hSelected, hEscape⟩ :=
    h3Path_noL2Trace_finiteDissipation_widthCap_sourceSquareEscape244
      hH3 hClass hMass hNoTrace hDInt
  let coeff : ℕ → ℝ := fun k => C (v k)
  let source : ℕ → ℝ := fun k =>
    ‖h3PathActualProjectedMomentumSource244 hH3 (τ (v k))‖
  refine ⟨τ, N, K, C, δ, v, m, hv, hCofinal, hTime,
    hSeparate, hSummable, hSelected, ?_, ?_⟩
  · intro η B D E hη hB hD hRegime hEff
    have hSquare : Tendsto (fun k : ℕ => coeff k ^ 2) atTop atTop := by
      simpa only [coeff] using hEscape η B D hη hB hD hRegime
    have hEff' : ∀ᶠ k : ℕ in atTop, |coeff k| ≤ source k + E := by
      simpa only [coeff, source] using hEff
    have hResult := h3Path_efficientSourceCeiling_forces_actualNormEscape244
      coeff source E hSquare hEff'
    simpa only [source] using hResult
  · intro η B D E hη hB hD hRegime hBound
    have hSquare : Tendsto (fun k : ℕ => coeff k ^ 2) atTop atTop := by
      simpa only [coeff] using hEscape η B D hη hB hD hRegime
    have hBound' : ∀ᶠ k : ℕ in atTop, source k ≤ E := by
      simpa only [source] using hBound
    have hResult := h3Path_boundedActualSource_forces_ceilingSlackEscape244
      coeff source E hSquare hBound'
    simpa only [coeff, source] using hResult

end
end PrimeTensor.FirstMonomialTriad
