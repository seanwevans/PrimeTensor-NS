import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudgetPDERates244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDESourceGainSplit244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEQuadraticSharpJointBarrier244
import Mathlib.Tactic

/-!
# Physical projected-source gain in higher-budget canonical exact clocks

No extra selected anchor, source ceiling or energy bound is introduced.
The source C is the attained maximum of the actual projected physical
momentum source on each original half-terminal interval, and the canonical
spectral coefficient K is its actual Fourier H³ norm. For every fixed radial
order m admitting a real integrable upper envelope of the top moment, the
higher-budget three-scale rate alternative becomes an exact four-way split:
source peak, terminal compression, source-linear cutoff gain, or
source-quadratic cutoff gain. No bound on the two gains is asserted.

A separate scalar lemma bounds the square of a physical linear rate by
actual H³ energy and the square of the actual projected-source ceiling,
subject to the physically necessary inner/outer radial ordering.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- The existing physical linear PDE clock rate is exactly linear in the
attained projected momentum source, with the original Fourier anchor K. -/
theorem h3Path_higherBudget_linearRate_eq_sourceGain244
    (R Q K C : ℝ) :
    h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C =
      C * h3PathFiniteAnnulusPDELinearGain244 R Q K := by
  unfold h3PathFiniteAnnulusPDEVariationCoefficient244
    h3PathFiniteAnnulusPDELinearGain244
  ring

/-- An exact high-order PDE three-scale rate can be paid by a larger
ACTUAL projected-source ceiling, or by explicit linear/quadratic cutoff
gains at any proposed fixed source bound S. No gain ceiling is presumed. -/
theorem h3Path_scalar_higherBudget_sourceOrCutoffGain244
    (R Q K C S A B G ε : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hAlt : G ≤ ε ∨
      A ≤ 16 * ε *
        (h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C + 1) ∨
      B ≤ 16 * ε ^ 2 *
        (h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C + 1)) :
    S < C ∨ G ≤ ε ∨
      A ≤ 16 * ε *
        (S * h3PathFiniteAnnulusPDELinearGain244 R Q K + 1) ∨
      B ≤ 16 * ε ^ 2 *
        (S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q + 1) := by
  by_cases hBig : S < C
  · exact Or.inl hBig
  have hCS : C ≤ S := le_of_not_gt hBig
  have hGains := h3Path_finiteAnnulusPDEGains_nonneg244 R Q K hK
  have hCS2 : C ^ 2 ≤ S ^ 2 := (sq_le_sq₀ hC hS).2 hCS
  have hLinear :
      C * h3PathFiniteAnnulusPDELinearGain244 R Q K ≤
        S * h3PathFiniteAnnulusPDELinearGain244 R Q K :=
    mul_le_mul_of_nonneg_right hCS hGains.1
  have hQuadratic :
      C ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q ≤
        S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q :=
    mul_le_mul_of_nonneg_right hCS2 hGains.2
  rcases hAlt with hTime | hLin | hQuad
  · exact Or.inr (Or.inl hTime)
  · rw [h3Path_higherBudget_linearRate_eq_sourceGain244] at hLin
    have hAdd :
        C * h3PathFiniteAnnulusPDELinearGain244 R Q K + 1 ≤
          S * h3PathFiniteAnnulusPDELinearGain244 R Q K + 1 := by
      linarith only [hLinear]
    have hScale := mul_le_mul_of_nonneg_left hAdd
      (show 0 ≤ 16 * ε by positivity)
    exact Or.inr (Or.inr (Or.inl (hLin.trans hScale)))
  · rw [h3Path_quadraticSharpQuadraticRate_sourceSquaredGain244] at hQuad
    have hAdd :
        C ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q + 1 ≤
          S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q + 1 := by
      linarith only [hQuadratic]
    have hScale := mul_le_mul_of_nonneg_left hAdd
      (show 0 ≤ 16 * ε ^ 2 by positivity)
    exact Or.inr (Or.inr (Or.inr (hQuad.trans hScale)))

/-- Squaring a specified physical linear-rate branch gives a necessary
source-energy cost using the EXISTING 2304 physical coefficient estimate.
The 512 factor comes solely from (Lambda+1)^2 <= 2(Lambda^2+1). -/
theorem h3Path_scalar_higherLinearRate_forces_energySourceSquare244
    (R Q K C E A ε : ℝ)
    (hR : 0 ≤ R) (hRQ : R ≤ Q)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hKE : K ^ 2 ≤ E)
    (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hRate : A ≤ 16 * ε *
      (h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C + 1)) :
    A ^ 2 ≤ 512 * ε ^ 2 *
      (2304 * E * C ^ 2 * (Q + 1) ^ 10 + 1) := by
  let L : ℝ := h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C
  have hL : 0 ≤ L := by
    dsimp only [L]
    exact h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
      R Q K C hK hC
  have hRate' : A ≤ 16 * ε * (L + 1) := by
    simpa only [L] using hRate
  have hRHS : 0 ≤ 16 * ε * (L + 1) := by positivity
  have hSq : A ^ 2 ≤ (16 * ε * (L + 1)) ^ 2 :=
    (sq_le_sq₀ hA hRHS).2 hRate'
  have hTwo : (L + 1) ^ 2 ≤ 2 * (L ^ 2 + 1) := by
    nlinarith only [sq_nonneg (L - 1)]
  have hLSq : L ^ 2 ≤ 2304 * E * C ^ 2 * (Q + 1) ^ 10 := by
    dsimp only [L]
    exact h3Path_exactAnchor_PDELinearRate_sq_le_energySource244
      R Q K C E hR hRQ hK hC hKE
  calc
    A ^ 2 ≤ (16 * ε * (L + 1)) ^ 2 := hSq
    _ = 256 * ε ^ 2 * (L + 1) ^ 2 := by ring
    _ ≤ 256 * ε ^ 2 * (2 * (L ^ 2 + 1)) :=
      mul_le_mul_of_nonneg_left hTwo (by positivity)
    _ = 512 * ε ^ 2 * (L ^ 2 + 1) := by ring
    _ ≤ 512 * ε ^ 2 *
        (2304 * E * C ^ 2 * (Q + 1) ^ 10 + 1) := by
      have hAdd : L ^ 2 + 1 ≤
          2304 * E * C ^ 2 * (Q + 1) ^ 10 + 1 := by
        linarith only [hLSq]
      exact mul_le_mul_of_nonneg_left hAdd (by positivity)

/-- The ORIGINAL disjoint exact-anchor witnesses now identify the
higher-budget PDE-rate payment as an attained physical source peak, a
compressed terminal time, or an explicit linear/quadratic frequency gain.
In addition K^2 <= E_3 is proved for the very same actual Fourier anchor.
The higher-order spacetime envelope remains an explicit premise. -/
theorem h3Path_noL2Trace_exactAnchor_higherBudget_physicalSourceOrGain244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
    ∃ hτ : (∀ n, τ n ∈ Set.Ioo a T),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, K (v k) =
        ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        0 < δ (v k)) ∧
      (∀ k, K (v k) ^ 2 ≤ velocityH3EnergyAt u (τ (v k))) ∧
      (∀ m : ℕ, ∀ F : ℝ → ℝ,
        (∀ s : ℝ, 0 ≤ F s) →
        IntervalIntegrable F volume a T →
        (∀ s : ℝ, ∀ hs : s ∈ Set.Ioo a T,
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass m s hs ≤ ENNReal.ofReal (F s)) →
        ∀ S : ℝ, 0 ≤ S →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
          (∃ s : ℝ,
            s ∈ Set.Icc (τ (v k))
              (τ (v k) + (T - τ (v k)) / 2) ∧
            S < ‖h3PathActualProjectedMomentumSource244 hH3 s‖) ∨
          (((v k : ℝ) + 1) ^ (2 * m + 3)) *
            (((T - τ (v k)) / 2) / 2) ≤ ε ∨
          ((((v k : ℝ) + 1) ^ 2) ^ m) *
            (((v k : ℝ) + 1) ^ 6) ≤
              16 * ε *
                (S * h3PathFiniteAnnulusPDELinearGain244
                  ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
                  (K (v k)) + 1) ∨
          (((((v k : ℝ) + 1) ^ 2) ^ m) ^ 2) *
            (((v k : ℝ) + 1) ^ 9) ≤
              16 * ε ^ 2 *
                (S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244
                  ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) + 1)) := by
  obtain ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal, hSeparate,
      hCanonical, hRates⟩ :=
    h3Path_noL2Trace_exactAnchor_higherBudget_forces_physicalPDERates244
      hH3 hClass hMass hNoTrace hDInt
  have hEnergy (k : ℕ) :
      K (v k) ^ 2 ≤ velocityH3EnergyAt u (τ (v k)) := by
    rw [(hCanonical k).1]
    exact h3Path_actualSpectralAnchor_sq_le_physicalEnergy244
      hH3 (τ (v k))
      ⟨lt_trans hClass.terminal_start.1 (hτ (v k)).1, (hτ (v k)).2⟩
  have hPeak (k : ℕ) :
      ∃ s : ℝ,
        s ∈ Set.Icc (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 s‖ = C (v k) := by
    have ht := hτ (v k)
    have ht0 : 0 < τ (v k) := lt_trans hClass.terminal_start.1 ht.1
    have hMiddle : τ (v k) < τ (v k) + (T - τ (v k)) / 2 := by
      linarith only [ht.2]
    have hb : τ (v k) + (T - τ (v k)) / 2 < T := by
      linarith only [ht.2]
    obtain ⟨s, hs, _hMax, hEq⟩ :=
      h3Path_actualSourceWindowEnvelope_attained244
        hH3 ht0 hMiddle hb
    exact ⟨s, hs, (((hCanonical k).2.1).trans hEq).symm⟩
  have hKnonneg (k : ℕ) : 0 ≤ K (v k) := by
    rw [(hCanonical k).1]
    exact norm_nonneg _
  have hCnonneg (k : ℕ) : 0 ≤ C (v k) := by
    obtain ⟨s, _hs, hEq⟩ := hPeak k
    rw [← hEq]
    exact norm_nonneg _
  refine ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
    hSeparate, hCanonical, hEnergy, ?_⟩
  intro m F hF hFInt hUpper S hS ε hε
  have hOld := hRates m F hF hFInt hUpper ε hε
  filter_upwards [hOld] with k hk
  have hSplit := h3Path_scalar_higherBudget_sourceOrCutoffGain244
    ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
    (K (v k)) (C (v k)) S
    ((((v k : ℝ) + 1) ^ 2) ^ m * (((v k : ℝ) + 1) ^ 6))
    (((((v k : ℝ) + 1) ^ 2) ^ m) ^ 2 * (((v k : ℝ) + 1) ^ 9))
    (((v k : ℝ) + 1) ^ (2 * m + 3) *
      (((T - τ (v k)) / 2) / 2)) ε
    (hKnonneg k) (hCnonneg k) hS hε.le hk
  rcases hSplit with hSource | hTime | hLinear | hQuadratic
  · left
    obtain ⟨s, hs, hEq⟩ := hPeak k
    exact ⟨s, hs, by rw [hEq]; exact hSource⟩
  · exact Or.inr (Or.inl hTime)
  · exact Or.inr (Or.inr (Or.inl hLinear))
  · exact Or.inr (Or.inr (Or.inr hQuadratic))

end
end PrimeTensor.FirstMonomialTriad
