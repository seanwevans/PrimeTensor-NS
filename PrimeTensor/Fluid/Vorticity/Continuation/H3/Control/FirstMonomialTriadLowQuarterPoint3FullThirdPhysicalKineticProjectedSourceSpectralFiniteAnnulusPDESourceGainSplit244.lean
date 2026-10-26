import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEIntermittentSixthBarrier244
import Mathlib.Tactic

/-!
# Intermittent physical source versus spectral-cutoff amplification

The exact physical projected-PDE coefficient is an explicit linear-plus-
quadratic polynomial in the selected nonnegative source ceiling C. This
module factors it into a linear gain depending on the starting spectral
bound K and a quadratic frequency gain, then separates the source and
frequency mechanisms responsible for intermittent sixth-order growth.

The final physical theorem retains the same witnesses as the prior
intermittent theorem and extracts a nontrivial linear-or-quadratic
component barrier. It does not bound the cutoff gains or source ceiling.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The source-linear amplification at the selected inner and outer radii. -/
noncomputable def h3PathFiniteAnnulusPDELinearGain244
    (R Q K : ℝ) : ℝ :=
  6 * K *
    ((Q + 1) ^ 2 *
        Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling Q) +
      (R + 1) ^ 2 *
        Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling R))

/-- The source-quadratic amplification; independent of the starting state. -/
noncomputable def h3PathFiniteAnnulusPDEQuadraticGain244
    (R Q : ℝ) : ℝ :=
  3 *
    (((Q + 1) *
        Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling Q)) ^ 2 +
      ((R + 1) *
        Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling R)) ^ 2)

/-- Exact polynomial factorization of the previously proved PHYSICAL
projected-PDE variation rates; this is not a new estimated rate. -/
theorem h3Path_finiteAnnulusPDERate_sourcePolynomial244
    (R Q K C : ℝ) :
    h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C +
        h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C + 1 =
      C * h3PathFiniteAnnulusPDELinearGain244 R Q K +
        C ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q + 1 := by
  unfold h3PathFiniteAnnulusPDEVariationCoefficient244
    h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
    h3PathLowRadialPDEGradientRate244
    h3PathFiniteAnnulusPDELinearGain244
    h3PathFiniteAnnulusPDEQuadraticGain244
  ring

/-- The linear and quadratic frequency amplifiers are nonnegative under
the natural nonnegative starting spectral bound. -/
theorem h3Path_finiteAnnulusPDEGains_nonneg244
    (R Q K : ℝ) (hK : 0 ≤ K) :
    0 ≤ h3PathFiniteAnnulusPDELinearGain244 R Q K ∧
      0 ≤ h3PathFiniteAnnulusPDEQuadraticGain244 R Q := by
  constructor
  · unfold h3PathFiniteAnnulusPDELinearGain244
    positivity
  · unfold h3PathFiniteAnnulusPDEQuadraticGain244
    positivity

/-- If the physical coefficient reaches a specified sixth-order barrier,
then either the projected-source ceiling exceeds S, or the explicit
cutoff/spectral gains evaluated at S already reach that barrier. -/
theorem h3Path_sixthRate_forces_sourceOrCutoffAmplification244
    (R Q K C B S : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hRate : B * R ^ 6 ≤
      h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C +
        h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C + 1) :
    S < C ∨
      B * R ^ 6 ≤
        S * h3PathFiniteAnnulusPDELinearGain244 R Q K +
          S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q + 1 := by
  by_cases hEscape : S < C
  · exact Or.inl hEscape
  · right
    have hCS : C ≤ S := le_of_not_gt hEscape
    have hGains := h3Path_finiteAnnulusPDEGains_nonneg244 R Q K hK
    have hC2 : C ^ 2 ≤ S ^ 2 := by
      have hProduct : 0 ≤ (S - C) * (S + C) :=
        mul_nonneg (sub_nonneg.mpr hCS) (add_nonneg hS hC)
      nlinarith only [hProduct]
    have hLinear :
        C * h3PathFiniteAnnulusPDELinearGain244 R Q K ≤
          S * h3PathFiniteAnnulusPDELinearGain244 R Q K :=
      mul_le_mul_of_nonneg_right hCS hGains.1
    have hQuadratic :
        C ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q ≤
          S ^ 2 * h3PathFiniteAnnulusPDEQuadraticGain244 R Q :=
      mul_le_mul_of_nonneg_right hC2 hGains.2
    rw [h3Path_finiteAnnulusPDERate_sourcePolynomial244] at hRate
    linarith only [hRate, hLinear, hQuadratic]

/-- Any sum rate above a sixth-order threshold contains a linear or
quadratic component above half of the threshold (up to the unit term). -/
theorem h3Path_sixthSumRate_forces_componentBarrier244
    (A Λ Ξ : ℝ) (hA : A ≤ Λ + Ξ + 1) :
    A ≤ 2 * Λ + 1 ∨ A ≤ 2 * Ξ + 1 := by
  by_contra hNot
  push_neg at hNot
  linarith only [hA, hNot.1, hNot.2]

/-- The actual cofinal physical witnesses have an intermittent
linear-or-quadratic sixth-order source-rate barrier. No eventual geometric
noncompression, bounded source, or bounded outer cutoff is assumed. -/
theorem h3Path_noL2Trace_finiteDissipation_intermittentPDEComponents244
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
        (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ,
        ((v k : ℝ) + 1) ^ 3 / 4 <
          h3PathCubicAnnulusActualGap244 hH3 τ N (v k)) ∧
      Summable (fun k : ℕ =>
        δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ η B : ℝ, 0 < η → 0 < B →
        ∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (T - τ (v k)) / 4 →
            B * ((v k : ℝ) + 1) ^ 6 ≤
              2 * h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ∨
            B * ((v k : ℝ) + 1) ^ 6 ≤
              2 * h3PathCubicAnnulusActualQuadraticRate244 N C (v k) + 1) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparate, hGap,
      hSummable, hSpike⟩ :=
    h3Path_noL2Trace_finiteDissipation_intermittentSixthBarrier244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hSeparate, hGap,
    hSummable, ?_⟩
  intro η B hη hB
  filter_upwards [hSpike η B hη hB] with k hk
  intro hkLag
  exact h3Path_sixthSumRate_forces_componentBarrier244 _ _ _ (hk hkLag)

end
end PrimeTensor.FirstMonomialTriad
