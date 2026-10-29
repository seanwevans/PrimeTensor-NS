import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHighTailEvacuation244
import Mathlib.Tactic

/-!
# Canonical physical H³ high-tail mass or projected-source impulse

The preceding exact-anchor PDE theorem forces a loss in genuine high-Q
physical dissipation when the full H³ dissipation drops on a canonical
window. This file splits its *actual one-cutoff linear-plus-quadratic* PDE
budget into two independent source-action mechanisms.

Write X_k = (Q_k+1) sqrt(3 W(Q_k)) C_k delta_k, the bounded-radial
projected-source impulse, and Y_k = (Q_k+1) K_k, where K_k is the actual
anchor weighted spectral sup norm. The physical low-Q PDE budget equals
6 Y_k X_k + 3 X_k². At a full dissipation cliff of depth theta,

  beta D_k < H_Q(t_k)

or

  (1-theta-beta) D_k < 12 Y_k X_k

or

  (1-theta-beta) D_k < 6 X_k².

No bound on the source impulse is assumed. The eventual full-dissipation
cliff still requires the previously explicit noncollapsed height-width
hypothesis. This is a necessary three-arm alternative, not a regularity
contradiction or an unconditional high-frequency bound.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The exact bounded-radial physical source action over the canonical
quadratic-sharp window. It is not a full-H³ projected-source norm. -/
noncomputable def h3PathCubicAnnulusOuterLowGradientSourceImpulse244
    (N : ℕ → ℕ) (C δ : ℕ → ℝ) (n : ℕ) : ℝ :=
  h3PathLowRadialPDEGradientRate244 ((N n : ℝ) + 1) (C n) * δ n

/-- A source-driven linear-plus-quadratic rate too large for the available
budget must have a large linear coupling or a large quadratic impulse. -/
theorem h3Path_scalar_sourceActionLinearOrQuadratic244
    (A Y X : ℝ) (hBudget : A < 6 * Y * X + 3 * X ^ 2) :
    A < 12 * Y * X ∨ A < 6 * X ^ 2 := by
  by_contra hNot
  push_neg at hNot
  nlinarith only [hBudget, hNot.1, hNot.2]

/-- If the high-frequency tail holds no more than beta of the full anchor
height, a genuine physical cliff forces large projected-source action in
one of the two actual one-cutoff PDE rate terms. -/
theorem h3Path_scalar_smallHighTail_cliff_forces_sourceAction244
    (D H₀ H₁ B Y X θ β : ℝ)
    (hH₁ : 0 ≤ H₁)
    (hTail : H₀ ≤ β * D)
    (hCliff : (1 - θ) * D - B < H₀ - H₁)
    (hExactRate : B = 6 * Y * X + 3 * X ^ 2) :
    (1 - θ - β) * D < 12 * Y * X ∨
      (1 - θ - β) * D < 6 * X ^ 2 := by
  have hRequired : (1 - θ - β) * D < B := by
    nlinarith only [hH₁, hTail, hCliff]
  rw [hExactRate] at hRequired
  exact h3Path_scalar_sourceActionLinearOrQuadratic244
    ((1 - θ - β) * D) Y X hRequired

/-- No a priori small high-tail hypothesis: either the tail itself is
already large, or the actual one-cutoff projected PDE rate splits into
the two necessary source-action arms. -/
theorem h3Path_scalar_cliff_highTailOrSourceAction244
    (D H₀ H₁ B Y X θ β : ℝ)
    (hH₁ : 0 ≤ H₁)
    (hCliff : (1 - θ) * D - B < H₀ - H₁)
    (hExactRate : B = 6 * Y * X + 3 * X ^ 2) :
    β * D < H₀ ∨
      (1 - θ - β) * D < 12 * Y * X ∨
      (1 - θ - β) * D < 6 * X ^ 2 := by
  by_cases hTail : β * D < H₀
  · exact Or.inl hTail
  · exact Or.inr (h3Path_scalar_smallHighTail_cliff_forces_sourceAction244
      D H₀ H₁ B Y X θ β hH₁ (le_of_not_gt hTail) hCliff hExactRate)

/-- At the ACTUAL exact-anchor projected-source clock, any full H³
physical cliff has a three-arm alternative: large high-Q dissipation
mass, large linear source action, or large quadratic source action.
The high tail and the source impulse are genuine physical Fourier data. -/
theorem h3Path_exactAnchorPDE_cliff_highTailOrSourceAction244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
    (v : ℕ → ℕ) (k : ℕ) (s θ β : ℝ)
    (ht : τ (v k) ∈ Set.Ioo a T)
    (hK : K (v k) =
      ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖)
    (hC : C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
      (τ (v k)) (τ (v k) + (T - τ (v k)) / 2))
    (hExact : δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
      ((T - τ (v k)) / 2)
      (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
      (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
      (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)))
    (hδ : 0 < δ (v k))
    (hEnd : τ (v k) + δ (v k) < T)
    (hs : s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)))
    (hDip : velocityH3DissipationAt u s <
      θ * velocityH3DissipationAt u (τ (v k))) :
    β * velocityH3DissipationAt u (τ (v k)) <
      h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ∨
    (1 - θ - β) * velocityH3DissipationAt u (τ (v k)) <
      12 * (((N (v k) : ℝ) + 1) + 1) * K (v k) *
        h3PathCubicAnnulusOuterLowGradientSourceImpulse244 N C δ (v k) ∨
    (1 - θ - β) * velocityH3DissipationAt u (τ (v k)) <
      6 * (h3PathCubicAnnulusOuterLowGradientSourceImpulse244 N C δ (v k)) ^ 2 := by
  let Q : ℝ := (N (v k) : ℝ) + 1
  let V : ℝ := h3PathLowRadialPDEGradientRate244 Q (C (v k))
  let X : ℝ := V * δ (v k)
  let Y : ℝ := (Q + 1) * K (v k)
  let B : ℝ :=
    h3PathCubicAnnulusOuterLowLinearRate244 N K C (v k) * δ (v k) +
    h3PathCubicAnnulusOuterLowQuadraticRate244 N C (v k) * δ (v k) ^ 2
  have hEvac := h3Path_exactAnchorPDE_dip_forces_highTailEvacuation244
    hH3 hClass τ N K C δ v k s θ ht hK hC hExact hδ hEnd hs hDip
  have hTailNonneg : 0 ≤
      h3PathActualHighRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 s) := by
    unfold h3PathActualHighRadialDissipation244
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg _ ξ
  have hRate : B = 6 * Y * X + 3 * X ^ 2 := by
    dsimp only [B, Y, X, V, Q,
      h3PathCubicAnnulusOuterLowLinearRate244,
      h3PathCubicAnnulusOuterLowQuadraticRate244]
    ring
  have hScalar := h3Path_scalar_cliff_highTailOrSourceAction244
    (velocityH3DissipationAt u (τ (v k)))
    (h3PathActualHighRadialDissipation244 Q
      (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))
    (h3PathActualHighRadialDissipation244 Q
      (h3AuditActualSpectralVelocityTotal hH3 s))
    B Y X θ β hTailNonneg (by simpa only [B, Q] using hEvac) hRate
  simpa only [Q, Y, X, V,
    h3PathCubicAnnulusOuterLowGradientSourceImpulse244, mul_assoc]
    using hScalar

/-- SAME canonical cofinal and disjoint windows: if the anchor height-times-
width charge does not collapse, then for every relative cliff theta and
positive desired high-tail fraction beta, EITHER the high-Q physical tail
already dominates beta of D, OR a linear spectral-source impulse, OR a
quadratic projected-source impulse must be comparably large.

Neither persistent charge nor any source/rate cap is asserted automatically. -/
theorem h3Path_noL2Trace_exactAnchor_persistentCharge_highTailOrSourceAction244
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
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k,
        K (v k) = ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
          ((T - τ (v k)) / 2)
          (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
          (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
          (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)) ∧
        0 < δ (v k) ∧ τ (v k) + δ (v k) < T) ∧
      (∀ η : ℝ, 0 < η →
        (∀ᶠ k : ℕ in atTop,
          η ≤ δ (v k) * velocityH3DissipationAt u (τ (v k))) →
        ∀ θ β : ℝ, 0 < θ → θ < 1 → 0 ≤ β → θ + β < 1 →
        ∀ᶠ k : ℕ in atTop,
          β * velocityH3DissipationAt u (τ (v k)) <
            h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ∨
          (1 - θ - β) * velocityH3DissipationAt u (τ (v k)) <
            12 * (((N (v k) : ℝ) + 1) + 1) * K (v k) *
              h3PathCubicAnnulusOuterLowGradientSourceImpulse244 N C δ (v k) ∨
          (1 - θ - β) * velocityH3DissipationAt u (τ (v k)) <
            6 * (h3PathCubicAnnulusOuterLowGradientSourceImpulse244 N C δ (v k)) ^ 2) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, hAll, hConditional⟩ :=
    h3Path_noL2Trace_exactAnchor_persistentCharge_highTailEvacuation244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
    hSeparate, hAll, ?_⟩
  intro η hη hPersist θ β hθ hθOne _hβ _hSum
  have hCliff := (hConditional η hη hPersist θ hθ hθOne).1
  filter_upwards [hCliff] with k hk
  obtain ⟨s, hs, hDip, _hTailLoss⟩ := hk
  rcases hAll k with ⟨hK, hC, hExact, hδ, hEnd⟩
  exact h3Path_exactAnchorPDE_cliff_highTailOrSourceAction244
    hH3 hClass τ N K C δ v k s θ β
    (hTime (v k)) hK hC hExact hδ hEnd hs hDip

end
end PrimeTensor.FirstMonomialTriad
