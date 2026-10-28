import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakCompressedRiccatiExtension244
import Mathlib.Tactic

/-!
# Exact cofinal obstruction to all three canonical critical-width caps

The previous theorem shows that simultaneous eventual geometric noncompression,
a sixth-order linear-source rate ceiling and a critical ninth/eighth annular
width ceiling force smooth continuation.  This module takes the logical
contrapositive on the SAME canonical sequence, under explicit nonextension.
For every fixed positive geometric threshold and finite nonnegative rate/width
caps, there is an arbitrarily late index violating at least one test.

If geometric noncompression and the linear cap do hold eventually, the
normalized annulus-width eighth power violates EVERY ninth-order cap
cofinally; dually, geometric noncompression plus the width cap forces the
normalized linear rate to violate EVERY sixth-order cap cofinally.

No unproved one of those three hypotheses is silently inserted.  This is a
necessary obstruction under nonextension, not unconditional regularity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Failure of an eventual upper bound is witnessed arbitrarily far along a
natural-number sequence.  This does not claim eventual strict violation. -/
theorem h3Path_scalar_notEventuallyLe_cofinalStrictViolation244
    (f g : ℕ → ℝ)
    (hNot : ¬ ∀ᶠ k : ℕ in atTop, f k ≤ g k) :
    ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧ g k < f k := by
  intro n
  by_contra hNoWitness
  have hTail : ∀ k : ℕ, n ≤ k → f k ≤ g k := by
    intro k hnk
    by_contra hNotLe
    exact hNoWitness ⟨k, hnk, lt_of_not_ge hNotLe⟩
  have hEventual : ∀ᶠ k : ℕ in atTop, f k ≤ g k :=
    Filter.eventually_atTop.2 ⟨n, hTail⟩
  exact hNot hEventual

/-- Simultaneous eventual three-cap failure produces an actual violation of
one of the three caps beyond each requested index. -/
theorem h3Path_scalar_notEventuallyTriple_cofinalFailure244
    (G F W R : ℕ → ℝ) (η U V : ℝ)
    (hNot : ¬ ∀ᶠ k : ℕ in atTop,
      η ≤ G k ∧ F k ≤ U * R k ^ 6 ∧ W k ≤ V * R k ^ 9) :
    ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧
      (G k < η ∨ U * R k ^ 6 < F k ∨ V * R k ^ 9 < W k) := by
  intro n
  by_contra hNoWitness
  have hTail : ∀ k : ℕ, n ≤ k →
      η ≤ G k ∧ F k ≤ U * R k ^ 6 ∧ W k ≤ V * R k ^ 9 := by
    intro k hnk
    have hBad (hViolation :
        G k < η ∨ U * R k ^ 6 < F k ∨ V * R k ^ 9 < W k) : False :=
      hNoWitness ⟨k, hnk, hViolation⟩
    constructor
    · by_contra hNg
      exact hBad (Or.inl (lt_of_not_ge hNg))
    · constructor
      · by_contra hNf
        exact hBad (Or.inr (Or.inl (lt_of_not_ge hNf)))
      · by_contra hNw
        exact hBad (Or.inr (Or.inr (lt_of_not_ge hNw)))
  have hEventual : ∀ᶠ k : ℕ in atTop,
      η ≤ G k ∧ F k ≤ U * R k ^ 6 ∧ W k ≤ V * R k ^ 9 :=
    Filter.eventually_atTop.2 ⟨n, hTail⟩
  exact hNot hEventual

/-- Under the exact no-trace, finite-physical-dissipation and no-extension
hypotheses, the original critical-width disjoint witnesses and the EXACT
source-maximizing time sequence rule out simultaneous eventual satisfaction
of all three geometric/PDE rate/annular cap tests.

The first conclusion is their cofinal three-way disjunction.  The second
and third are genuine normalized escape alternatives: whenever two caps
hold eventually, the third violates EVERY nonnegative fixed ceiling on
arbitrarily late indices.  No reselected annuli or source maxima occur. -/
theorem h3Path_noL2Trace_noExtension_canonicalCriticalRegimeCofinalFailure244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTerminalMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (hNoExtension : ¬ ∃ w : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u w T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v : ℕ → ℕ) (s : ℕ → ℝ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k, v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2)) ∧
      (∀ k, s k ∈ Set.Icc (τ (v k))
          (τ (v k) + (T - τ (v k)) / 2) ∧
        ‖h3PathActualProjectedMomentumSource244 hH3 (s k)‖ = C (v k)) ∧
      (∀ η U V : ℝ, 0 < η → 0 ≤ U → 0 ≤ V →
        ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧
          ( ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) < η ∨
            U * (((v k : ℝ) + 1) ^ 6) <
              h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ∨
            V * (((v k : ℝ) + 1) ^ 9) <
              (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8)) ∧
      (∀ η U : ℝ, 0 < η → 0 ≤ U →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2)) →
        (∀ᶠ k : ℕ in atTop,
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            U * (((v k : ℝ) + 1) ^ 6)) →
        ∀ V : ℝ, 0 ≤ V → ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧
          V * (((v k : ℝ) + 1) ^ 9) <
            (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8) ∧
      (∀ η V : ℝ, 0 < η → 0 ≤ V →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2)) →
        (∀ᶠ k : ℕ in atTop,
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            V * (((v k : ℝ) + 1) ^ 9)) →
        ∀ U : ℝ, 0 ≤ U → ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧
          U * (((v k : ℝ) + 1) ^ 6) <
            h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, hExtension⟩ :=
    h3Path_noL2Trace_canonicalWidth_criticalRegime_forces_extension244
      hH3 hClass hTerminalMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, ?_, ?_, ?_⟩
  · intro η U V hη hU hV
    have hNot : ¬ ∀ᶠ k : ℕ in atTop,
        η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
        h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
          U * (((v k : ℝ) + 1) ^ 6) ∧
        (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
          V * (((v k : ℝ) + 1) ^ 9) := by
      intro hRegime
      exact hNoExtension (hExtension η U V hη hU hV hRegime)
    exact h3Path_scalar_notEventuallyTriple_cofinalFailure244
      (fun k => ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2))
      (fun k => h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1)
      (fun k => (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8)
      (fun k => ((v k : ℝ) + 1)) η U V hNot
  · intro η U hη hU hGeom hRate V hV
    apply h3Path_scalar_notEventuallyLe_cofinalStrictViolation244
      (fun k => (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8)
      (fun k => V * (((v k : ℝ) + 1) ^ 9))
    intro hWidth
    have hRegime : ∀ᶠ k : ℕ in atTop,
        η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
        h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
          U * (((v k : ℝ) + 1) ^ 6) ∧
        (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
          V * (((v k : ℝ) + 1) ^ 9) := by
      filter_upwards [hGeom, hRate, hWidth] with k hg hr hw
      exact ⟨hg, hr, hw⟩
    exact hNoExtension (hExtension η U V hη hU hV hRegime)
  · intro η V hη hV hGeom hWidth U hU
    apply h3Path_scalar_notEventuallyLe_cofinalStrictViolation244
      (fun k => h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1)
      (fun k => U * (((v k : ℝ) + 1) ^ 6))
    intro hRate
    have hRegime : ∀ᶠ k : ℕ in atTop,
        η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
        h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
          U * (((v k : ℝ) + 1) ^ 6) ∧
        (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
          V * (((v k : ℝ) + 1) ^ 9) := by
      filter_upwards [hGeom, hRate, hWidth] with k hg hr hw
      exact ⟨hg, hr, hw⟩
    exact hNoExtension (hExtension η U V hη hU hV hRegime)

end
end PrimeTensor.FirstMonomialTriad
