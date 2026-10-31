import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHigherBudgetActualGradientSpike244
import Mathlib.Tactic

/-!
# Unbounded actual physical velocity gradients on every terminal time tail

This file turns the conditional logarithmic coordinate-gradient spikes of the
previous module into a terminal-tail statement. It does NOT assert that the
higher-radial majorant, cutoff, projected-source ceiling, or terminal clock
hypotheses follow automatically from the physical Navier--Stokes PDE.

The result concerns actual derivatives at actual spatial points. It does not
imply divergence of a time integral, nor an unconditional BKM obstruction.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A fixed positive logarithmic spike rate at arbitrarily late radii
already gives arbitrarily large real gradient components on the specified
physical terminal tail. No supremum or maximizer is introduced. -/
theorem h3Path_eventualActualGradientLogSpikes_force_tailUnbounded244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T b : ℝ} {τ : ℕ → ℝ} {v : ℕ → ℕ} {c : ℝ}
    (hτ : ∀ n, τ n < T)
    (hv : StrictMono v)
    (hc : 0 < c)
    (hSpikes : ∀ᶠ k : ℕ in atTop,
      ∃ s : ℝ, s ∈ Set.Ioo b (τ (v k)) ∧
        ∃ i j : Axis Depth.three, ∃ x : Point3,
          c * Real.log ((v k : ℝ) + 1) <
            abs (spatial3.d i (loggedVelocityComponent u s j) x)) :
    ∀ M : ℝ, ∃ s : ℝ, s ∈ Set.Ioo b T ∧
      ∃ i j : Axis Depth.three, ∃ x : Point3,
        M < abs (spatial3.d i (loggedVelocityComponent u s j) x) := by
  intro M
  have hLogTop : Tendsto
      (fun k : ℕ => Real.log ((v k : ℝ) + 1)) atTop atTop :=
    h3Path_strictMono_canonicalLogRadius_escape244 v hv
  have hLarge : ∀ᶠ k : ℕ in atTop,
      M / c + 1 ≤ Real.log ((v k : ℝ) + 1) :=
    hLogTop.eventually (eventually_ge_atTop (M / c + 1))
  obtain ⟨k, hkSpike, hkLarge⟩ := (hSpikes.and hLarge).exists
  obtain ⟨s, hs, i, j, x, hGradient⟩ := hkSpike
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hScaled : c * (M / c + 1) ≤
      c * Real.log ((v k : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hkLarge hc.le
  have hThreshold : M < c * Real.log ((v k : ℝ) + 1) := by
    have hCancel : c * (M / c + 1) = M + c := by
      field_simp [hc0]
      <;> ring
    rw [hCancel] at hScaled
    linarith only [hScaled, hc]
  exact ⟨s, ⟨hs.1, lt_trans hs.2 (hτ (v k))⟩,
    i, j, x, lt_trans hThreshold hGradient⟩

/-- Under exactly the antecedents used for the canonical critical annulus
logarithmic gate, every physical terminal time tail contains arbitrarily
large actual coordinate velocity derivatives. This is a pointwise tail
obstruction, NOT an assertion of temporal integral divergence. -/
theorem h3Path_noL2Trace_exactAnchor_higherBudget_actualGradientTailEscape244
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
      (∀ k, v k ≤ N (v k) ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2)) ∧
      (∀ m : ℕ, ∀ F : ℝ → ℝ,
        (∀ s : ℝ, 0 ≤ F s) →
        IntervalIntegrable F volume a T →
        (∀ s : ℝ, ∀ hs : s ∈ Set.Ioo a T,
          h3TerminalPhysicalExtendedHigherRadialMomentAt
            hH3 hClass m s hs ≤ ENNReal.ofReal (F s)) →
        ∀ S D η ε : ℝ,
          0 ≤ S → 0 ≤ D → 0 < η → 0 < ε → ε < η →
          16 * ε ^ 2 * (36 * S ^ 2 * (D + 256) + 1) < 1 →
          (∀ᶠ k : ℕ in atTop, C (v k) ≤ S) →
          (∀ᶠ k : ℕ in atTop,
            ((N (v k) : ℝ) + 2) ^ 8 ≤ D * ((v k : ℝ) + 1) ^ 9) →
          (∀ᶠ k : ℕ in atTop,
            η ≤ ((v k : ℝ) + 1) ^ (2 * m + 3) * ((T - τ (v k)) / 4)) →
          ∀ b : ℝ, b ∈ Set.Ioo a T →
            ∀ M : ℝ,
              ∃ s : ℝ, s ∈ Set.Ioo b T ∧
                ∃ i j : Axis Depth.three, ∃ x : Point3,
                  M < abs (spatial3.d i (loggedVelocityComponent u s j) x)) := by
  classical
  obtain ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
      hSeparate, hAnchor, hHigher⟩ :=
    h3Path_noL2Trace_exactAnchor_higherBudget_actualGradientLogSpikes244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
    hSeparate, hAnchor, ?_⟩
  intro m F hF hFInt hUpper S D η ε hS hD hη hε hεη
    hSmall hCeil hCap hGeom b hb M
  let A : ℝ := 4 * (T - b) * 4422
  let c : ℝ := 1 / (1 + A)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
        (sub_nonneg.mpr hb.2.le))
      (by norm_num : (0 : ℝ) ≤ 4422)
  have hDen : 0 < 1 + A := by linarith only [hA]
  have hc : 0 < c := by
    dsimp only [c]
    exact one_div_pos.mpr hDen
  have hCost : A * c < 1 := by
    dsimp only [c]
    rw [mul_one_div]
    exact (div_lt_iff₀ hDen).2 (by linarith only [hDen])
  have hp : (1 : ℝ) ≤ ((16 * m + 3 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ 16 * m + 3)
  have hcSmall : 4 * (T - b) * 4422 * c <
      ((16 * m + 3 : ℕ) : ℝ) := by
    exact lt_of_lt_of_le (by simpa only [A] using hCost) hp
  have hSpikes := hHigher m F hF hFInt hUpper S D η ε
    hS hD hη hε hεη hSmall hCeil hCap hGeom b hb c hc.le hcSmall
  exact h3Path_eventualActualGradientLogSpikes_force_tailUnbounded244
    (fun n => (hτ n).2) hv hc hSpikes M

end
end PrimeTensor.FirstMonomialTriad
