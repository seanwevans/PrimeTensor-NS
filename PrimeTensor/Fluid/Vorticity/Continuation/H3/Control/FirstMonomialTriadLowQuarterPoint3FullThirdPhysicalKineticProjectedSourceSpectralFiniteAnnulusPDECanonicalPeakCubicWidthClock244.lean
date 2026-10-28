import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalPeakOptimizedPersistence244
import Mathlib.Tactic

/-!
# Exact cubic temporal concentration clock at canonical source maxima

The existing disjoint optimized physical H³ persistence windows have
A_k^8 = 16384*(E₀(b)+1)*H_k^3, where A_k is the original peak spectral
SUP norm, H_k the persistent physical dissipation floor, and d_k the
positive selected interval width. Finite terminal H³ dissipation yields
Summable (d_k*H_k). The exact polynomial identity is therefore

   d_k^3*A_k^8 = 16384*(E₀(b)+1)*(d_k*H_k)^3 -> 0.

This is the root-free formulation of d_k = o(A_k^(-8/3)). It is stronger
than d_k -> 0 and identifies the exact temporal exponent forced by the
optimized Fourier H³ coercivity. No quantitative lower bound for the
*actual* persistence duration or contradiction is asserted. The final
result transports the theorem to a subsequence of the SAME canonical
source-maximizing physical times, under the unchanged conditional
critical-width hypotheses.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Exact polynomial normalization of the optimized height-width charge:
no fractional exponents and no spectral L²/product-sup norm identification. -/
theorem h3Path_optimizedPeakWidthCube_exact244
    (d A H E : ℝ)
    (hIdentity : A ^ 8 = 16384 * (E + 1) * H ^ 3) :
    d ^ 3 * A ^ 8 =
      (16384 * (E + 1)) * (d * H) ^ 3 := by
  rw [hIdentity]
  ring

/-- On any sequence whose optimized height-width charge vanishes,
its original peak spectral amplitudes satisfy a cubic temporal clock. -/
theorem h3Path_optimizedPeakWidthCube_tendsto_zero244
    (d A H : ℕ → ℝ) (E : ℝ)
    (hIdentity : ∀ k, A k ^ 8 = 16384 * (E + 1) * H k ^ 3)
    (hChargeZero : Tendsto (fun k => d k * H k) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k => d k ^ 3 * A k ^ 8)
      atTop (𝓝 (0 : ℝ)) := by
  have hCube : Tendsto (fun k => (d k * H k) ^ 3)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using hChargeZero.pow 3
  have hScaled : Tendsto
      (fun k => (16384 * (E + 1)) * (d k * H k) ^ 3)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hCube :
      Tendsto (fun k => (16384 * (E + 1)) * (d k * H k) ^ 3)
        atTop (𝓝 ((16384 * (E + 1)) * (0 : ℝ))))
  have hEq :
      (fun k => d k ^ 3 * A k ^ 8) =
        (fun k => (16384 * (E + 1)) * (d k * H k) ^ 3) := by
    funext k
    exact h3Path_optimizedPeakWidthCube_exact244
      (d k) (A k) (H k) E (hIdentity k)
  rw [hEq]
  exact hScaled

/-- The finite terminal dissipation budget bounds EACH cubic spectral-clock
charge: the exact coefficient is 2^14 times the fixed kinetic mass plus one. -/
theorem h3Path_optimizedPeakWidthCube_le_budget244
    (d A H E B : ℝ)
    (hE : 0 ≤ E) (hd : 0 ≤ d) (hH : 0 ≤ H)
    (hIdentity : A ^ 8 = 16384 * (E + 1) * H ^ 3)
    (hBudget : d * H ≤ B) :
    d ^ 3 * A ^ 8 ≤ 16384 * (E + 1) * B ^ 3 := by
  have hProd : 0 ≤ d * H := mul_nonneg hd hH
  have hCube := pow_le_pow_left₀ hProd hBudget 3
  have hC : 0 ≤ 16384 * (E + 1) := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hCube hC
  calc
    d ^ 3 * A ^ 8 = (16384 * (E + 1)) * (d * H) ^ 3 :=
      h3Path_optimizedPeakWidthCube_exact244 d A H E hIdentity
    _ ≤ (16384 * (E + 1)) * B ^ 3 := hScaled

/-- A positive lower bound for the cubic amplitude-width clock is
incompatible with finite optimized dissipation charges. This is a
necessary obstruction for any future PDE-based lower duration estimate. -/
theorem h3Path_optimizedPeakWidthCube_eventually_small244
    (d A H : ℕ → ℝ) (E : ℝ)
    (hIdentity : ∀ k, A k ^ 8 = 16384 * (E + 1) * H k ^ 3)
    (hSummable : Summable (fun k => d k * H k))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, d k ^ 3 * A k ^ 8 < ε := by
  have hZero := h3Path_optimizedPeakWidthCube_tendsto_zero244
    d A H E hIdentity hSummable.tendsto_atTop_zero
  exact (tendsto_order.1 hZero).2 ε hε

/-- The numerical persistence exponent is sharp as a necessary upper
clock: no eventually positive lower cubic-amplitude cost survives finite
H³ dissipation under the exact optimized source-peak identity. -/
theorem h3Path_optimizedPeakWidthCube_noPositiveLowerClock244
    (d A H : ℕ → ℝ) (E : ℝ)
    (hIdentity : ∀ k, A k ^ 8 = 16384 * (E + 1) * H k ^ 3)
    (hSummable : Summable (fun k => d k * H k))
    (ε : ℝ) (hε : 0 < ε) :
    ¬ (∀ᶠ k : ℕ in atTop, ε ≤ d k ^ 3 * A k ^ 8) := by
  intro hLower
  have hUpper := h3Path_optimizedPeakWidthCube_eventually_small244
    d A H E hIdentity hSummable ε hε
  obtain ⟨k, hkLower, hkUpper⟩ := (hLower.and hUpper).exists
  exact (not_lt_of_ge hkLower) hkUpper

/-- The SAME canonical physical source-maximizing observations, under the
unchanged explicit critical-width regime, have disjoint optimized physical
persistence windows satisfying the root-free sharp temporal-collapse law
`d_k^3 * ‖U₃(s(w k))‖^8 -> 0`. New times are selected only as a subsequence
of the original source maxima; no quantitative PDE persistence lower bound
is asserted. -/
theorem h3Path_noL2Trace_canonicalWidth_sourcePeakCubicWidthClock244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hTerminalMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
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
      (∀ η B D : ℝ, 0 < η → 0 ≤ B → 0 ≤ D →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * (((v k : ℝ) + 1) ^ 6) ∧
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 ≤
            D * (((v k : ℝ) + 1) ^ 9)) →
        ∀ b : ℝ, b ∈ Set.Ioo a T →
        ∃ (w : ℕ → ℕ) (d H : ℕ → ℝ),
          StrictMono w ∧
          Tendsto (fun k => s (w k)) atTop (𝓝 T) ∧
          (∀ k l, k < l → s (w k) + d k < s (w l)) ∧
          (∀ k, 0 < d k ∧ s (w k) + d k < T) ∧
          (∀ k, 0 ≤ H k ∧
            ‖h3AuditActualSpectralVelocityTotal hH3 (s (w k))‖ ^ 2 / 8 ≤ H k ∧
            ‖h3AuditActualSpectralVelocityTotal hH3 (s (w k))‖ ^ 8 =
              16384 * (velocityH3Energy0At u b + 1) * (H k) ^ 3) ∧
          (∀ k r, r ∈ Set.Icc (s (w k)) (s (w k) + d k) →
            H k ≤ velocityH3DissipationAt u r) ∧
          Tendsto H atTop atTop ∧
          Summable (fun k => d k * H k) ∧
          Tendsto (fun k => d k * H k) atTop (𝓝 (0 : ℝ)) ∧
          Tendsto (fun k =>
            d k ^ 3 *
              ‖h3AuditActualSpectralVelocityTotal hH3 (s (w k))‖ ^ 8)
            atTop (𝓝 (0 : ℝ)) ∧
          (∀ m, (∑ k ∈ Finset.range m, d k * H k) ≤
            ∫ r in a..T, velocityH3DissipationAt u r)) := by
  obtain ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
      hSeparate, hSummable, hCanonical, hPeak, hJoint⟩ :=
    h3Path_noL2Trace_canonicalWidth_sourcePeakOptimizedPersistence244
      hH3 hClass hTerminalMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, s, hv, hCofinal, hTime,
    hSeparate, hSummable, hCanonical, hPeak, ?_⟩
  intro η B D hη hB hD hRegime b hb
  obtain ⟨w, d, H, hw, hwCofinal, hDisjoint, hWidths,
      hHeights, hFloors, hEscape, hCharges, hChargeZero, hBudget⟩ :=
    hJoint η B D hη hB hD hRegime b hb
  have hIdentity (k : ℕ) :
      ‖h3AuditActualSpectralVelocityTotal hH3 (s (w k))‖ ^ 8 =
        16384 * (velocityH3Energy0At u b + 1) * H k ^ 3 :=
    (hHeights k).2.2
  have hCubic : Tendsto (fun k : ℕ =>
      d k ^ 3 * ‖h3AuditActualSpectralVelocityTotal hH3 (s (w k))‖ ^ 8)
      atTop (𝓝 (0 : ℝ)) :=
    h3Path_optimizedPeakWidthCube_tendsto_zero244
      d (fun k => ‖h3AuditActualSpectralVelocityTotal hH3 (s (w k))‖)
      H (velocityH3Energy0At u b) hIdentity hChargeZero
  exact ⟨w, d, H, hw, hwCofinal, hDisjoint, hWidths,
    hHeights, hFloors, hEscape, hCharges, hChargeZero, hCubic, hBudget⟩

end
end PrimeTensor.FirstMonomialTriad
