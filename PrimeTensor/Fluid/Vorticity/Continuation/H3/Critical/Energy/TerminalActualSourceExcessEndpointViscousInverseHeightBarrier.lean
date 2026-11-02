import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousTwoWindowExposure
import Mathlib.Tactic

/-!
# Critical inverse-height persistence barrier for synchronized endpoint spikes

Finite terminal physical H³ dissipation forces the charge
  η(k) * (R(k)^2 * ε(k)^2 / 8)
to vanish on the SAME cofinal selection used by the spectral and physical
PDE-clock gates. Since R(k), ε(k) are positive, this implies the quantitative
strict bound η(k) < γ / (R(k)^2 * ε(k)^2 / 8) eventually for every γ > 0.

In particular a positive fraction of the critical inverse-height window
cannot persist for all sufficiently late indices. The endpoint high-dissipation
branch of the selected four-way gate is thereby confined to these shrinking
inverse-height times, while all other physical alternatives remain exactly
as before. Nothing in this module asserts a terminal-uniform continuity
radius or a Navier–Stokes regularity conclusion.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Vanishing height-width charges and strictly positive comparison heights
force the width to be eventually strictly below EVERY fixed positive
multiple of the inverse height. No growth assumption on the heights is
needed. In particular the statement remains informative when heights vary. -/
theorem h3Critical_scalar_vanishingCharge_eventualInverseHeightWidth
    (η H : ℕ → ℝ)
    (hHeight : ∀ k : ℕ, 0 < H k)
    (hCharge : Tendsto (fun k : ℕ => η k * H k) atTop (𝓝 (0 : ℝ)))
    (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ k : ℕ in atTop, η k < γ / H k := by
  have hTiny : ∀ᶠ k : ℕ in atTop, η k * H k < γ :=
    (tendsto_order.1 hCharge).2 γ hγ
  filter_upwards [hTiny] with k hk
  exact (lt_div_iff₀ (hHeight k)).2 hk

/-- A cofinal persistence lower bound at ANY fixed positive multiple of the
inverse height contradicts vanishing terminal charges. This rules out an
*eventual* critical-scale plateau, not an isolated positive-width spike. -/
theorem h3Critical_scalar_vanishingCharge_noEventualCriticalPersistence
    (η H : ℕ → ℝ)
    (hHeight : ∀ k : ℕ, 0 < H k)
    (hCharge : Tendsto (fun k : ℕ => η k * H k) atTop (𝓝 (0 : ℝ)))
    (γ : ℝ) (hγ : 0 < γ) :
    ¬ (∀ᶠ k : ℕ in atTop, γ / H k ≤ η k) := by
  intro hPersistent
  have hShort := h3Critical_scalar_vanishingCharge_eventualInverseHeightWidth
    η H hHeight hCharge γ hγ
  obtain ⟨k, hShortK, hPersistentK⟩ := (hShort.and hPersistent).exists
  exact (not_lt_of_ge hPersistentK) hShortK

/-- Under finite terminal full physical H³ dissipation, the ORIGINAL
cofinal fivefold witnesses have summable endpoint viscous charges, and the
selected endpoint-persistence branch has a critical inverse-height upper
width bound on every sufficiently late index. The alternative PDE-clock,
non-spectral and anchor-viscosity branches are preserved without altering
the witnesses.

This is a necessary escape-scale restriction, not a proof of terminal
regularity: the selected widths may collapse arbitrarily quickly. -/
theorem h3Critical_noL2Trace_cofinalFivefold_inverseHeightEndpointPersistenceGate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (c ρ σ M q : ℕ → ℝ)
    (hc : ∀ n, c n ∈ Set.Ioo b T)
    (hcLimit : Tendsto c atTop (𝓝 T))
    (hρ : ∀ n, 0 ≤ ρ n)
    (hσ : ∀ n, 0 ≤ σ n)
    (hM : ∀ n, 0 ≤ M n)
    (hq : ∀ n, 0 < q n)
    (R ε : ℕ → ℝ) (hR : ∀ k, 0 < R k) (hε : ∀ k, 0 < ε k)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ i : Fin 3, ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ sSource sState δ p η : ℕ → ℝ, ∃ N : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → p k + η k < p l) ∧
      Summable (fun k : ℕ => η k * (R k ^ 2 * ε k ^ 2 / 8)) ∧
      Tendsto (fun k : ℕ => η k * (R k ^ 2 * ε k ^ 2 / 8))
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ m : ℕ,
        (∑ k ∈ Finset.range m,
          η k * (R k ^ 2 * ε k ^ 2 / 8)) ≤
          ∫ r in a..T, velocityH3DissipationAt u r) ∧
      (∀ k : ℕ,
        3 + 4 * h3AuditInitialLerayEnergyCoefficient * ε k ≤
          max 1 (σ (v k)) + 1 →
        h3Critical_fivefold_nonSpectralExcursionAlternative hH3
          (t (v k)) (w (v k)) (δ k) (σ (v k))
          (M (v k)) (q (v k)) (sSource k) ∨
        ε k ^ 2 ≤ 2 * (3 * h3TerminalRadialSobolevWeightSquareCeiling (R k)) *
          (‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ *
            w (v k)) ^ 2 ∨
        R k ^ 2 * ε k ^ 2 < 8 * velocityH3DissipationAt u (t (v k)) ∨
        (0 < η k ∧
          ∀ r : ℝ, r ∈ Set.Icc (p k) (p k + η k) →
            R k ^ 2 * ε k ^ 2 / 8 <
              h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) ∧
            R k ^ 2 * ε k ^ 2 / 8 < velocityH3DissipationAt u r)) ∧
      (∀ γ : ℝ, 0 < γ →
        ∀ᶠ k : ℕ in atTop,
          η k < γ / (R k ^ 2 * ε k ^ 2 / 8)) ∧
      (∀ γ : ℝ, 0 < γ →
        ∀ᶠ k : ℕ in atTop,
          3 + 4 * h3AuditInitialLerayEnergyCoefficient * ε k ≤
            max 1 (σ (v k)) + 1 →
          h3Critical_fivefold_nonSpectralExcursionAlternative hH3
            (t (v k)) (w (v k)) (δ k) (σ (v k))
            (M (v k)) (q (v k)) (sSource k) ∨
          ε k ^ 2 ≤ 2 * (3 * h3TerminalRadialSobolevWeightSquareCeiling (R k)) *
            (‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ *
              w (v k)) ^ 2 ∨
          R k ^ 2 * ε k ^ 2 < 8 * velocityH3DissipationAt u (t (v k)) ∨
          (0 < η k ∧
            η k < γ / (R k ^ 2 * ε k ^ 2 / 8) ∧
            ∀ r : ℝ, r ∈ Set.Icc (p k) (p k + η k) →
              R k ^ 2 * ε k ^ 2 / 8 <
                h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                  (h3AuditActualSpectralVelocityTotal hH3 r) ∧
              R k ^ 2 * ε k ^ 2 / 8 < velocityH3DissipationAt u r)) := by
  obtain ⟨i, t, w, v, sSource, sState, δ, p, η, N,
      hv, hLimit, hSeparate, hSummable, hCharge, hBudget, hGate⟩ :=
    h3Critical_noL2Trace_cofinalFivefold_endpointViscousChargeCollapse
      hH3 hClass b hb hNoTrace c ρ σ M q
      hc hcLimit hρ hσ hM hq R ε hR hε hDInt
  have hHeight (k : ℕ) : 0 < R k ^ 2 * ε k ^ 2 / 8 := by
    have hr := hR k
    have he := hε k
    positivity
  have hShort (γ : ℝ) (hγ : 0 < γ) :
      ∀ᶠ k : ℕ in atTop,
        η k < γ / (R k ^ 2 * ε k ^ 2 / 8) :=
    h3Critical_scalar_vanishingCharge_eventualInverseHeightWidth
      η (fun k => R k ^ 2 * ε k ^ 2 / 8) hHeight hCharge γ hγ
  have hRefined (γ : ℝ) (hγ : 0 < γ) :
      ∀ᶠ k : ℕ in atTop,
        3 + 4 * h3AuditInitialLerayEnergyCoefficient * ε k ≤
          max 1 (σ (v k)) + 1 →
        h3Critical_fivefold_nonSpectralExcursionAlternative hH3
          (t (v k)) (w (v k)) (δ k) (σ (v k))
          (M (v k)) (q (v k)) (sSource k) ∨
        ε k ^ 2 ≤ 2 * (3 * h3TerminalRadialSobolevWeightSquareCeiling (R k)) *
          (‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ *
            w (v k)) ^ 2 ∨
        R k ^ 2 * ε k ^ 2 < 8 * velocityH3DissipationAt u (t (v k)) ∨
        (0 < η k ∧
          η k < γ / (R k ^ 2 * ε k ^ 2 / 8) ∧
          ∀ r : ℝ, r ∈ Set.Icc (p k) (p k + η k) →
            R k ^ 2 * ε k ^ 2 / 8 <
              h3PathActualLowRadialDissipation244 ((N k : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 r) ∧
            R k ^ 2 * ε k ^ 2 / 8 < velocityH3DissipationAt u r) := by
    filter_upwards [hShort γ hγ] with k hk
    intro hThreshold
    rcases hGate k hThreshold with hNonSpectral | hClock | hAnchor | hInternal
    · exact Or.inl hNonSpectral
    · exact Or.inr (Or.inl hClock)
    · exact Or.inr (Or.inr (Or.inl hAnchor))
    · exact Or.inr (Or.inr (Or.inr ⟨hInternal.1, hk, hInternal.2⟩))
  exact ⟨i, t, w, v, sSource, sState, δ, p, η, N,
    hv, hLimit, hSeparate, hSummable, hCharge, hBudget,
    hGate, hShort, hRefined⟩

end
end PrimeTensor.Bridge.Euclidean
