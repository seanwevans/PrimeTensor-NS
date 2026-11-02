import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousAnnularPDEBudget
import Mathlib.Tactic

/-!
# Terminal physical annular PDE clock or superquadratic rate obstruction

The preceding theorem proves summability of the *physically certified* annular
persistence charges, with exact widths

  theta(k) = min (d(k)/2) (H(k)/(8*(Lambda(k)+1)))

on the active branch. Since theta(k)*H(k)/4 tends to zero, for every fixed
c>0 and M>0 sufficiently late active windows obey

  d(k)*H(k) < c  OR  M*H(k)^2 < Lambda(k)+1.

The second alternative is the **superquadratic variation-rate requirement**:
if the source-window duration does not collapse faster than inverse height,
then the true projected-momentum PDE annular variation coefficient must grow
faster than every fixed multiple of the squared spike height. Conversely,
if the PDE rate is eventually bounded by such a multiple on active indices,
the remaining physical source duration must collapse at the inverse-height
scale. These statements use the same cofinal physical witnesses and four-way
gate; they do not close a Navier--Stokes continuation theorem.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Exact quantitative dichotomy extracted from the genuine PDE-certified
annular charge: no artificial lower persistence width is introduced. -/
theorem h3Critical_scalar_annularPDE_eventualClockOrSuperquadraticRate
    (active : ℕ → Prop) (d H Λ : ℕ → ℝ)
    (hΛ : ∀ k : ℕ, 0 ≤ Λ k)
    (hClock : ∀ γ : ℝ, 0 < γ → ∀ᶠ k : ℕ in atTop,
      ¬ active k ∨
      (d k / 2) * (H k / 4) < γ ∨
      ((H k / 4) / (2 * (Λ k + 1))) * (H k / 4) < γ)
    (c M : ℝ) (hc : 0 < c) (hM : 0 < M) :
    ∀ᶠ k : ℕ in atTop,
      ¬ active k ∨ d k * H k < c ∨ M * (H k) ^ 2 < Λ k + 1 := by
  let γ : ℝ := min (c / 8) (1 / (32 * M))
  have hγ : 0 < γ := by
    dsimp only [γ]
    exact lt_min (by positivity) (by positivity)
  have hLate := hClock γ hγ
  filter_upwards [hLate] with k hk
  rcases hk with hInactive | hShort | hRate
  · exact Or.inl hInactive
  · have hBound : γ ≤ c / 8 := min_le_left _ _
    exact Or.inr (Or.inl (by nlinarith only [hShort, hBound]))
  · have hBound : γ ≤ 1 / (32 * M) := min_le_right _ _
    have hDen : 0 < Λ k + 1 := by linarith only [hΛ k]
    have hEq : (H k / 4 / (2 * (Λ k + 1))) * (H k / 4) =
        H k ^ 2 / (32 * (Λ k + 1)) := by
      field_simp [ne_of_gt hDen] <;> ring
    rw [hEq] at hRate
    have hFrac : H k ^ 2 / (32 * (Λ k + 1)) < 1 / (32 * M) :=
      lt_of_lt_of_le hRate hBound
    have hCross : H k ^ 2 * (32 * M) <
        (1 : ℝ) * (32 * (Λ k + 1)) :=
      (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 32 * (Λ k + 1))
        (by positivity : (0 : ℝ) < 32 * M)).mp hFrac
    exact Or.inr (Or.inr (by nlinarith only [hCross]))

/-- A source/PDE rate ceiling on active slots forces collapse of their
remaining source-window duration at the inverse-height scale. -/
theorem h3Critical_scalar_annularPDE_boundedRate_forces_clockCollapse
    (active : ℕ → Prop) (d H Λ : ℕ → ℝ)
    (hAlt : ∀ c M : ℝ, 0 < c → 0 < M →
      ∀ᶠ k : ℕ in atTop,
        ¬ active k ∨ d k * H k < c ∨ M * H k ^ 2 < Λ k + 1)
    (M : ℝ) (hM : 0 < M)
    (hRate : ∀ᶠ k : ℕ in atTop,
      active k → Λ k + 1 ≤ M * H k ^ 2) :
    ∀ c : ℝ, 0 < c →
      ∀ᶠ k : ℕ in atTop, ¬ active k ∨ d k * H k < c := by
  intro c hc
  filter_upwards [hAlt c M hc hM, hRate] with k hk hCeiling
  rcases hk with hInactive | hShort | hSuper
  · exact Or.inl hInactive
  · exact Or.inr hShort
  · by_cases ha : active k
    · exact False.elim ((not_le_of_gt hSuper) (hCeiling ha))
    · exact Or.inl ha

/-- Same fivefold synchronized source/state peaks and physical four-way gate.
The annular dissipation budget now yields the final quantitative physical
choice: either no active annulus, inverse-height source clock collapse, or
variation-rate growth faster than ANY prescribed multiple of H^2. -/
theorem h3Critical_noL2Trace_cofinalFivefold_annularClockRateBarrier
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
    (L : ℕ → ℕ)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ i : Fin 3, ∃ t w : ℕ → ℝ, ∃ v : ℕ → ℕ,
    ∃ sSource sState δ p η : ℕ → ℝ, ∃ N : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k : ℕ => t (v k)) atTop (𝓝 T) ∧
      (∀ c₀ M₀ : ℝ, 0 < c₀ → 0 < M₀ → ∀ᶠ k : ℕ in atTop,
        ¬ (η k ≠ 0 ∧
          8 * velocityH3Energy0At u b * ((L k : ℝ) + 1) ^ 8 <
            R k ^ 2 * ε k ^ 2 / 8) ∨
        (t (v k) + w (v k) - p k) *
          (R k ^ 2 * ε k ^ 2 / 8) < c₀ ∨
        M₀ * (R k ^ 2 * ε k ^ 2 / 8) ^ 2 <
          h3PathFiniteAnnulusPDEVariationCoefficient244
            ((L k : ℝ) + 1) ((N k : ℝ) + 1)
            ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖
            ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ + 1) ∧
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
            R k ^ 2 * ε k ^ 2 / 8 < velocityH3DissipationAt u r)) := by
  obtain ⟨i, t, w, v, sSource, sState, δ, p, η, N, θ,
      hv, hLimit, _hThetaEq, _hInside, _hSeparate,
      _hSummable, _hChargeZero, _hBound, hClock, hGate⟩ :=
    h3Critical_noL2Trace_cofinalFivefold_annularPDEBudget
      hH3 hClass b hb hNoTrace c ρ σ M q
      hc hcLimit hρ hσ hM hq R ε hR hε L hDInt
  let H : ℕ → ℝ := fun k => R k ^ 2 * ε k ^ 2 / 8
  let rate : ℕ → ℝ := fun k =>
    h3PathFiniteAnnulusPDEVariationCoefficient244
      ((L k : ℝ) + 1) ((N k : ℝ) + 1)
      ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖
      ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖
  let d : ℕ → ℝ := fun k => t (v k) + w (v k) - p k
  let active : ℕ → Prop := fun k => η k ≠ 0 ∧
    8 * velocityH3Energy0At u b * ((L k : ℝ) + 1) ^ 8 < H k
  have hRate (k : ℕ) : 0 ≤ rate k := by
    exact h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
      ((L k : ℝ) + 1) ((N k : ℝ) + 1)
      ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖
      ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖
      (norm_nonneg _) (norm_nonneg _)
  have hOldClock : ∀ γ : ℝ, 0 < γ → ∀ᶠ k : ℕ in atTop,
      ¬ active k ∨
      (d k / 2) * (H k / 4) < γ ∨
      ((H k / 4) / (2 * (rate k + 1))) * (H k / 4) < γ := by
    intro γ hγ
    simpa only [active, d, H, rate] using hClock γ hγ
  have hNewClock (c₀ M₀ : ℝ) (hc₀ : 0 < c₀) (hM₀ : 0 < M₀) :
      ∀ᶠ k : ℕ in atTop,
        ¬ active k ∨ d k * H k < c₀ ∨ M₀ * (H k) ^ 2 < rate k + 1 :=
    h3Critical_scalar_annularPDE_eventualClockOrSuperquadraticRate
      active d H rate hRate hOldClock c₀ M₀ hc₀ hM₀
  refine ⟨i, t, w, v, sSource, sState, δ, p, η, N,
    hv, hLimit, ?_, hGate⟩
  intro c₀ M₀ hc₀ hM₀
  simpa only [active, d, H, rate] using hNewClock c₀ M₀ hc₀ hM₀

end
end PrimeTensor.Bridge.Euclidean
