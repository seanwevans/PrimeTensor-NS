import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessEndpointViscousAnnularClockRateBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceDropQuarticPhysicalClock
import Mathlib.Tactic

/-!
# Fifth-order cutoff cost of terminal annular projected-PDE variation

The physical PDE annular variation coefficient is not an abstract rate:
  Lambda(R,Q,K,C) = 6 K C ((Q+1)^2 sqrt(3 W3(Q)) +
                           (R+1)^2 sqrt(3 W3(R))).
Since W3(x) <= 4 x^6 for x >= 1, its positive square root gives
  Lambda(R,Q,K,C) <= 24 K C ((Q+1)^5 + (R+1)^5).

Thus, on a non-compressed, active high-H3 annular endpoint branch, the
previously necessary superquadratic Lambda/H^2 growth must be paid by the
actual spectral-state envelope, the actual physical projected-source
maximum, and the fifth powers of the two frequency cutoffs.

Neither K nor C nor the cutoffs are asserted terminal-uniform. The result
is a quantitative necessary condition, not terminal continuation.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- The square root of the radial H3 Fourier weight has cubic growth.
The extra two powers in the gradient multiplier produce a fifth-order
PDE variation coefficient. -/
theorem h3Critical_annularPDE_sqrtWeight_le_cubicCutoff
    (Q : ℝ) (hQ : 1 ≤ Q) :
    Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling Q) ≤
      4 * (Q + 1) ^ 3 := by
  have hWeight := h3Critical_quarticClock_radialWeight_le_fourSixth Q hQ
  have hQNonneg : 0 ≤ Q := by linarith only [hQ]
  have hQCube : Q ^ 3 ≤ (Q + 1) ^ 3 := by
    apply pow_le_pow_left₀ hQNonneg
    linarith
  have hBound :
      3 * h3TerminalRadialSobolevWeightSquareCeiling Q ≤
        (4 * Q ^ 3) ^ 2 := by
    have hSix : 0 ≤ Q ^ 6 := by positivity
    nlinarith only [hWeight, hSix]
  have hRoot :
      Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling Q) ≤
        4 * Q ^ 3 :=
    (Real.sqrt_le_iff).2 ⟨by positivity, hBound⟩
  exact hRoot.trans (mul_le_mul_of_nonneg_left hQCube (by norm_num))

/-- The actual annular source-rate coefficient has polynomial degree five
in each radial endpoint, with no future-time full-H3 derivative premise. -/
theorem h3Critical_annularPDE_variationRate_le_quinticPhysicalProduct
    (R Q K C : ℝ) (hR : 1 ≤ R) (hQ : 1 ≤ Q)
    (hK : 0 ≤ K) (hC : 0 ≤ C) :
    h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C ≤
      24 * K * C * ((Q + 1) ^ 5 + (R + 1) ^ 5) := by
  have hQRoot := h3Critical_annularPDE_sqrtWeight_le_cubicCutoff Q hQ
  have hRRoot := h3Critical_annularPDE_sqrtWeight_le_cubicCutoff R hR
  have hQCost :
      (Q + 1) ^ 2 *
          Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling Q) ≤
        4 * (Q + 1) ^ 5 := by
    calc
      _ ≤ (Q + 1) ^ 2 * (4 * (Q + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left hQRoot (sq_nonneg _)
      _ = 4 * (Q + 1) ^ 5 := by ring
  have hRCost :
      (R + 1) ^ 2 *
          Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling R) ≤
        4 * (R + 1) ^ 5 := by
    calc
      _ ≤ (R + 1) ^ 2 * (4 * (R + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left hRRoot (sq_nonneg _)
      _ = 4 * (R + 1) ^ 5 := by ring
  have hFactor : 0 ≤ 6 * K * C := by positivity
  calc
    h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C =
        6 * K * C *
          ((Q + 1) ^ 2 *
            Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling Q) +
           (R + 1) ^ 2 *
            Real.sqrt (3 * h3TerminalRadialSobolevWeightSquareCeiling R)) := rfl
    _ ≤ 6 * K * C * (4 * (Q + 1) ^ 5 + 4 * (R + 1) ^ 5) :=
      mul_le_mul_of_nonneg_left (add_le_add hQCost hRCost) hFactor
    _ = 24 * K * C * ((Q + 1) ^ 5 + (R + 1) ^ 5) := by ring

/-- The committed clock/rate dichotomy, with the exact physical PDE rate
replaced by its proved fifth-order source/state/frequency upper bound. -/
theorem h3Critical_scalar_annularQuinticPhysicalRateGate
    (active : ℕ → Prop) (d H Λ P : ℕ → ℝ)
    (hClock : ∀ c M : ℝ, 0 < c → 0 < M →
      ∀ᶠ k : ℕ in atTop,
        ¬ active k ∨ d k * H k < c ∨ M * H k ^ 2 < Λ k + 1)
    (hPoly : ∀ k : ℕ, Λ k ≤ P k)
    (c M : ℝ) (hc : 0 < c) (hM : 0 < M) :
    ∀ᶠ k : ℕ in atTop,
      ¬ active k ∨ d k * H k < c ∨ M * H k ^ 2 < P k + 1 := by
  filter_upwards [hClock c M hc hM] with k hk
  rcases hk with hInactive | hShort | hFast
  · exact Or.inl hInactive
  · exact Or.inr (Or.inl hShort)
  · exact Or.inr (Or.inr (lt_of_lt_of_le hFast (add_le_add (hPoly k) (le_refl (1 : ℝ)))))

/-- On the unchanged cofinal no-L2-trace witnesses, finite terminal H3
viscosity forces inverse-height compression or a superquadratic actual
source-state product multiplied by fifth-order cutoff weights. -/
theorem h3Critical_noL2Trace_cofinalFivefold_annularQuinticPhysicalRateGate
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
          24 * ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖ *
            ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ *
              (((N k : ℝ) + 2) ^ 5 + ((L k : ℝ) + 2) ^ 5) + 1) ∧
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
  obtain ⟨i, t, w, v, sSource, sState, δ, p, η, N,
      hv, hLimit, hClock, hGate⟩ :=
    h3Critical_noL2Trace_cofinalFivefold_annularClockRateBarrier
      hH3 hClass b hb hNoTrace c ρ σ M q
      hc hcLimit hρ hσ hM hq R ε hR hε L hDInt
  let active : ℕ → Prop := fun k => η k ≠ 0 ∧
    8 * velocityH3Energy0At u b * ((L k : ℝ) + 1) ^ 8 <
      R k ^ 2 * ε k ^ 2 / 8
  let d : ℕ → ℝ := fun k => t (v k) + w (v k) - p k
  let H : ℕ → ℝ := fun k => R k ^ 2 * ε k ^ 2 / 8
  let rate : ℕ → ℝ := fun k =>
    h3PathFiniteAnnulusPDEVariationCoefficient244
      ((L k : ℝ) + 1) ((N k : ℝ) + 1)
      ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖
      ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖
  let poly : ℕ → ℝ := fun k =>
    24 * ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖ *
      ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖ *
        (((N k : ℝ) + 2) ^ 5 + ((L k : ℝ) + 2) ^ 5)
  have hCut (k : ℕ) :
      (1 : ℝ) ≤ (L k : ℝ) + 1 ∧
        (1 : ℝ) ≤ (N k : ℝ) + 1 := by
    constructor
    · have h : (0 : ℝ) ≤ (L k : ℝ) := Nat.cast_nonneg _
      linarith only [h]
    · have h : (0 : ℝ) ≤ (N k : ℝ) := Nat.cast_nonneg _
      linarith only [h]
  have hRatePoly (k : ℕ) : rate k ≤ poly k := by
    have h := h3Critical_annularPDE_variationRate_le_quinticPhysicalProduct
      ((L k : ℝ) + 1) ((N k : ℝ) + 1)
      ‖h3AuditActualSpectralVelocityTotal hH3 (sState k)‖
      ‖h3PathActualProjectedMomentumSource244 hH3 (sSource k)‖
      (hCut k).1 (hCut k).2 (norm_nonneg _) (norm_nonneg _)
    simpa only [rate, poly, show (N k : ℝ) + 1 + 1 = (N k : ℝ) + 2 by ring,
      show (L k : ℝ) + 1 + 1 = (L k : ℝ) + 2 by ring] using h
  have hOriginal : ∀ c₀ M₀ : ℝ, 0 < c₀ → 0 < M₀ →
      ∀ᶠ k : ℕ in atTop,
        ¬ active k ∨ d k * H k < c₀ ∨ M₀ * H k ^ 2 < rate k + 1 := by
    intro c₀ M₀ hc₀ hM₀
    simpa only [active, d, H, rate] using hClock c₀ M₀ hc₀ hM₀
  have hPolyClock := h3Critical_scalar_annularQuinticPhysicalRateGate
    active d H rate poly hOriginal hRatePoly
  refine ⟨i, t, w, v, sSource, sState, δ, p, η, N,
    hv, hLimit, ?_, hGate⟩
  intro c₀ M₀ hc₀ hM₀
  simpa only [active, d, H, poly] using hPolyClock c₀ M₀ hc₀ hM₀

end
end PrimeTensor.Bridge.Euclidean
