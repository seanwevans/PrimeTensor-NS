import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorNearHalfHighTail244
import Mathlib.Tactic

/-!
# Exact canonical half-LOW-frequency persistence forces near-total high-tail mass

The source-aware quadratic-sharp clock does not merely bound the outer low-Q
variation by D(anchor)/2. Its budget is at most HALF THE EXACT ANNULAR GAP,
which is strictly smaller than the LOW-Q dissipation at the anchor.
Therefore the physical low-Q dissipation can lose less than half its own
anchor mass during the entire original window. Full dissipation dominates
low-Q dissipation there, giving the quantitative actual window cost

   delta_k * (D_k-H_{Q_k}(anchor))/2 <= I_k.

Because these full physical masses I_k are summable, the low-frequency
weighted anchor costs are summable. On the same canonical cofinal windows,
for each beta<1 and epsilon>0, eventually delta D<=epsilon OR H_Q>beta D.
If delta D has a positive eventual lower bound, the high-Q fractions exceed
every fixed beta<1 eventually. The charge lower bound is NOT established.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The canonical exact annular PDE gap is strictly below the genuine
physical LOW-Q dissipation. This uses nonnegativity of the actual LOW-R
spectral density and the positive cubic radial charge. -/
theorem h3Path_exactAnchor_gap_lt_outerLowDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (v : ℕ → ℕ) (k : ℕ) :
    h3PathCubicAnnulusActualGap244 hH3 τ N (v k) <
      h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
  have hLowR : 0 ≤
      h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
    unfold h3PathActualLowRadialDissipation244
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg _ ξ
  have hCubic : 0 < ((v k : ℝ) + 1) ^ 3 := by positivity
  unfold h3PathCubicAnnulusActualGap244
  linarith only [hLowR, hCubic]

/-- The unchanged quadratic-sharp selector bounds the WHOLE outer low-Q
projected-PDE variation by half the anchor LOW-Q physical dissipation.
This is sharper than the old bound in terms of total D(anchor). -/
theorem h3Path_exactAnchor_outerLowBudget_lt_halfLow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
    (v : ℕ → ℕ) (k : ℕ)
    (ht : τ (v k) ∈ Set.Ioo a T)
    (hK : K (v k) = ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖)
    (hC : 0 ≤ C (v k))
    (hExact : δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
      ((T - τ (v k)) / 2)
      (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
      (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
      (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)))
    (hGap : ((v k : ℝ) + 1) ^ 3 / 4 <
      h3PathCubicAnnulusActualGap244 hH3 τ N (v k)) :
    h3PathCubicAnnulusOuterLowLinearRate244 N K C (v k) * δ (v k) +
      h3PathCubicAnnulusOuterLowQuadraticRate244 N C (v k) * δ (v k) ^ 2 <
      h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) / 2 := by
  let t : ℝ := τ (v k)
  let R : ℝ := (v k : ℝ) + 1
  let Q : ℝ := (N (v k) : ℝ) + 1
  let g : ℝ := h3PathCubicAnnulusActualGap244 hH3 τ N (v k)
  let Λ : ℝ := h3PathCubicAnnulusActualLinearRate244 N K C (v k)
  let Ξ : ℝ := h3PathCubicAnnulusActualQuadraticRate244 N C (v k)
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hK0 : 0 ≤ K (v k) := by rw [hK]; exact norm_nonneg _
  have hg : 0 < g := by
    have hR3 : 0 < R ^ 3 := by dsimp only [R]; positivity
    dsimp only [g, R] at hGap ⊢
    linarith only [hGap, hR3]
  have hb : 0 < (T - t) / 2 := by
    dsimp only [t]
    linarith only [ht.2]
  have hΛ : 0 ≤ Λ := by
    dsimp only [Λ, h3PathCubicAnnulusActualLinearRate244]
    exact h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
      R Q (K (v k)) (C (v k)) hK0 hC
  have hΞ : 0 ≤ Ξ := by
    dsimp only [Ξ, h3PathCubicAnnulusActualQuadraticRate244]
    exact h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244
      R Q (C (v k))
  have hδ : 0 ≤ δ (v k) := by
    obtain ⟨w, hw, hwpos, _, _, _⟩ :=
      h3Path_cubicAnnulusQuadraticSharpPDEWidth_valid244
        ((T - t) / 2) g Λ Ξ hb hg hΛ hΞ
    rw [hExact, ← hw]
    exact hwpos.le
  have hHalf := h3Path_quadraticSharpWidth_halfGapBudget244
    ((T - t) / 2) g Λ Ξ (δ (v k)) hb hg hΛ hΞ
    (by simpa only [t, g, Λ, Ξ] using hExact)
  have hOuter := h3Path_outerLowPDEBudget_le_annularBudget244
    R Q (K (v k)) (C (v k)) (δ (v k)) hR hQ hK0 hC hδ
  have hBudget :
      h3PathCubicAnnulusOuterLowLinearRate244 N K C (v k) * δ (v k) +
        h3PathCubicAnnulusOuterLowQuadraticRate244 N C (v k) * δ (v k) ^ 2 ≤
          g / 2 := by
    calc
      _ ≤ Λ * δ (v k) + Ξ * δ (v k) ^ 2 := by
        simpa only [R, Q, Λ, Ξ, h3PathCubicAnnulusActualLinearRate244,
          h3PathCubicAnnulusActualQuadraticRate244,
          h3PathCubicAnnulusOuterLowLinearRate244,
          h3PathCubicAnnulusOuterLowQuadraticRate244] using hOuter
      _ ≤ g / 2 := hHalf
  have hGapLow := h3Path_exactAnchor_gap_lt_outerLowDissipation244
    hH3 τ N v k
  dsimp only [g] at hBudget
  linarith only [hBudget, hGapLow]

/-- At every time of the ORIGINAL source-aware canonical window, the
full physical H³ dissipation dominates half the LOW-Q anchor dissipation.
There is no temporal continuity assumption on the full high-frequency tail. -/
theorem h3Path_exactAnchor_fullDissipation_ge_halfOuterLow244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
    (v : ℕ → ℕ) (k : ℕ) (s : ℝ)
    (ht : τ (v k) ∈ Set.Ioo a T)
    (hK : K (v k) = ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖)
    (hCexact : C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
      (τ (v k)) (τ (v k) + (T - τ (v k)) / 2))
    (hC : 0 ≤ C (v k))
    (hExact : δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
      ((T - τ (v k)) / 2)
      (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
      (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
      (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)))
    (hδ : 0 < δ (v k))
    (hEnd : τ (v k) + δ (v k) < T)
    (hg : ((v k : ℝ) + 1) ^ 3 / 4 <
      h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
    (hs : s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k))) :
    h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
      (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) / 2 ≤
        velocityH3DissipationAt u s := by
  let t : ℝ := τ (v k)
  let b : ℝ := (T - t) / 2
  let Q : ℝ := (N (v k) : ℝ) + 1
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hK0 : 0 ≤ K (v k) := by rw [hK]; exact norm_nonneg _
  have hb : 0 < b := by dsimp only [b, t]; linarith only [ht.2]
  have htb : t < t + b := by linarith only [hb]
  have hbT : t + b < T := by dsimp only [b, t]; linarith only [ht.2]
  have hδBound : δ (v k) ≤ b / 2 := by
    rw [hExact]
    change h3PathCubicAnnulusQuadraticSharpPDEWidth244 b _ _ _ ≤ b / 2
    unfold h3PathCubicAnnulusQuadraticSharpPDEWidth244
    exact min_le_left _ _
  have hδLe : δ (v k) ≤ b := by linarith only [hδBound, hb]
  have hSource (r : ℝ)
      (hr : r ∈ Set.Icc t (t + δ (v k))) :
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C (v k) := by
    have hrHalf : r ∈ Set.Icc t (t + b) := by
      constructor
      · exact hr.1
      · linarith only [hr.2, hδLe]
    have hBound := h3Path_actualSourceWindowEnvelope_pointwise_le244
      hH3 (lt_trans hClass.terminal_start.1 ht.1)
      htb hbT r hrHalf
    simpa only [hCexact, t, b] using hBound
  have hBase : ∀ j : Fin 3,
      ‖(h3AuditActualSpectralVelocityTotal hH3 t) j‖ ≤ K (v k) := by
    intro j
    rw [hK]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).1 le_rfl j
  have hBudget := h3Path_exactAnchor_outerLowBudget_lt_halfLow244
    hH3 τ N K C δ v k ht hK hC hExact hg
  have hPlateau := h3Path_physicalPDE_outerLow_forces_fullPlateau244
    hH3 hClass Q (K (v k)) (C (v k)) t (δ (v k)) s
    hQ hK0 hδ ht hEnd hs hBase hSource
  have hPart := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ht Q
  dsimp only [Q, t] at hPart hPlateau
  dsimp only [h3PathCubicAnnulusOuterLowLinearRate244,
    h3PathCubicAnnulusOuterLowQuadraticRate244] at hBudget
  linarith only [hBudget, hPlateau, hPart]

/-- Since the entire LOW-Q anchor state persists at half height over the
canonical window, the genuine full physical dissipation integral pays
half its LOW-Q anchor charge. No full-H³ temporal modulus is needed. -/
theorem h3Path_exactAnchor_outerLowIntegratedCharge244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
    (v : ℕ → ℕ) (k : ℕ)
    (ht : τ (v k) ∈ Set.Ioo a T)
    (hK : K (v k) = ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖)
    (hCexact : C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
      (τ (v k)) (τ (v k) + (T - τ (v k)) / 2))
    (hC : 0 ≤ C (v k))
    (hExact : δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
      ((T - τ (v k)) / 2)
      (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
      (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
      (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)))
    (hδ : 0 < δ (v k))
    (hEnd : τ (v k) + δ (v k) < T)
    (hg : ((v k : ℝ) + 1) ^ 3 / 4 <
      h3PathCubicAnnulusActualGap244 hH3 τ N (v k)) :
    δ (v k) *
      h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ≤
      2 * (∫ s in τ (v k)..(τ (v k) + δ (v k)),
        velocityH3DissipationAt u s) := by
  have hSubInt : IntervalIntegrable (velocityH3DissipationAt u)
      volume (τ (v k)) (τ (v k) + δ (v k)) := by
    apply hDInt.mono_set
    rw [Set.uIcc_of_le (le_add_of_nonneg_right hδ.le),
      Set.uIcc_of_le hClass.terminal_start.2.le]
    exact Set.Icc_subset_Icc ht.1.le hEnd.le
  have hCompare :
      (∫ _s in τ (v k)..(τ (v k) + δ (v k)),
        h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) / 2) ≤
      ∫ s in τ (v k)..(τ (v k) + δ (v k)),
        velocityH3DissipationAt u s := by
    exact intervalIntegral.integral_mono_on
      (le_add_of_nonneg_right hδ.le)
      intervalIntegrable_const hSubInt
      (fun s hs => h3Path_exactAnchor_fullDissipation_ge_halfOuterLow244
        hH3 hClass τ N K C δ v k s ht hK hCexact hC hExact
        hδ hEnd hg hs)
  have hConst :
      (∫ _s in τ (v k)..(τ (v k) + δ (v k)),
        h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) / 2) =
      δ (v k) *
        (h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) / 2) := by
    simp <;> ring
  have hCost :
      δ (v k) *
        (h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) / 2) ≤
      ∫ s in τ (v k)..(τ (v k) + δ (v k)),
        velocityH3DissipationAt u s := by
    exact hConst ▸ hCompare
  nlinarith only [hCost]

/-- Vanishing actual physical full-window cost and positive widths imply:
for every beta<1, either peak charge collapses, or more than beta of
actual anchor dissipation occupies the high-frequency tail. -/
theorem h3Path_scalar_lowWindowCharge_nearFullHighTail244
    (D H I δ : ℕ → ℝ)
    (hWidth : ∀ k, 0 < δ k)
    (hMassZero : Tendsto I atTop (𝓝 (0 : ℝ)))
    (hCharge : ∀ k, δ k * (D k - H k) ≤ 2 * I k)
    (β ε : ℝ) (hβ : β < 1) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      δ k * D k ≤ ε ∨ β * D k < H k := by
  let θ : ℝ := 1 - β
  have hθ : 0 < θ := by dsimp only [θ]; linarith only [hβ]
  have hMassTwice : Tendsto (fun k => 2 * I k) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hMassZero.const_mul (2 : ℝ)
  have hSmall : ∀ᶠ k : ℕ in atTop, 2 * I k < θ * ε :=
    hMassTwice.eventually (eventually_lt_nhds (mul_pos hθ hε))
  filter_upwards [hSmall] with k hk
  by_cases hTail : β * D k < H k
  · exact Or.inr hTail
  · have hTailLe : H k ≤ β * D k := le_of_not_gt hTail
    have hLower : θ * D k ≤ D k - H k := by
      dsimp only [θ]
      linarith only [hTailLe]
    have hScaled : θ * (δ k * D k) ≤ 2 * I k := by
      calc
        θ * (δ k * D k) = δ k * (θ * D k) := by ring
        _ ≤ δ k * (D k - H k) :=
          mul_le_mul_of_nonneg_left hLower (hWidth k).le
        _ ≤ 2 * I k := hCharge k
    have hStrict : θ * (δ k * D k) < θ * ε := lt_of_le_of_lt hScaled hk
    have hChargeLe : δ k * D k ≤ ε := by
      by_contra hNot
      have hRev : ε ≤ δ k * D k := (lt_of_not_ge hNot).le
      have hMul : θ * ε ≤ θ * (δ k * D k) :=
        mul_le_mul_of_nonneg_left hRev hθ.le
      exact (not_lt_of_ge hMul) hStrict
    exact Or.inl hChargeLe

/-- ORIGINAL exact-anchor canonical windows have a summable weighted
LOW-Q anchor charge, and hence a near-TOTAL high-frequency alternative:
for every beta<1, either delta D is eventually arbitrarily small or
the actual high-Q tail exceeds beta D. A persistent positive delta D
forces every fixed beta<1 on the SAME unreselected canonical anchors.
The persistence premise is still conditional. -/
theorem h3Path_noL2Trace_exactAnchor_lowChargeOrNearFullHighTail244
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
        0 < δ (v k)) ∧
      (∀ k, δ (v k) *
        h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ≤
        2 * (∫ s in τ (v k)..(τ (v k) + δ (v k)),
          velocityH3DissipationAt u s)) ∧
      Summable (fun k => δ (v k) *
        h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ β ε : ℝ, β < 1 → 0 < ε → ∀ᶠ k : ℕ in atTop,
        δ (v k) * velocityH3DissipationAt u (τ (v k)) ≤ ε ∨
          β * velocityH3DissipationAt u (τ (v k)) <
            h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ η : ℝ, 0 < η →
        (∀ᶠ k : ℕ in atTop,
          η ≤ δ (v k) * velocityH3DissipationAt u (τ (v k))) →
        ∀ β : ℝ, β < 1 → ∀ᶠ k : ℕ in atTop,
          β * velocityH3DissipationAt u (τ (v k)) <
            h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, _hSummable, hAll, _hBarrier, _hPeaks⟩ :=
    h3Path_noL2Trace_finiteDissipation_exactAnchorCanonicalThreeScale244
      hH3 hClass hMass hNoTrace hDInt
  have hK (k : ℕ) :
      K (v k) = ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ :=
    (hAll k).1
  have hC (k : ℕ) : C (v k) = h3PathActualProjectedSourceWindowEnvelope244
      hH3 (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) := by
    rcases hAll k with ⟨_, _, _, _, hc, _, _, _, _, _, _, _⟩
    exact hc
  have hWidth (k : ℕ) : 0 < δ (v k) := by
    rcases hAll k with ⟨_, _, _, _, _, _, hp, _, _, _, _, _⟩
    exact hp
  have hEnd (k : ℕ) : τ (v k) + δ (v k) < T := by
    rcases hAll k with ⟨_, _, _, _, _, _, _, hp, _, _, _, _⟩
    exact hp
  have hExact (k : ℕ) : δ (v k) =
      h3PathCubicAnnulusQuadraticSharpPDEWidth244
        ((T - τ (v k)) / 2)
        (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
        (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
        (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)) := by
    rcases hAll k with ⟨_, _, _, _, _, _, _, _, hp, _, _, _⟩
    exact hp
  have hGap (k : ℕ) : ((v k : ℝ) + 1) ^ 3 / 4 <
      h3PathCubicAnnulusActualGap244 hH3 τ N (v k) := by
    rcases hAll k with ⟨_, _, _, _, _, _, _, _, _, _, hp, _⟩
    exact hp
  have hCnonneg (k : ℕ) : 0 ≤ C (v k) := by
    rcases hAll k with ⟨_, _, _, _, _, hp, _, _, _, _, _, _⟩
    obtain ⟨s, _hs, hEq⟩ := hp
    rw [← hEq]
    exact norm_nonneg _
  have hLowCost (k : ℕ) :
      δ (v k) *
        h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) ≤
        2 * (∫ s in τ (v k)..(τ (v k) + δ (v k)),
          velocityH3DissipationAt u s) :=
    h3Path_exactAnchor_outerLowIntegratedCharge244
      hH3 hClass hDInt τ N K C δ v k (hTime (v k))
      (hK k) (hC k) (hCnonneg k) (hExact k)
      (hWidth k) (hEnd k) (hGap k)
  have hIntegralSummable : Summable (fun k =>
      ∫ r in τ (v k)..(τ (v k) + δ (v k)),
        velocityH3DissipationAt u r) :=
    h3Path_disjointNonnegativeWindows_fullIntegral_summable244
      (velocityH3DissipationAt u) a T
      (fun k => τ (v k)) (fun k => δ (v k))
      hClass.terminal_start.2.le
      (fun r => velocityH3DissipationAt_nonneg u r)
      hDInt (fun k => (hTime (v k)).1.le)
      (fun k => (hWidth k).le) (fun k => (hEnd k).le)
      (fun k => (hSeparate k (k + 1) (Nat.lt_succ_self k)).le)
  have hIntegralZero : Tendsto (fun k =>
      ∫ r in τ (v k)..(τ (v k) + δ (v k)),
        velocityH3DissipationAt u r) atTop (𝓝 (0 : ℝ)) :=
    hIntegralSummable.tendsto_atTop_zero
  have hLowNonneg (k : ℕ) : 0 ≤ δ (v k) *
      h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
    apply mul_nonneg (hWidth k).le
    unfold h3PathActualLowRadialDissipation244
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg _ ξ
  have hLowSummable : Summable (fun k => δ (v k) *
      h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) := by
    have hMajor : Summable (fun k =>
        2 * (∫ r in τ (v k)..(τ (v k) + δ (v k)),
          velocityH3DissipationAt u r)) :=
      Summable.mul_left 2 hIntegralSummable
    exact hMajor.of_nonneg_of_le hLowNonneg hLowCost
  have hDiffCharge (k : ℕ) :
      δ (v k) *
        (velocityH3DissipationAt u (τ (v k)) -
          h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ≤
        2 * (∫ s in τ (v k)..(τ (v k) + δ (v k)),
          velocityH3DissipationAt u s) := by
    have hPartition := h3Path_actualRadialDissipation_partition244
      hH3 hClass (τ (v k)) (hTime (v k)) ((N (v k) : ℝ) + 1)
    calc
      δ (v k) *
          (velocityH3DissipationAt u (τ (v k)) -
            h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) =
          δ (v k) *
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
                rw [← hPartition]
                ring
      _ ≤ 2 * (∫ s in τ (v k)..(τ (v k) + δ (v k)),
          velocityH3DissipationAt u s) := hLowCost k
  have hAlt (β ε : ℝ) (hβ : β < 1) (hε : 0 < ε) :
      ∀ᶠ k : ℕ in atTop,
        δ (v k) * velocityH3DissipationAt u (τ (v k)) ≤ ε ∨
        β * velocityH3DissipationAt u (τ (v k)) <
          h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) :=
    h3Path_scalar_lowWindowCharge_nearFullHighTail244
      (fun k => velocityH3DissipationAt u (τ (v k)))
      (fun k => h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))
      (fun k => ∫ s in τ (v k)..(τ (v k) + δ (v k)),
        velocityH3DissipationAt u s)
      (fun k => δ (v k)) hWidth hIntegralZero hDiffCharge
      β ε hβ hε
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
    hSeparate, ?_, hLowCost, hLowSummable, hAlt, ?_⟩
  · intro k
    exact ⟨hK k, hC k, hWidth k⟩
  · intro η hη hPersistent β hβ
    have hHalf : 0 < η / 2 := by linarith only [hη]
    have hEventually := hAlt β (η / 2) hβ hHalf
    filter_upwards [hEventually, hPersistent] with k hk hCharge
    rcases hk with hSmall | hTail
    · exfalso
      linarith only [hSmall, hCharge, hη]
    · exact hTail

end
end PrimeTensor.FirstMonomialTriad
