import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorHalfGapHighTail244
import Mathlib.Tactic

/-!
# Canonical half-height low-frequency plateau and near-half high-tail alternative

The exact canonical quadratic-sharp clock makes the complete outer LOW-Q
physical projected-PDE variation smaller than half the actual full H³
anchor dissipation. The physical low/high radial partition then gives,
at EVERY time in the same clock window,

  D₃(s) > D₃(t)/2 - H_Q(t).

Integration against actual full physical H³ dissipation forces the
window charge of this half-height deficit to vanish. Consequently, for
EVERY fixed beta < 1/2 and epsilon > 0, the original canonical windows
must eventually satisfy delta D <= epsilon OR H_Q > beta D. The beta
may be arbitrarily close to 1/2 and need not be fixed to 1/4.

No persistence or small source-action hypothesis is added. The usual
no-terminal-L²-trace and finite-full-H³-dissipation premises remain explicit.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- If the complete low-frequency part can lose at most B and the new
high-frequency part is nonnegative, the full physical dissipation at
all future times is bounded below by its original low-frequency part
minus B. This is a simple exact-partition inequality. -/
theorem h3Path_scalar_lowPDEVariation_forces_fullPlateau244
    (D₀ D₁ L₀ L₁ H₀ H₁ B : ℝ)
    (hD₀ : D₀ = L₀ + H₀)
    (hD₁ : D₁ = L₁ + H₁)
    (hVariation : |L₀ - L₁| ≤ B)
    (hH₁ : 0 ≤ H₁) :
    D₀ - H₀ - B ≤ D₁ := by
  have hLow : L₀ - L₁ ≤ B :=
    (le_abs_self (L₀ - L₁)).trans hVariation
  linarith only [hD₀, hD₁, hLow, hH₁]

/-- The physical projected-momentum PDE controls the actual low-Q
channel and hence the FULL untruncated dissipation from below, apart
from the initial HIGH-Q mass and a *single-cutoff* quadratic rate.
This does not bound high-frequency motion itself. -/
theorem h3Path_physicalPDE_outerLow_forces_fullPlateau244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (Q K C t δ s : ℝ)
    (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hδ : 0 < δ) (ht : t ∈ Set.Ioo a T) (hEnd : t + δ < T)
    (hs : s ∈ Set.Icc t (t + δ))
    (hBase : ∀ j : Fin 3,
      ‖(h3AuditActualSpectralVelocityTotal hH3 t) j‖ ≤ K)
    (hSource : ∀ r : ℝ, r ∈ Set.Icc t (t + δ) →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C) :
    velocityH3DissipationAt u t -
      h3PathActualHighRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      ((6 * (Q + 1) * K * h3PathLowRadialPDEGradientRate244 Q C) * δ +
        (3 * (h3PathLowRadialPDEGradientRate244 Q C) ^ 2) * δ ^ 2) ≤
      velocityH3DissipationAt u s := by
  let L : ℝ → ℝ := fun r =>
    h3PathActualLowRadialDissipation244 Q
      (h3AuditActualSpectralVelocityTotal hH3 r)
  let H : ℝ → ℝ := fun r =>
    h3PathActualHighRadialDissipation244 Q
      (h3AuditActualSpectralVelocityTotal hH3 r)
  let Λ : ℝ := 6 * (Q + 1) * K * h3PathLowRadialPDEGradientRate244 Q C
  let Ξ : ℝ := 3 * (h3PathLowRadialPDEGradientRate244 Q C) ^ 2
  have hC : 0 ≤ C := by
    have htMem : t ∈ Set.Icc t (t + δ) :=
      ⟨le_rfl, le_add_of_nonneg_right hδ.le⟩
    exact (norm_nonneg _).trans (hSource t htMem)
  have hV : 0 ≤ h3PathLowRadialPDEGradientRate244 Q C :=
    h3Path_lowRadialPDEGradientRate_nonneg244 Q C hQ hC
  have hΛ : 0 ≤ Λ := by
    dsimp only [Λ]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (by linarith only [hQ])) hK) hV
  have hΞ : 0 ≤ Ξ := by dsimp only [Ξ]; positivity
  have htAbs : t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 ht.1, ht.2⟩
  have hsClass : s ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hEnd⟩
  have hsAbs : s ∈ Set.Ioo (0 : ℝ) T :=
    ⟨lt_trans hClass.terminal_start.1 hsClass.1, hsClass.2⟩
  have hElapsed : 0 ≤ s - t := sub_nonneg.mpr hs.1
  have hElapsedLe : s - t ≤ δ := by linarith only [hs.2]
  have hElapsedSq : (s - t) ^ 2 ≤ δ ^ 2 :=
    pow_le_pow_left₀ hElapsed hElapsedLe 2
  have hVariation : |L t - L s| ≤ Λ * (s - t) + Ξ * (s - t) ^ 2 := by
    exact h3Path_actualLowRadialDissipationVariation_anchoredPDE244
      hH3 Q K hQ hK t s C htAbs hsAbs hs.1 hBase
      (fun r hr => hSource r ⟨hr.1, le_trans hr.2 hs.2⟩)
  have hMax : |L t - L s| ≤ Λ * δ + Ξ * δ ^ 2 := by
    calc
      _ ≤ Λ * (s - t) + Ξ * (s - t) ^ 2 := hVariation
      _ ≤ Λ * δ + Ξ * δ ^ 2 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hElapsedLe hΛ)
          (mul_le_mul_of_nonneg_left hElapsedSq hΞ)
  have htPartition : velocityH3DissipationAt u t = L t + H t := by
    simpa only [L, H] using
      (h3Path_actualRadialDissipation_partition244 hH3 hClass t ht Q).symm
  have hsPartition : velocityH3DissipationAt u s = L s + H s := by
    simpa only [L, H] using
      (h3Path_actualRadialDissipation_partition244 hH3 hClass s hsClass Q).symm
  have hHighNonneg : 0 ≤ H s := by
    dsimp only [H, h3PathActualHighRadialDissipation244]
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg _ ξ
  have hBound := h3Path_scalar_lowPDEVariation_forces_fullPlateau244
    (velocityH3DissipationAt u t) (velocityH3DissipationAt u s)
    (L t) (L s) (H t) (H s) (Λ * δ + Ξ * δ ^ 2)
    htPartition hsPartition hMax hHighNonneg
  simpa only [L, H, Λ, Ξ] using hBound

/-- With an actual outer low-Q PDE budget below half the initial full
H³ dissipation, the full physical dissipation stays above its initial
half-height minus the initial genuine high-frequency tail. Its exact
physical time integral therefore pays the corresponding deficit cost. -/
theorem h3Path_physicalPDE_halfHeightDeficit_integratedCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (Q K C t δ : ℝ)
    (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hδ : 0 < δ) (ht : t ∈ Set.Ioo a T) (hEnd : t + δ < T)
    (hBase : ∀ j : Fin 3,
      ‖(h3AuditActualSpectralVelocityTotal hH3 t) j‖ ≤ K)
    (hSource : ∀ r : ℝ, r ∈ Set.Icc t (t + δ) →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hBudget :
      (6 * (Q + 1) * K * h3PathLowRadialPDEGradientRate244 Q C) * δ +
        (3 * (h3PathLowRadialPDEGradientRate244 Q C) ^ 2) * δ ^ 2 <
      velocityH3DissipationAt u t / 2) :
    δ * (velocityH3DissipationAt u t / 2 -
      h3PathActualHighRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t)) ≤
      ∫ s in t..(t + δ), velocityH3DissipationAt u s := by
  have hFloor (s : ℝ) (hs : s ∈ Set.Icc t (t + δ)) :
      velocityH3DissipationAt u t / 2 -
        h3PathActualHighRadialDissipation244 Q
          (h3AuditActualSpectralVelocityTotal hH3 t) ≤
        velocityH3DissipationAt u s := by
    have hPlateau := h3Path_physicalPDE_outerLow_forces_fullPlateau244
      hH3 hClass Q K C t δ s hQ hK hδ ht hEnd hs hBase hSource
    linarith only [hPlateau, hBudget]
  have hSubInt : IntervalIntegrable (velocityH3DissipationAt u)
      volume t (t + δ) := by
    apply hDInt.mono_set
    rw [Set.uIcc_of_le (le_add_of_nonneg_right hδ.le),
      Set.uIcc_of_le hClass.terminal_start.2.le]
    exact Set.Icc_subset_Icc ht.1.le hEnd.le
  have hCompare :
      (∫ _s in t..(t + δ),
        velocityH3DissipationAt u t / 2 -
          h3PathActualHighRadialDissipation244 Q
            (h3AuditActualSpectralVelocityTotal hH3 t)) ≤
      ∫ s in t..(t + δ), velocityH3DissipationAt u s :=
    intervalIntegral.integral_mono_on
      (le_add_of_nonneg_right hδ.le)
      intervalIntegrable_const hSubInt hFloor
  have hConst :
      (∫ _s in t..(t + δ),
        velocityH3DissipationAt u t / 2 -
          h3PathActualHighRadialDissipation244 Q
            (h3AuditActualSpectralVelocityTotal hH3 t)) =
        δ * (velocityH3DissipationAt u t / 2 -
          h3PathActualHighRadialDissipation244 Q
            (h3AuditActualSpectralVelocityTotal hH3 t)) := by
    simp <;> ring
  exact hConst ▸ hCompare

/-- A vanishing integrated mass forces the anchor charge to collapse
unless the high-frequency fraction exceeds ANY prescribed beta < 1/2.
This is a quantitative consequence of the exact half-height deficit
charge, and requires no cliff-time extraction. -/
theorem h3Path_scalar_halfHeightDeficit_chargeOrHighTail244
    (D H I δ : ℕ → ℝ)
    (hWidth : ∀ k, 0 < δ k)
    (hMassZero : Tendsto I atTop (𝓝 (0 : ℝ)))
    (hCharge : ∀ k, δ k * (D k / 2 - H k) ≤ I k)
    (β ε : ℝ) (hβ : β < 1 / 2) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      δ k * D k ≤ ε ∨ β * D k < H k := by
  let θ : ℝ := 1 / 2 - β
  have hθ : 0 < θ := by dsimp only [θ]; linarith only [hβ]
  have hSmall : ∀ᶠ k : ℕ in atTop, I k < θ * ε :=
    hMassZero.eventually (eventually_lt_nhds (mul_pos hθ hε))
  filter_upwards [hSmall] with k hk
  by_cases hTail : β * D k < H k
  · exact Or.inr hTail
  · have hTailLe : H k ≤ β * D k := le_of_not_gt hTail
    have hLower : θ * D k ≤ D k / 2 - H k := by
      dsimp only [θ]
      linarith only [hTailLe]
    have hScaled : θ * (δ k * D k) ≤ I k := by
      calc
        θ * (δ k * D k) = δ k * (θ * D k) := by ring
        _ ≤ δ k * (D k / 2 - H k) :=
          mul_le_mul_of_nonneg_left hLower (hWidth k).le
        _ ≤ I k := hCharge k
    have hStrict : θ * (δ k * D k) < θ * ε := lt_of_le_of_lt hScaled hk
    have hChargeLe : δ k * D k ≤ ε := by
      by_contra hNot
      have hRev : ε ≤ δ k * D k :=
        (lt_of_not_ge hNot).le
      have hMul : θ * ε ≤ θ * (δ k * D k) :=
        mul_le_mul_of_nonneg_left hRev hθ.le
      exact (not_lt_of_ge hMul) hStrict
    exact Or.inl hChargeLe

/-- The ORIGINAL canonical windows satisfy an intrinsic half-height
low-frequency persistence cost. For EVERY beta < 1/2, either their
physical anchor-height charges are arbitrarily small eventually, or
the actual high-Q dissipation occupies more than beta of the full H³
anchor height. If the height charge stays bounded below by eta > 0,
then EVERY fixed beta < 1/2 is eventually achieved on the SAME anchors.
No separate source-action or regularity hypothesis is added. -/
theorem h3Path_noL2Trace_exactAnchor_halfHeightChargeOrNearHalfHighTail244
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
        (velocityH3DissipationAt u (τ (v k)) / 2 -
          h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ≤
        ∫ s in τ (v k)..(τ (v k) + δ (v k)),
          velocityH3DissipationAt u s) ∧
      (∀ β ε : ℝ, β < 1 / 2 → 0 < ε → ∀ᶠ k : ℕ in atTop,
        δ (v k) * velocityH3DissipationAt u (τ (v k)) ≤ ε ∨
          β * velocityH3DissipationAt u (τ (v k)) <
            h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ η : ℝ, 0 < η →
        (∀ᶠ k : ℕ in atTop,
          η ≤ δ (v k) * velocityH3DissipationAt u (τ (v k))) →
        ∀ β : ℝ, β < 1 / 2 → ∀ᶠ k : ℕ in atTop,
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
  have hKnonneg (k : ℕ) : 0 ≤ K (v k) := by
    rw [hK k]
    exact norm_nonneg _
  have hCost (k : ℕ) :
      δ (v k) *
        (velocityH3DissipationAt u (τ (v k)) / 2 -
          h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ≤
        ∫ s in τ (v k)..(τ (v k) + δ (v k)),
          velocityH3DissipationAt u s := by
    let t : ℝ := τ (v k)
    let b : ℝ := (T - t) / 2
    let Q : ℝ := (N (v k) : ℝ) + 1
    have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
    have hb : 0 < b := by dsimp only [b, t]; linarith only [(hTime (v k)).2]
    have htb : t < t + b := by linarith only [hb]
    have hbT : t + b < T := by
      dsimp only [b, t]
      linarith only [(hTime (v k)).2]
    have hδBound : δ (v k) ≤ b / 2 := by
      rw [hExact k]
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
        hH3 (lt_trans hClass.terminal_start.1 (hTime (v k)).1)
        htb hbT r hrHalf
      simpa only [hC k, t, b] using hBound
    have hBase : ∀ j : Fin 3,
        ‖(h3AuditActualSpectralVelocityTotal hH3 t) j‖ ≤ K (v k) := by
      intro j
      rw [hK k]
      exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).1 le_rfl j
    have hBudget := h3Path_exactAnchor_outerLowBudget_lt_halfDissipation244
      hH3 hClass τ N K C δ v k (hTime (v k))
      (hK k) (hCnonneg k) (hExact k) (hGap k)
    have hIntegrated := h3Path_physicalPDE_halfHeightDeficit_integratedCost244
      hH3 hClass hDInt Q (K (v k)) (C (v k)) t (δ (v k))
      hQ (hKnonneg k) (hWidth k) (hTime (v k)) (hEnd k)
      hBase hSource
      (by simpa only [Q, h3PathCubicAnnulusOuterLowLinearRate244,
        h3PathCubicAnnulusOuterLowQuadraticRate244, t] using hBudget)
    simpa only [Q, t] using hIntegrated
  have hMassZero : Tendsto (fun k =>
      ∫ r in τ (v k)..(τ (v k) + δ (v k)),
        velocityH3DissipationAt u r) atTop (𝓝 (0 : ℝ)) := by
    have hSummable := h3Path_disjointNonnegativeWindows_fullIntegral_summable244
      (velocityH3DissipationAt u) a T
      (fun k => τ (v k)) (fun k => δ (v k))
      hClass.terminal_start.2.le
      (fun r => velocityH3DissipationAt_nonneg u r)
      hDInt (fun k => (hTime (v k)).1.le)
      (fun k => (hWidth k).le) (fun k => (hEnd k).le)
      (fun k => (hSeparate k (k + 1) (Nat.lt_succ_self k)).le)
    exact hSummable.tendsto_atTop_zero
  have hAlt (β ε : ℝ) (hβ : β < 1 / 2) (hε : 0 < ε) :
      ∀ᶠ k : ℕ in atTop,
        δ (v k) * velocityH3DissipationAt u (τ (v k)) ≤ ε ∨
          β * velocityH3DissipationAt u (τ (v k)) <
            h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
    exact h3Path_scalar_halfHeightDeficit_chargeOrHighTail244
      (fun k => velocityH3DissipationAt u (τ (v k)))
      (fun k => h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))
      (fun k => ∫ r in τ (v k)..(τ (v k) + δ (v k)),
        velocityH3DissipationAt u r)
      (fun k => δ (v k)) hWidth hMassZero hCost β ε hβ hε
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
    hSeparate, ?_, hCost, hAlt, ?_⟩
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
