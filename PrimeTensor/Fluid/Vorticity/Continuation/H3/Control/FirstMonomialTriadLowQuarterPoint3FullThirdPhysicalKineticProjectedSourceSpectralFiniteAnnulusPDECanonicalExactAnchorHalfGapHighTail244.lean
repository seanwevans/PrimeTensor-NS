import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorSourceActionTrichotomy244
import Mathlib.Tactic

/-!
# Exact canonical clock pays less than HALF the physical anchor dissipation

The canonical sharp quadratic selector allocates at most a quarter of its
annular gap to each of the linear and quadratic PDE time-variation terms.
The outer LOW-Q budget is a nonnegative sub-budget of this full annulus.
Because the exact gap is strictly below the physical H³ dissipation at
the original anchor, the whole low-Q variation is strictly less than
D₃(anchor)/2, with NO separate relative PDE rate premise.

An actual D₃ cliff below a quarter of its anchor height consequently
forces actual high-Q dissipation to exceed a quarter of D₃ at the anchor.
The disjoint-window argument gives the genuinely unconditional eventual
alternative: small anchor height-width charge OR large high-Q tail.
The fixed positive anchor-height charge hypothesis is retained only for
the corollary that excludes the small-charge branch.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The literal quadratic-sharp selector spends at most gap/4 on EACH
physical PDE time variation term, hence at most gap/2 in total. -/
theorem h3Path_quadraticSharpWidth_halfGapBudget244
    (b gap Λ Ξ δ : ℝ)
    (hb : 0 < b) (hg : 0 < gap)
    (hΛ : 0 ≤ Λ) (hΞ : 0 ≤ Ξ)
    (hExact : δ = h3PathCubicAnnulusQuadraticSharpPDEWidth244 b gap Λ Ξ) :
    Λ * δ + Ξ * δ ^ 2 ≤ gap / 2 := by
  obtain ⟨w, hw, hwpos, _hwT, _hwOne, _hwBudget⟩ :=
    h3Path_cubicAnnulusQuadraticSharpPDEWidth_valid244
      b gap Λ Ξ hb hg hΛ hΞ
  have hδ : 0 ≤ δ := by
    rw [hExact, ← hw]
    exact hwpos.le
  have hΛp : 0 < Λ + 1 := by linarith only [hΛ]
  have hΞp : 0 < Ξ + 1 := by linarith only [hΞ]
  have hLinear : δ ≤ gap / (4 * (Λ + 1)) := by
    rw [hExact]
    unfold h3PathCubicAnnulusQuadraticSharpPDEWidth244
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hRoot : δ ≤ Real.sqrt (gap / (4 * (Ξ + 1))) := by
    rw [hExact]
    unfold h3PathCubicAnnulusQuadraticSharpPDEWidth244
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  have hArg : 0 ≤ gap / (4 * (Ξ + 1)) := by positivity
  have hSqrtNonneg : 0 ≤ Real.sqrt (gap / (4 * (Ξ + 1))) :=
    Real.sqrt_nonneg _
  have hSq : δ ^ 2 ≤ (Real.sqrt (gap / (4 * (Ξ + 1)))) ^ 2 :=
    (sq_le_sq₀ hδ hSqrtNonneg).2 hRoot
  have hSq' : δ ^ 2 ≤ gap / (4 * (Ξ + 1)) := by
    rw [Real.sq_sqrt hArg] at hSq
    exact hSq
  have hLinearCost : (Λ + 1) * δ ≤ gap / 4 := by
    calc
      (Λ + 1) * δ ≤ (Λ + 1) * (gap / (4 * (Λ + 1))) :=
        mul_le_mul_of_nonneg_left hLinear hΛp.le
      _ = gap / 4 := by field_simp [ne_of_gt hΛp]
  have hQuadraticCost : (Ξ + 1) * δ ^ 2 ≤ gap / 4 := by
    calc
      (Ξ + 1) * δ ^ 2 ≤ (Ξ + 1) * (gap / (4 * (Ξ + 1))) :=
        mul_le_mul_of_nonneg_left hSq' hΞp.le
      _ = gap / 4 := by field_simp [ne_of_gt hΞp]
  have hLin : Λ * δ ≤ gap / 4 := by
    nlinarith only [hLinearCost, hδ]
  have hQuad : Ξ * δ ^ 2 ≤ gap / 4 := by
    have hs : 0 ≤ δ ^ 2 := sq_nonneg _
    nlinarith only [hQuadraticCost, hs]
  linarith only [hLin, hQuad]

/-- The PDE budget for the entire LOW-Q dissipation is a nonnegative
component of the annulus budget. The other component is the LOW-R rate. -/
theorem h3Path_outerLowPDEBudget_le_annularBudget244
    (R Q K C δ : ℝ)
    (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hδ : 0 ≤ δ) :
    (6 * (Q + 1) * K * h3PathLowRadialPDEGradientRate244 Q C) * δ +
      (3 * (h3PathLowRadialPDEGradientRate244 Q C) ^ 2) * δ ^ 2 ≤
    h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C * δ +
      h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C * δ ^ 2 := by
  have hVR : 0 ≤ h3PathLowRadialPDEGradientRate244 R C :=
    h3Path_lowRadialPDEGradientRate_nonneg244 R C hR hC
  have hOtherLinear : 0 ≤
      6 * (R + 1) * K * h3PathLowRadialPDEGradientRate244 R C := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (by linarith only [hR])) hK)
      hVR
  have hLinearIdentity :
      h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C =
      6 * (Q + 1) * K * h3PathLowRadialPDEGradientRate244 Q C +
      6 * (R + 1) * K * h3PathLowRadialPDEGradientRate244 R C := by
    unfold h3PathFiniteAnnulusPDEVariationCoefficient244
      h3PathLowRadialPDEGradientRate244
    ring
  have hLinearLe :
      6 * (Q + 1) * K * h3PathLowRadialPDEGradientRate244 Q C ≤
        h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C := by
    rw [hLinearIdentity]
    linarith only [hOtherLinear]
  have hOtherQuadratic : 0 ≤
      3 * (h3PathLowRadialPDEGradientRate244 R C) ^ 2 := by positivity
  have hQuadraticIdentity :
      h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C =
      3 * (h3PathLowRadialPDEGradientRate244 Q C) ^ 2 +
      3 * (h3PathLowRadialPDEGradientRate244 R C) ^ 2 := by
    unfold h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
    ring
  have hQuadLe :
      3 * (h3PathLowRadialPDEGradientRate244 Q C) ^ 2 ≤
        h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C := by
    rw [hQuadraticIdentity]
    linarith only [hOtherQuadratic]
  exact add_le_add
    (mul_le_mul_of_nonneg_right hLinearLe hδ)
    (mul_le_mul_of_nonneg_right hQuadLe (sq_nonneg δ))

/-- The original exact canonical first-crossing annulus already makes
the full LOW-Q PDE variation budget strictly smaller than HALF the
actual physical H³ anchor dissipation. No new source or rate cap. -/
theorem h3Path_exactAnchor_outerLowBudget_lt_halfDissipation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
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
      velocityH3DissipationAt u (τ (v k)) / 2 := by
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
  have hAnnLe := h3Path_actualFiniteAnnulusDissipation_le_fullAt244
    hH3 hClass t ht R Q
  have hGapLt : g < velocityH3DissipationAt u t := by
    have hR3 : 0 < R ^ 3 := by dsimp only [R]; positivity
    dsimp only [R, Q, t] at hAnnLe hR3
    dsimp only [g, h3PathCubicAnnulusActualGap244, R, Q, t]
    linarith only [hR3, hAnnLe]
  dsimp only [t] at hGapLt
  linarith only [hBudget, hGapLt]

/-- A quarter-height physical temporal cliff requires an absolute
quarter of the anchor physical H³ dissipation to occupy the actual
HIGH-Q spectral tail, without any extra low-frequency PDE budget cap. -/
theorem h3Path_exactAnchor_quarterCliff_forces_quarterHighTail244
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
    (hs : s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)))
    (hDip : velocityH3DissipationAt u s <
      (1 / 4 : ℝ) * velocityH3DissipationAt u (τ (v k))) :
    (1 / 4 : ℝ) * velocityH3DissipationAt u (τ (v k)) <
      h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
  have hEvac := h3Path_exactAnchorPDE_dip_forces_highTailEvacuation244
    hH3 hClass τ N K C δ v k s (1 / 4 : ℝ)
    ht hK hCexact hExact hδ hEnd hs hDip
  have hBudget := h3Path_exactAnchor_outerLowBudget_lt_halfDissipation244
    hH3 hClass τ N K C δ v k ht hK hC hExact hg
  have hHighNonneg : 0 ≤
      h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s) := by
    unfold h3PathActualHighRadialDissipation244
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg _ ξ
  linarith only [hEvac, hBudget, hHighNonneg]

/-- The SAME exact-anchor, strictly disjoint canonical physical windows
unconditionally satisfy: either an arbitrarily small eventual D(anchor)*δ
charge, or the actual high-Q tail contains > 1/4 of full anchor dissipation.
A fixed nonvanishing charge excludes the first alternative without any
new source action or relative-rate hypothesis. -/
theorem h3Path_noL2Trace_exactAnchor_chargeOrQuarterHighTail244
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
      (∀ k,
        h3PathCubicAnnulusOuterLowLinearRate244 N K C (v k) * δ (v k) +
          h3PathCubicAnnulusOuterLowQuadraticRate244 N C (v k) *
            δ (v k) ^ 2 <
              velocityH3DissipationAt u (τ (v k)) / 2) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop,
        δ (v k) * velocityH3DissipationAt u (τ (v k)) ≤ η ∨
        (1 / 4 : ℝ) * velocityH3DissipationAt u (τ (v k)) <
          h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ η : ℝ, 0 < η →
        (∀ᶠ k : ℕ in atTop,
          η ≤ δ (v k) * velocityH3DissipationAt u (τ (v k))) →
        ∀ᶠ k : ℕ in atTop,
          (1 / 4 : ℝ) * velocityH3DissipationAt u (τ (v k)) <
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
  have hCnonneg (k : ℕ) : 0 ≤ C (v k) := by
    rcases hAll k with ⟨_, _, _, _, _, hp, _, _, _, _, _, _⟩
    obtain ⟨s, _hs, hEq⟩ := hp
    rw [← hEq]
    exact norm_nonneg _
  have hδ (k : ℕ) : 0 < δ (v k) := by
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
  have hHalf (k : ℕ) :
      h3PathCubicAnnulusOuterLowLinearRate244 N K C (v k) * δ (v k) +
        h3PathCubicAnnulusOuterLowQuadraticRate244 N C (v k) *
          δ (v k) ^ 2 < velocityH3DissipationAt u (τ (v k)) / 2 :=
    h3Path_exactAnchor_outerLowBudget_lt_halfDissipation244
      hH3 hClass τ N K C δ v k (hTime (v k))
      (hK k) (hCnonneg k) (hExact k) (hGap k)
  have hMassZero : Tendsto (fun k =>
      ∫ r in τ (v k)..(τ (v k) + δ (v k)),
        velocityH3DissipationAt u r) atTop (𝓝 (0 : ℝ)) := by
    have hSummable := h3Path_disjointNonnegativeWindows_fullIntegral_summable244
      (velocityH3DissipationAt u) a T
      (fun k => τ (v k)) (fun k => δ (v k))
      hClass.terminal_start.2.le
      (fun r => velocityH3DissipationAt_nonneg u r)
      hDInt (fun k => (hTime (v k)).1.le)
      (fun k => (hδ k).le) (fun k => (hEnd k).le)
      (fun k => (hSeparate k (k + 1) (Nat.lt_succ_self k)).le)
    exact hSummable.tendsto_atTop_zero
  have hStart (k : ℕ) : a ≤ τ (v k) := (hTime (v k)).1.le
  have hFirst (η : ℝ) (hη : 0 < η) : ∀ᶠ k : ℕ in atTop,
      δ (v k) * velocityH3DissipationAt u (τ (v k)) ≤ η ∨
      (1 / 4 : ℝ) * velocityH3DissipationAt u (τ (v k)) <
        h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
    have hDips := h3Path_physicalVanishingWindowMass_chargeOrTemporalDip244
      (velocityH3DissipationAt u) a T
      (fun k => τ (v k)) (fun k => δ (v k))
      hClass.terminal_start.2.le hDInt hStart hδ (fun k => (hEnd k).le)
      hMassZero η (1 / 4 : ℝ) hη (by norm_num)
    filter_upwards [hDips] with k hk
    rcases hk with hSmall | ⟨s, hs, hDip⟩
    · exact Or.inl hSmall
    · exact Or.inr (h3Path_exactAnchor_quarterCliff_forces_quarterHighTail244
        hH3 hClass τ N K C δ v k s (hTime (v k))
        (hK k) (hC k) (hCnonneg k) (hExact k) (hδ k)
        (hEnd k) (hGap k) hs hDip)
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
    hSeparate, ?_, hHalf, hFirst, ?_⟩
  · intro k
    exact ⟨hK k, hC k, hδ k⟩
  · intro η hη hPersistent
    have hHalfEta : 0 < η / 2 := by linarith only [hη]
    have hAlt := hFirst (η / 2) hHalfEta
    filter_upwards [hAlt, hPersistent] with k hk hCharge
    rcases hk with hSmall | hHigh
    · exfalso
      linarith only [hSmall, hCharge, hη]
    · exact hHigh

end
end PrimeTensor.FirstMonomialTriad
