import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorTopHigherRadialUniversalEscape244
import Mathlib.Tactic

/-!
# Unconditional inner-cutoff top higher-radial escape on the canonical PDE anchors

The exact canonical construction already gives, at its original anchor, an
annular H³ dissipation excess above 3 R³ / 4 where R = v(k)+1. This is
contained in the genuine high-R FULL dissipation. The existing physical
full-to-top bridge therefore yields a lower bound for the actual q^(4+m)
physical extended moment at the SAME time, for every fixed m.

Unlike the earlier *outer*-cutoff near-total theorem, this inner-cutoff
result does not require the unresolved persistent delta_k * D_k charge.
It does retain the original no-terminal-trace and finite-dissipation
premises and does not establish or rule out Navier–Stokes singularity.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- A nonnegative outer high tail makes the inner high tail dominate the
finite-annulus low-frequency difference. -/
theorem h3Path_scalar_annulus_le_innerHighTail244
    (LR LQ HR HQ D : ℝ)
    (hR : LR + HR = D) (hQ : LQ + HQ = D)
    (hHQ : 0 ≤ HQ) :
    LQ - LR ≤ HR := by
  linarith only [hR, hQ, hHQ]

/-- The original cubic annular gap forces a *physical* high-frequency
H³ dissipation floor at the INNER radius R = v(k)+1. This is not a
statement about the larger canonical outer radius N(vk)+1. -/
theorem h3Path_exactAnchor_innerHighTail_cubicFloor244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (v : ℕ → ℕ) (k : ℕ)
    (ht : τ (v k) ∈ Set.Ioo a T)
    (hGap : ((v k : ℝ) + 1) ^ 3 / 4 <
      h3PathCubicAnnulusActualGap244 hH3 τ N (v k)) :
    3 * (((v k : ℝ) + 1) ^ 3) / 4 <
      h3PathActualHighRadialDissipation244 ((v k : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
  let t : ℝ := τ (v k)
  let R : ℝ := (v k : ℝ) + 1
  let Q : ℝ := (N (v k) : ℝ) + 1
  let G := h3AuditActualSpectralVelocityTotal hH3 t
  have hAnn : 3 * R ^ 3 / 4 <
      h3PathActualLowRadialDissipation244 Q G -
        h3PathActualLowRadialDissipation244 R G := by
    dsimp only [h3PathCubicAnnulusActualGap244] at hGap
    dsimp only [t, R, Q, G]
    linarith only [hGap]
  have hRPart := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ht R
  have hQPart := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ht Q
  have hQNonneg : 0 ≤ h3PathActualHighRadialDissipation244 Q G := by
    unfold h3PathActualHighRadialDissipation244
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg _ ξ
  have hInner := h3Path_scalar_annulus_le_innerHighTail244
    (h3PathActualLowRadialDissipation244 R G)
    (h3PathActualLowRadialDissipation244 Q G)
    (h3PathActualHighRadialDissipation244 R G)
    (h3PathActualHighRadialDissipation244 Q G)
    (velocityH3DissipationAt u t) hRPart hQPart hQNonneg
  dsimp only [R, Q, G, t] at hAnn hInner ⊢
  exact lt_of_lt_of_le hAnn hInner

/-- The *existing physical top-order* extended radial hierarchy pays
at least one quarter of the inner high-tail cubic floor, with the
additional (R²)^m frequency amplification and no moment finiteness. -/
theorem h3Path_exactAnchor_innerCubic_forces_topHigherMoment244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (v : ℕ → ℕ)
    (k m : ℕ) (ht : τ (v k) ∈ Set.Ioo a T)
    (hGap : ((v k : ℝ) + 1) ^ 3 / 4 <
      h3PathCubicAnnulusActualGap244 hH3 τ N (v k)) :
    ENNReal.ofReal
      (((((v k : ℝ) + 1) ^ 2) ^ m) *
        (3 * (((v k : ℝ) + 1) ^ 3) / 16)) ≤
      h3TerminalPhysicalExtendedHigherRadialMomentAt
        hH3 hClass m (τ (v k)) ht := by
  let R : ℝ := (v k : ℝ) + 1
  have hR : 1 ≤ R := by
    dsimp only [R]
    have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hn]
  have hHigh := h3Path_exactAnchor_innerHighTail_cubicFloor244
    hH3 hClass τ N v k ht hGap
  have hQuarter : 3 * R ^ 3 / 16 ≤
      h3PathActualHighRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) / 4 := by
    change 3 * R ^ 3 / 4 <
      h3PathActualHighRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) at hHigh
    linarith only [hHigh]
  have hScaled := mul_le_mul_of_nonneg_left hQuarter
    (pow_nonneg (sq_nonneg R) m)
  have hMoment := h3Path_physicalHighTail_forces_topHigherRadialMoment244
    hH3 hClass (τ (v k)) ht m R hR
  have hLift := (ENNReal.ofReal_le_ofReal hScaled).trans hMoment
  simpa only [R] using hLift

/-- An explicit cubic frequency floor drives every extended top-order
physical moment to infinity, provided the floor applies at every index.
The bound is pointwise, not merely eventual. -/
theorem h3Path_scalar_cubicLower_forces_allTopMomentEscape244
    (R : ℕ → ℝ) (M : ℕ → ℝ≥0∞) (m : ℕ)
    (hR : ∀ k, 1 ≤ R k)
    (hRadius : Tendsto (fun k => (R k) ^ 3) atTop atTop)
    (hMoment : ∀ k,
      ENNReal.ofReal (((R k) ^ 2) ^ m * (3 * (R k) ^ 3 / 16)) ≤ M k) :
    Tendsto M atTop (𝓝 ∞) := by
  have hReal : Tendsto (fun k => 3 * (R k) ^ 3 / 16) atTop atTop := by
    have h := hRadius.const_mul_atTop
      (show (0 : ℝ) < 3 / 16 by norm_num)
    convert h using 1
    funext k
    ring
  have hLift : Tendsto (fun k => ENNReal.ofReal (3 * (R k) ^ 3 / 16))
      atTop (𝓝 ∞) := ENNReal.tendsto_ofReal_atTop.comp hReal
  have hLower : (fun k => ENNReal.ofReal (3 * (R k) ^ 3 / 16)) ≤ M := by
    intro k
    have hSq : 1 ≤ (R k) ^ 2 := by
      have h := pow_le_pow_left₀
        (by norm_num : (0 : ℝ) ≤ 1) (hR k) 2
      simpa only [one_pow] using h
    have hp : 1 ≤ ((R k) ^ 2) ^ m := by
      have h := pow_le_pow_left₀
        (by norm_num : (0 : ℝ) ≤ 1) hSq m
      simpa only [one_pow] using h
    have hCubic : 0 ≤ 3 * (R k) ^ 3 / 16 := by
      have hr : 0 ≤ R k := by linarith only [hR k]
      positivity
    have hScale : 3 * (R k) ^ 3 / 16 ≤
        ((R k) ^ 2) ^ m * (3 * (R k) ^ 3 / 16) := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hp hCubic)
    exact (ENNReal.ofReal_le_ofReal hScale).trans (hMoment k)
  exact tendsto_nhds_top_mono' hLift hLower

/-- SAME canonical exact PDE anchors: the genuine high-frequency H³
mass above the *inner* radius v(k)+1 exceeds a cubic floor, and all
existing physical extended top-order higher radial moments escape
along these anchors WITHOUT a persistent height-width charge premise.
This does not imply outer-radius near-total high-tail concentration. -/
theorem h3Path_noL2Trace_exactAnchor_unconditionalInnerHigherEscape244
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
      (∀ k, K (v k) =
        ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        0 < δ (v k)) ∧
      (∀ k, 3 * (((v k : ℝ) + 1) ^ 3) / 4 <
        h3PathActualHighRadialDissipation244 ((v k : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ m : ℕ, ∀ k : ℕ,
        ENNReal.ofReal (((((v k : ℝ) + 1) ^ 2) ^ m) *
          (3 * (((v k : ℝ) + 1) ^ 3) / 16)) ≤
        h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass m (τ (v k)) (hτ (v k))) ∧
      (∀ m : ℕ,
        Tendsto (fun k => h3TerminalPhysicalExtendedHigherRadialMomentAt
          hH3 hClass m (τ (v k)) (hτ (v k))) atTop (𝓝 ∞)) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, _hSummable, hAll, _hBarrier, _hPeaks⟩ :=
    h3Path_noL2Trace_finiteDissipation_exactAnchorCanonicalThreeScale244
      hH3 hClass hMass hNoTrace hDInt
  have hK (k : ℕ) :
      K (v k) = ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ :=
    (hAll k).1
  have hC (k : ℕ) : C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
      (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) := by
    rcases hAll k with ⟨_, _, _, _, hc, _, _, _, _, _, _, _⟩
    exact hc
  have hWidth (k : ℕ) : 0 < δ (v k) := by
    rcases hAll k with ⟨_, _, _, _, _, _, hp, _, _, _, _, _⟩
    exact hp
  have hGap (k : ℕ) : ((v k : ℝ) + 1) ^ 3 / 4 <
      h3PathCubicAnnulusActualGap244 hH3 τ N (v k) := by
    rcases hAll k with ⟨_, _, _, _, _, _, _, _, _, _, hg, _⟩
    exact hg
  have hHigh (k : ℕ) : 3 * (((v k : ℝ) + 1) ^ 3) / 4 <
      h3PathActualHighRadialDissipation244 ((v k : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) :=
    h3Path_exactAnchor_innerHighTail_cubicFloor244
      hH3 hClass τ N v k (hTime (v k)) (hGap k)
  have hMoment (m k : ℕ) :
      ENNReal.ofReal (((((v k : ℝ) + 1) ^ 2) ^ m) *
        (3 * (((v k : ℝ) + 1) ^ 3) / 16)) ≤
      h3TerminalPhysicalExtendedHigherRadialMomentAt
        hH3 hClass m (τ (v k)) (hTime (v k)) :=
    h3Path_exactAnchor_innerCubic_forces_topHigherMoment244
      hH3 hClass τ N v k m (hTime (v k)) (hGap k)
  have hRadius := h3Path_strictMono_canonicalRadiusCube_escape244 v hv
  refine ⟨τ, N, K, C, δ, v, hTime, hv, hCofinal,
    hSeparate, ?_, hHigh, hMoment, ?_⟩
  · intro k
    exact ⟨hK k, hC k, hWidth k⟩
  · intro m
    exact h3Path_scalar_cubicLower_forces_allTopMomentEscape244
      (fun k => (v k : ℝ) + 1)
      (fun k => h3TerminalPhysicalExtendedHigherRadialMomentAt
        hH3 hClass m (τ (v k)) (hTime (v k)))
      m (fun k => by
        have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
        linarith only [hn]) hRadius (hMoment m)

end
end PrimeTensor.FirstMonomialTriad
