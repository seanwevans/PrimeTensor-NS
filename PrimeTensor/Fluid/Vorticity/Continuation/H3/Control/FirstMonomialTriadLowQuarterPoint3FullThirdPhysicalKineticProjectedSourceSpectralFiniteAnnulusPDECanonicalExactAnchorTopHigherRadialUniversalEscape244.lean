import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorTopHigherRadialBridge244
import Mathlib.Tactic

/-!
# Universal higher radial moment escape on the original canonical anchors

This is a conditional rate theorem, not a theorem that the anchor-height
charge remains positive. On the EXISTING strict, cofinal, disjoint physical
windows, delta_k -> 0 without using an invented clock estimate. If
eta <= delta_k D3(anchor_k) eventually, then D3(anchor_k) -> +infinity.
Moreover eta <= (T-anchor_k) D3(anchor_k) eventually.

The previously proved exact physical full-to-top q^(4+m) bridge implies that
for EVERY fixed m, the genuine extended top-order higher radial moment
M_(4+m)(anchor_k) tends to +infinity on the SAME sequence, even when m=0.
No new cutoff/velocity/source bound and no higher moment integrability input.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology ENNReal

noncomputable section
set_option maxHeartbeats 1800000

/-- Cofinal physical endpoints and positive windows that stay before the
terminal time force their window widths to vanish. -/
theorem h3Path_scalar_cofinalTerminalWindow_width_vanish244
    (T : ℝ) (t δ : ℕ → ℝ)
    (ht : Tendsto t atTop (𝓝 T))
    (hδ : ∀ k, 0 ≤ δ k)
    (hEnd : ∀ k, t k + δ k ≤ T) :
    Tendsto δ atTop (𝓝 (0 : ℝ)) := by
  have hUpper (k : ℕ) : δ k ≤ T - t k := by
    have h := hEnd k
    linarith only [h]
  have hDiff : Tendsto (fun k => T - t k) atTop (𝓝 (0 : ℝ)) := by
    have hConst : Tendsto (fun _ : ℕ => T) atTop (𝓝 T) :=
      tendsto_const_nhds
    have hSub := hConst.sub ht
    simpa only [sub_self] using hSub
  exact squeeze_zero'
    (Filter.Eventually.of_forall hδ)
    (Filter.Eventually.of_forall hUpper) hDiff

/-- Positive height-width charge on shrinking windows forces unbounded
physical dissipation heights; the widths must be strictly positive. -/
theorem h3Path_scalar_shrinkingWindow_persistentCharge_heightEscape244
    (D δ : ℕ → ℝ)
    (hδ : ∀ k, 0 < δ k)
    (hδZero : Tendsto δ atTop (𝓝 (0 : ℝ)))
    (η : ℝ) (hη : 0 < η)
    (hCharge : ∀ᶠ k : ℕ in atTop, η ≤ δ k * D k) :
    Tendsto D atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  let B : ℝ := max M 0 + 1
  have hB : 0 < B := by
    dsimp only [B]
    have hMax : 0 ≤ max M 0 := le_max_right _ _
    linarith only [hMax]
  have hMB : M ≤ B := by
    dsimp only [B]
    have hMax : M ≤ max M 0 := le_max_left _ _
    linarith only [hMax]
  have hSmall : ∀ᶠ k : ℕ in atTop, δ k < η / B :=
    hδZero.eventually (eventually_lt_nhds (div_pos hη hB))
  filter_upwards [hCharge, hSmall] with k hk hδSmall
  have hLower : B ≤ D k := by
    by_contra hNot
    have hDLt : D k < B := lt_of_not_ge hNot
    have hScale : δ k * D k < δ k * B :=
      mul_lt_mul_of_pos_left hDLt (hδ k)
    have hWidth : δ k * B < η := (lt_div_iff₀ hB).mp hδSmall
    linarith only [hk, hScale, hWidth]
  exact hMB.trans hLower

/-- Natural canonical outer cutoffs produce noncontracting powers at every
additional radial moment order. -/
theorem h3Path_scalar_canonicalOuterPower_ge_one244
    (N : ℕ → ℕ) (k m : ℕ) :
    (1 : ℝ) ≤ ((((N k : ℝ) + 1) ^ 2) ^ m) := by
  have hNat : (0 : ℝ) ≤ (N k : ℝ) := Nat.cast_nonneg _
  have hOne : (1 : ℝ) ≤ (N k : ℝ) + 1 := by
    linarith only [hNat]
  have hSquare : (1 : ℝ) ≤ ((N k : ℝ) + 1) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hOne 2
    simpa only [one_pow] using h
  have hPower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hSquare m
  simpa only [one_pow] using hPower

/-- Polynomially weighted physical top-order moment bounds force actual
extended moment escape if the original physical H³ heights diverge.
No moment is required to have a finite real integral. -/
theorem h3Path_scalar_topHigherMoment_escape_of_heightEscape244
    (D p : ℕ → ℝ) (M : ℕ → ℝ≥0∞)
    (hD : Tendsto D atTop atTop)
    (hp : ∀ k, 1 ≤ p k)
    (hMoment : ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (p k * ((1 / 2 : ℝ) * D k / 4)) ≤ M k) :
    Tendsto M atTop (𝓝 ∞) := by
  have hScaled : Tendsto (fun k => D k / 8) atTop atTop := by
    have h := hD.const_mul_atTop (show (0 : ℝ) < 1 / 8 by norm_num)
    convert h using 1
    funext k
    ring
  have hOfReal : Tendsto (fun k => ENNReal.ofReal (D k / 8))
      atTop (𝓝 ∞) := ENNReal.tendsto_ofReal_atTop.comp hScaled
  have hDnonneg : ∀ᶠ k : ℕ in atTop, 0 ≤ D k :=
    hD.eventually (eventually_ge_atTop (0 : ℝ))
  have hLower : ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (D k / 8) ≤ M k := by
    filter_upwards [hMoment, hDnonneg] with k hk hDk
    have hFactor : 0 ≤ D k / 8 := div_nonneg hDk (by norm_num)
    have hScaledLe : D k / 8 ≤ p k * ((1 / 2 : ℝ) * D k / 4) := by
      have hCmp : (1 : ℝ) * (D k / 8) ≤ p k * (D k / 8) :=
        mul_le_mul_of_nonneg_right (hp k) hFactor
      convert hCmp using 1 <;> ring
    exact (ENNReal.ofReal_le_ofReal hScaledLe).trans hk
  let L : ℕ → ℝ≥0∞ := fun k =>
    min (ENNReal.ofReal (D k / 8)) (M k)
  have hEq : (fun k => ENNReal.ofReal (D k / 8)) =ᶠ[atTop] L := by
    filter_upwards [hLower] with k hk
    exact (min_eq_left hk).symm
  have hLT : Tendsto L atTop (𝓝 ∞) := hOfReal.congr' hEq
  have hLE : L ≤ M := by
    intro k
    exact min_le_right _ _
  exact tendsto_nhds_top_mono' hLT hLE

/-- Under the EXISTING, explicitly conditional noncollapsed canonical anchor
charge, the actual physical H³ heights and ALL the established extended
top-order q^(4+m) higher radial moments diverge on ONE unreselected cofinal
sequence. Moreover the heights obey the terminal-time rate obstruction
eta <= (T-t_k) D3(t_k). No extra PDE or high-frequency hypothesis. -/
theorem h3Path_noL2Trace_exactAnchor_persistentCharge_universalTopHigherEscape244
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
      (∀ η : ℝ, 0 < η →
        (∀ᶠ k : ℕ in atTop,
          η ≤ δ (v k) * velocityH3DissipationAt u (τ (v k))) →
        Tendsto (fun k => velocityH3DissipationAt u (τ (v k)))
          atTop atTop ∧
        (∀ᶠ k : ℕ in atTop,
          η ≤ (T - τ (v k)) * velocityH3DissipationAt u (τ (v k))) ∧
        (∀ m : ℕ,
          Tendsto
            (fun k => h3TerminalPhysicalExtendedHigherRadialMomentAt
              hH3 hClass m (τ (v k)) (hτ (v k)))
            atTop (𝓝 ∞))) := by
  obtain ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal, hSeparate,
      hCanonical, _hAlt, hPersistent⟩ :=
    h3Path_noL2Trace_exactAnchor_chargeOrTopHigherRadialMoment244
      hH3 hClass hMass hNoTrace hDInt
  have hWidth (k : ℕ) : 0 < δ (v k) := (hCanonical k).2.2
  have hEnd (k : ℕ) : τ (v k) + δ (v k) ≤ T := by
    have hNext := hSeparate k (k + 1) (Nat.lt_succ_self k)
    exact (le_of_lt (lt_trans hNext (hτ (v (k + 1))).2))
  have hWidthZero : Tendsto (fun k => δ (v k)) atTop (𝓝 (0 : ℝ)) :=
    h3Path_scalar_cofinalTerminalWindow_width_vanish244
      T (fun k => τ (v k)) (fun k => δ (v k))
      hCofinal (fun k => (hWidth k).le) hEnd
  refine ⟨τ, N, K, C, δ, v, hτ, hv, hCofinal,
    hSeparate, hCanonical, ?_⟩
  intro η hη hCharge
  let D : ℕ → ℝ := fun k => velocityH3DissipationAt u (τ (v k))
  have hEscape : Tendsto D atTop atTop :=
    h3Path_scalar_shrinkingWindow_persistentCharge_heightEscape244
      D (fun k => δ (v k)) hWidth hWidthZero η hη hCharge
  have hDnonneg : ∀ᶠ k : ℕ in atTop, 0 ≤ D k :=
    hEscape.eventually (eventually_ge_atTop (0 : ℝ))
  have hTerminalRate : ∀ᶠ k : ℕ in atTop,
      η ≤ (T - τ (v k)) * velocityH3DissipationAt u (τ (v k)) := by
    filter_upwards [hCharge, hDnonneg] with k hk hDk
    have hDiff : δ (v k) ≤ T - τ (v k) := by
      have h := hEnd k
      linarith only [h]
    have hMul := mul_le_mul_of_nonneg_right hDiff hDk
    exact hk.trans hMul
  refine ⟨hEscape, hTerminalRate, ?_⟩
  intro m
  let p : ℕ → ℝ := fun k => ((((N (v k) : ℝ) + 1) ^ 2) ^ m)
  let M : ℕ → ℝ≥0∞ := fun k =>
    h3TerminalPhysicalExtendedHigherRadialMomentAt
      hH3 hClass m (τ (v k)) (hτ (v k))
  have hp : ∀ k, 1 ≤ p k := by
    intro k
    exact h3Path_scalar_canonicalOuterPower_ge_one244 N (v k) m
  have hMoment : ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (p k * ((1 / 2 : ℝ) * D k / 4)) ≤ M k := by
    simpa only [p, D, M] using
      (hPersistent η hη hCharge m (1 / 2 : ℝ) (by norm_num))
  exact h3Path_scalar_topHigherMoment_escape_of_heightEscape244
    D p M hEscape hp hMoment

end
end PrimeTensor.FirstMonomialTriad
