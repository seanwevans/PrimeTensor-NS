import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorExteriorEvacuation244
import Mathlib.Tactic

/-!
# Physical PDE control isolates high-frequency tail loss at exact canonical cliffs

The existing exterior-evacuation theorem controlled the sum of low-R and
high-Q dissipation. The source-driven PDE modulus controls the whole LOW-Q
channel separately, hence the exact radial partition D = L_Q + H_Q
localizes any physical full-dissipation cliff to genuine high-Q evacuation,
up to one explicit anchored quadratic PDE budget at the canonical Q.

There is no automatic relative smallness of this budget, and the positive
anchor-height charge remains an explicit conditional hypothesis.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The one-cutoff low-Q linear PDE coefficient at a canonical outer radius. -/
noncomputable def h3PathCubicAnnulusOuterLowLinearRate244
    (N : ℕ → ℕ) (K C : ℕ → ℝ) (n : ℕ) : ℝ :=
  6 * (((N n : ℝ) + 1) + 1) * K n *
    h3PathLowRadialPDEGradientRate244 ((N n : ℝ) + 1) (C n)

/-- The one-cutoff low-Q quadratic PDE coefficient at the same radius. -/
noncomputable def h3PathCubicAnnulusOuterLowQuadraticRate244
    (N : ℕ → ℕ) (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  3 * (h3PathLowRadialPDEGradientRate244
    ((N n : ℝ) + 1) (C n)) ^ 2

/-- Exact physical partition at a single outer cutoff, with no signed
surrogate: the remainder is the genuine high-frequency H³ dissipation. -/
theorem h3Path_physicalHighTail_outerPartition244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (Q : ℝ) :
    velocityH3DissipationAt u t -
      h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t) =
      h3PathActualHighRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t) := by
  have hPart := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ht Q
  linarith only [hPart]

/-- A full-dissipation physical cliff, with a projected-PDE ceiling,
forces high-Q tail dissipation to fall: the low-Q channel is separately
controlled by its own anchored linear-plus-quadratic variation modulus. -/
theorem h3Path_physicalPDE_cliff_forces_highTailEvacuation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (Q K C t δ s θ : ℝ)
    (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hδ : 0 < δ) (ht : t ∈ Set.Ioo a T) (hEnd : t + δ < T)
    (hs : s ∈ Set.Icc t (t + δ))
    (hBase : ∀ j : Fin 3,
      ‖(h3AuditActualSpectralVelocityTotal hH3 t) j‖ ≤ K)
    (hSource : ∀ r : ℝ, r ∈ Set.Icc t (t + δ) →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hDip : velocityH3DissipationAt u s <
      θ * velocityH3DissipationAt u t) :
    (1 - θ) * velocityH3DissipationAt u t -
      ((6 * (Q + 1) * K * h3PathLowRadialPDEGradientRate244 Q C) * δ +
        (3 * (h3PathLowRadialPDEGradientRate244 Q C) ^ 2) * δ ^ 2) <
      h3PathActualHighRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t) -
      h3PathActualHighRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 s) := by
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
  have hLoss := h3Path_scalar_cliff_forces_exteriorLoss244
    (velocityH3DissipationAt u t) (velocityH3DissipationAt u s)
    (L t) (L s) (Λ * δ + Ξ * δ ^ 2) θ hDip hMax
  have htPartition : velocityH3DissipationAt u t - L t = H t := by
    simpa only [L, H] using
      (h3Path_physicalHighTail_outerPartition244 hH3 hClass t ht Q)
  have hsPartition : velocityH3DissipationAt u s - L s = H s := by
    simpa only [L, H] using
      (h3Path_physicalHighTail_outerPartition244 hH3 hClass s hsClass Q)
  change (1 - θ) * velocityH3DissipationAt u t -
    (Λ * δ + Ξ * δ ^ 2) < H t - H s
  calc
    _ < (velocityH3DissipationAt u t - L t) -
      (velocityH3DissipationAt u s - L s) := hLoss
    _ = H t - H s := by rw [htPartition, hsPartition]

/-- The exact original source envelope, spectral norm, and sharp clock
carry the one-cutoff low-Q modulus to the original canonical outer radius. -/
theorem h3Path_exactAnchorPDE_dip_forces_highTailEvacuation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
    (v : ℕ → ℕ) (k : ℕ) (s θ : ℝ)
    (ht : τ (v k) ∈ Set.Ioo a T)
    (hK : K (v k) =
      ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖)
    (hC : C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
      (τ (v k)) (τ (v k) + (T - τ (v k)) / 2))
    (hExact : δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
      ((T - τ (v k)) / 2)
      (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
      (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
      (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)))
    (hδ : 0 < δ (v k))
    (hEnd : τ (v k) + δ (v k) < T)
    (hs : s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)))
    (hDip : velocityH3DissipationAt u s <
      θ * velocityH3DissipationAt u (τ (v k))) :
    (1 - θ) * velocityH3DissipationAt u (τ (v k)) -
      (h3PathCubicAnnulusOuterLowLinearRate244 N K C (v k) * δ (v k) +
       h3PathCubicAnnulusOuterLowQuadraticRate244 N C (v k) *
         δ (v k) ^ 2) <
      h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
      h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s) := by
  let t : ℝ := τ (v k)
  let b : ℝ := (T - t) / 2
  let Q : ℝ := (N (v k) : ℝ) + 1
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hK0 : 0 ≤ K (v k) := by rw [hK]; exact norm_nonneg _
  have hBase : ∀ j : Fin 3,
      ‖(h3AuditActualSpectralVelocityTotal hH3 t) j‖ ≤ K (v k) := by
    intro j
    rw [hK]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).1 le_rfl j
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
      hH3 (lt_trans hClass.terminal_start.1 ht.1) htb hbT r hrHalf
    simpa only [hC, t, b] using hBound
  have hBound := h3Path_physicalPDE_cliff_forces_highTailEvacuation244
    hH3 hClass Q (K (v k)) (C (v k)) t (δ (v k)) s θ
    hQ hK0 hδ ht hEnd hs hBase hSource hDip
  simpa only [Q, t, h3PathCubicAnnulusOuterLowLinearRate244,
    h3PathCubicAnnulusOuterLowQuadraticRate244] using hBound

/-- If a relative outer low-Q PDE budget is smaller than the fractional
full-dissipation cliff, the high-Q physical tail has a quantitatively
large positive mass at the original anchor. This is conditional. -/
theorem h3Path_scalar_lowBudget_highTail_anchorLower244
    (D H₀ H₁ err θ α : ℝ)
    (hH₁ : 0 ≤ H₁)
    (hBudget : err ≤ α * D)
    (hEvac : (1 - θ) * D - err < H₀ - H₁) :
    (1 - θ - α) * D < H₀ := by
  linarith only [hH₁, hBudget, hEvac]

/-- On the SAME cofinal exact-anchor canonical disjoint windows, a physical
cliff plus the established low-Q PDE modulus forces genuine HIGH-Q tail
loss. An additionally controlled relative low-Q budget converts this into
an absolute positive anchor high-Q dissipation lower bound. Both results
retain the explicit, conditional nonvanishing anchor-height premise. -/
theorem h3Path_noL2Trace_exactAnchor_persistentCharge_highTailEvacuation244
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
        δ (v k) = h3PathCubicAnnulusQuadraticSharpPDEWidth244
          ((T - τ (v k)) / 2)
          (h3PathCubicAnnulusActualGap244 hH3 τ N (v k))
          (h3PathCubicAnnulusActualLinearRate244 N K C (v k))
          (h3PathCubicAnnulusActualQuadraticRate244 N C (v k)) ∧
        0 < δ (v k) ∧ τ (v k) + δ (v k) < T) ∧
      (∀ η : ℝ, 0 < η →
        (∀ᶠ k : ℕ in atTop,
          η ≤ δ (v k) * velocityH3DissipationAt u (τ (v k))) →
        ∀ θ : ℝ, 0 < θ → θ < 1 →
        (∀ᶠ k : ℕ in atTop,
          ∃ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) ∧
            velocityH3DissipationAt u s <
              θ * velocityH3DissipationAt u (τ (v k)) ∧
            (1 - θ) * velocityH3DissipationAt u (τ (v k)) -
              (h3PathCubicAnnulusOuterLowLinearRate244 N K C (v k) * δ (v k) +
               h3PathCubicAnnulusOuterLowQuadraticRate244 N C (v k) * δ (v k) ^ 2) <
              h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
              h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 s)) ∧
        (∀ α : ℝ,
          (∀ᶠ k : ℕ in atTop,
            h3PathCubicAnnulusOuterLowLinearRate244 N K C (v k) * δ (v k) +
              h3PathCubicAnnulusOuterLowQuadraticRate244 N C (v k) * δ (v k) ^ 2 ≤
              α * velocityH3DissipationAt u (τ (v k))) →
          ∀ᶠ k : ℕ in atTop,
            (1 - θ - α) * velocityH3DissipationAt u (τ (v k)) <
              h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
                (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, hAll, hConditional⟩ :=
    h3Path_noL2Trace_exactAnchor_persistentCharge_exteriorEvacuation244
      hH3 hClass hMass hNoTrace hDInt
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime, hSeparate, hAll, ?_⟩
  intro η hη hPersist θ hθ hθOne
  have hCliffs := hConditional η hη hPersist θ hθ hθOne
  have hHigh : ∀ᶠ k : ℕ in atTop,
      ∃ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) ∧
        velocityH3DissipationAt u s <
          θ * velocityH3DissipationAt u (τ (v k)) ∧
        (1 - θ) * velocityH3DissipationAt u (τ (v k)) -
          (h3PathCubicAnnulusOuterLowLinearRate244 N K C (v k) * δ (v k) +
           h3PathCubicAnnulusOuterLowQuadraticRate244 N C (v k) * δ (v k) ^ 2) <
          h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
          h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
            (h3AuditActualSpectralVelocityTotal hH3 s) := by
    filter_upwards [hCliffs] with k hk
    obtain ⟨s, hs, hDip, _hExterior⟩ := hk
    rcases hAll k with ⟨hK, hC, hExact, hδ, hEnd⟩
    have hLoss := h3Path_exactAnchorPDE_dip_forces_highTailEvacuation244
      hH3 hClass τ N K C δ v k s θ (hTime (v k))
      hK hC hExact hδ hEnd hs hDip
    exact ⟨s, hs, hDip, hLoss⟩
  constructor
  · exact hHigh
  · intro α hBudget
    filter_upwards [hHigh, hBudget] with k hk hRate
    obtain ⟨s, _hs, _hDip, hEvac⟩ := hk
    have hHighNonneg : 0 ≤
        h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 s) := by
      unfold h3PathActualHighRadialDissipation244
      apply integral_nonneg
      intro ξ
      exact h3TerminalSpectralDissipationSingleDensity_nonneg _ ξ
    exact h3Path_scalar_lowBudget_highTail_anchorLower244
      (velocityH3DissipationAt u (τ (v k)))
      (h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))
      (h3PathActualHighRadialDissipation244 ((N (v k) : ℝ) + 1)
        (h3AuditActualSpectralVelocityTotal hH3 s))
      (h3PathCubicAnnulusOuterLowLinearRate244 N K C (v k) * δ (v k) +
       h3PathCubicAnnulusOuterLowQuadraticRate244 N C (v k) * δ (v k) ^ 2)
      θ α hHighNonneg hRate hEvac

end
end PrimeTensor.FirstMonomialTriad
