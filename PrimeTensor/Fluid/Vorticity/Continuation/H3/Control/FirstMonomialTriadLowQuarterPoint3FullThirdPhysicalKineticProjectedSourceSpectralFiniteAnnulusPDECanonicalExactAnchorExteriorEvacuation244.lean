import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorTemporalCliff244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEAnchoredPersistence244
import Mathlib.Tactic

/-!
# Exact physical PDE annulus modulus forces exterior dissipation evacuation

The physical temporal-cliff alternative concerns the FULL, untruncated H³
viscous dissipation. The proved source-driven PDE time modulus concerns only
the finite spectral annulus. Their exact difference identifies a necessary
change in the complementary low-frequency and high-frequency dissipations.

At the SAME canonical minimal annuli and exact-source sharp clocks, a dip
D(s) < theta D(t) forces

  exterior(t) - exterior(s) >
    (1-theta) D(t) - (Lambda delta + Xi delta^2).

The exterior is the ACTUAL low-R plus high-Q Fourier dissipation.  The
canonical maximum projected source and actual spectral coefficient are
retained in Lambda and Xi; neither is replaced by a chosen ceiling.  The
conditional premise of nonvanishing anchor-height charges remains explicit.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Complementary physical dissipative channels outside a finite radial
annulus: the low-radius and high-radius contributions, not an artificial
remainder or a signed unverified defect. -/
noncomputable def h3PathFiniteAnnulusPhysicalExterior244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (R Q t : ℝ) : ℝ :=
  h3PathActualLowRadialDissipation244 R
      (h3AuditActualSpectralVelocityTotal hH3 t) +
  h3PathActualHighRadialDissipation244 Q
      (h3AuditActualSpectralVelocityTotal hH3 t)

/-- Exact spectral partition: full viscous H³ dissipation minus finite
annulus dissipation equals the sum of the low and high exterior channels. -/
theorem h3Path_physicalFiniteAnnulus_exteriorPartition244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (t : ℝ) (ht : t ∈ Set.Ioo a T) (R Q : ℝ) :
    velocityH3DissipationAt u t -
      (h3PathActualLowRadialDissipation244 Q
        (h3AuditActualSpectralVelocityTotal hH3 t) -
       h3PathActualLowRadialDissipation244 R
        (h3AuditActualSpectralVelocityTotal hH3 t)) =
      h3PathFiniteAnnulusPhysicalExterior244 hH3 R Q t := by
  have hPartition := h3Path_actualRadialDissipation_partition244
    hH3 hClass t ht Q
  dsimp only [h3PathFiniteAnnulusPhysicalExterior244]
  linarith only [hPartition]

/-- A full dissipation dip that is faster than the finite-annulus change
must be paid by a genuine decrease of the complementary channels. -/
theorem h3Path_scalar_cliff_forces_exteriorLoss244
    (D₀ D₁ B₀ B₁ err θ : ℝ)
    (hDip : D₁ < θ * D₀)
    (hVariation : |B₀ - B₁| ≤ err) :
    (1 - θ) * D₀ - err <
      (D₀ - B₀) - (D₁ - B₁) := by
  have hOne : B₀ - B₁ ≤ err :=
    (le_abs_self (B₀ - B₁)).trans hVariation
  linarith only [hDip, hOne]

/-- Physical PDE refinement: an actual full-H³ dissipation dip inside a
source-controlled window forces an exterior low/high dissipation decrease,
up to the EXACT quadratic anchored finite-annulus PDE variation budget. -/
theorem h3Path_physicalPDE_cliff_forces_exteriorEvacuation244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (R Q K C t δ s θ : ℝ)
    (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hδ : 0 < δ) (ht : t ∈ Set.Ioo a T) (hEnd : t + δ < T)
    (hs : s ∈ Set.Icc t (t + δ))
    (hBase : ∀ j : Fin 3,
      ‖(h3AuditActualSpectralVelocityTotal hH3 t) j‖ ≤ K)
    (hSource : ∀ r : ℝ, r ∈ Set.Icc t (t + δ) →
      ‖h3PathActualProjectedMomentumSource244 hH3 r‖ ≤ C)
    (hDip : velocityH3DissipationAt u s <
      θ * velocityH3DissipationAt u t) :
    (1 - θ) * velocityH3DissipationAt u t -
      (h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C * δ +
       h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C * δ ^ 2) <
      h3PathFiniteAnnulusPhysicalExterior244 hH3 R Q t -
        h3PathFiniteAnnulusPhysicalExterior244 hH3 R Q s := by
  let B : ℝ → ℝ := fun r =>
    h3PathActualLowRadialDissipation244 Q
      (h3AuditActualSpectralVelocityTotal hH3 r) -
    h3PathActualLowRadialDissipation244 R
      (h3AuditActualSpectralVelocityTotal hH3 r)
  let Λ := h3PathFiniteAnnulusPDEVariationCoefficient244 R Q K C
  let Ξ := h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244 R Q C
  have hC : 0 ≤ C := by
    have htMem : t ∈ Set.Icc t (t + δ) :=
      ⟨le_rfl, le_add_of_nonneg_right hδ.le⟩
    exact (norm_nonneg _).trans (hSource t htMem)
  have hΛ : 0 ≤ Λ :=
    h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244 R Q K C hK hC
  have hΞ : 0 ≤ Ξ :=
    h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244 R Q C
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
  have hVariation : |B t - B s| ≤ Λ * (s - t) + Ξ * (s - t) ^ 2 := by
    exact h3Path_actualFiniteAnnulusVariation_anchoredPDE244
      hH3 R Q K hR hQ hK t s C htAbs hsAbs hs.1 hBase
      (fun r hr => hSource r ⟨hr.1, le_trans hr.2 hs.2⟩)
  have hMaxVariation : |B t - B s| ≤ Λ * δ + Ξ * δ ^ 2 := by
    calc
      _ ≤ Λ * (s - t) + Ξ * (s - t) ^ 2 := hVariation
      _ ≤ Λ * δ + Ξ * δ ^ 2 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hElapsedLe hΛ)
          (mul_le_mul_of_nonneg_left hElapsedSq hΞ)
  have hCliff := h3Path_scalar_cliff_forces_exteriorLoss244
    (velocityH3DissipationAt u t) (velocityH3DissipationAt u s)
    (B t) (B s) (Λ * δ + Ξ * δ ^ 2) θ hDip hMaxVariation
  have hExteriorT := h3Path_physicalFiniteAnnulus_exteriorPartition244
    hH3 hClass t ht R Q
  have hExteriorS := h3Path_physicalFiniteAnnulus_exteriorPartition244
    hH3 hClass s hsClass R Q
  dsimp only [B, Λ, Ξ] at hCliff
  rw [hExteriorT, hExteriorS] at hCliff
  exact hCliff

/-- The exact canonical clock keeps its attained source envelope and
literal spectral anchor when the exterior evacuation bound is applied at
any point inside the original disjoint persistence window. -/
theorem h3Path_exactAnchorPDE_dip_forces_exteriorEvacuation244
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
      (h3PathCubicAnnulusActualLinearRate244 N K C (v k) * δ (v k) +
       h3PathCubicAnnulusActualQuadraticRate244 N C (v k) * δ (v k) ^ 2) <
      h3PathFiniteAnnulusPhysicalExterior244 hH3
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (τ (v k)) -
      h3PathFiniteAnnulusPhysicalExterior244 hH3
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) s := by
  let t : ℝ := τ (v k)
  let b : ℝ := (T - t) / 2
  let R : ℝ := (v k : ℝ) + 1
  let Q : ℝ := (N (v k) : ℝ) + 1
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hK0 : 0 ≤ K (v k) := by
    rw [hK]
    exact norm_nonneg _
  have hBase : ∀ j : Fin 3,
      ‖(h3AuditActualSpectralVelocityTotal hH3 t) j‖ ≤ K (v k) := by
    intro j
    rw [hK]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).1 le_rfl j
  have hb : 0 < b := by dsimp only [b, t]; linarith only [ht.2]
  have htb : t < t + b := by linarith only [hb]
  have hbT : t + b < T := by
    dsimp only [b, t]
    linarith only [ht.2]
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
  have hBound := h3Path_physicalPDE_cliff_forces_exteriorEvacuation244
    hH3 hClass R Q (K (v k)) (C (v k)) t (δ (v k)) s θ
    hR hQ hK0 hδ ht hEnd hs hBase hSource hDip
  simpa only [R, Q, t,
    h3PathCubicAnnulusActualLinearRate244,
    h3PathCubicAnnulusActualQuadraticRate244] using hBound

/-- The canonical temporal-cliff witness is never reselected. With an
explicit eventually nonvanishing anchor-height charge, each sufficiently
late original disjoint window contains a true full-H³ dissipation dip;
the physical PDE forces that dip to be paid by LOW+HIGH exterior spectral
dissipation, up to its exact sharp linear-plus-quadratic annular budget. -/
theorem h3Path_noL2Trace_exactAnchor_persistentCharge_exteriorEvacuation244
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
        ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ᶠ k : ℕ in atTop,
          ∃ s : ℝ, s ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k)) ∧
            velocityH3DissipationAt u s <
              θ * velocityH3DissipationAt u (τ (v k)) ∧
            (1 - θ) * velocityH3DissipationAt u (τ (v k)) -
              (h3PathCubicAnnulusActualLinearRate244 N K C (v k) * δ (v k) +
               h3PathCubicAnnulusActualQuadraticRate244 N C (v k) *
                 δ (v k) ^ 2) <
              h3PathFiniteAnnulusPhysicalExterior244 hH3
                ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (τ (v k)) -
              h3PathFiniteAnnulusPhysicalExterior244 hH3
                ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) s) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, _hSummable, hAll, _hBarrier, _hPeaks⟩ :=
    h3Path_noL2Trace_finiteDissipation_exactAnchorCanonicalThreeScale244
      hH3 hClass hMass hNoTrace hDInt
  have hWidth (k : ℕ) : 0 < δ (v k) := by
    rcases hAll k with ⟨_, _, _, _, _, _, hp, _, _, _, _, _⟩
    exact hp
  have hEnd (k : ℕ) : τ (v k) + δ (v k) < T := by
    rcases hAll k with ⟨_, _, _, _, _, _, _, he, _, _, _, _⟩
    exact he
  have hMassSummable : Summable (fun k =>
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
  have hMassZero := hMassSummable.tendsto_atTop_zero
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
    hSeparate, ?_, ?_⟩
  · intro k
    rcases hAll k with ⟨hK, _, _, _, hC, _, hδ, hT, hExact, _, _, _⟩
    exact ⟨hK, hC, hExact, hδ, hT⟩
  · intro η hη hPersist θ hθ _hθOne
    have hDip := h3Path_physicalPersistentAnchorCharge_forces_temporalCliff244
      (velocityH3DissipationAt u) a T
      (fun k => τ (v k)) (fun k => δ (v k))
      hClass.terminal_start.2.le hDInt
      (fun k => (hTime (v k)).1.le)
      hWidth (fun k => (hEnd k).le) hMassZero
      η hη hPersist θ hθ
    filter_upwards [hDip] with k hk
    obtain ⟨s, hs, hDipRate⟩ := hk
    rcases hAll k with ⟨hK, _, _, _, hC, _, hδ, hT, hExact, _, _, _⟩
    have hEvac := h3Path_exactAnchorPDE_dip_forces_exteriorEvacuation244
      hH3 hClass τ N K C δ v k s θ (hTime (v k))
      hK hC hExact hδ hT hs hDipRate
    exact ⟨s, hs, hDipRate, hEvac⟩

end
end PrimeTensor.FirstMonomialTriad
