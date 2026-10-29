import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorPhysicalExposure244
import Mathlib.Tactic

/-!
# Exact-anchor full physical dissipation: divergent means and supercubic alternative

The ACTUAL full-H³ dissipative mass I_k on each canonical disjoint window
is summable and tends to zero, whereas its anchor D_k exceeds 3 R_k³/4.
The canonical persistent annulus gives I_k >= δ_k R_k³ / 2. Therefore
its mean I_k/δ_k diverges while δ_k R_k³ -> 0.

The resulting *unconditional-on-width* necessary dichotomy is:
for each M >= 0 and ε > 0, eventually either δ_k D_k <= ε, or
M R_k³ < D_k. Thus if δ_k D_k is bounded BELOW by a fixed positive
amount, the actual anchor excess ratio D_k/R_k³ tends to infinity.

No uniform continuity of full H³ dissipation is introduced. No critical
ninth/eighth annulus cap or smooth terminal extension is concluded.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- The canonical cubic floor forces the ACTUAL time-mean dissipation to
escape, even though the full integral mass of each window tends to zero. -/
theorem h3Path_scalar_cubicCharge_forces_divergingWindowMean244
    (R I δ : ℕ → ℝ)
    (hδ : ∀ k, 0 < δ k)
    (hRadial : Tendsto (fun k => (R k) ^ 3) atTop atTop)
    (hCharge : ∀ k, δ k * ((R k) ^ 3 / 2) ≤ I k) :
    Tendsto (fun k => I k / δ k) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  let B : ℝ := max M 0 + 1
  have hMB : M ≤ B := by
    dsimp only [B]
    have hMax : M ≤ max M 0 := le_max_left _ _
    linarith only [hMax]
  have hLarge : ∀ᶠ k : ℕ in atTop, 2 * B ≤ (R k) ^ 3 :=
    hRadial.eventually (eventually_ge_atTop (2 * B))
  filter_upwards [hLarge] with k hk
  have hHalf : B ≤ (R k) ^ 3 / 2 := by
    linarith only [hk]
  have hBound : M * δ k ≤ I k := by
    calc
      M * δ k ≤ B * δ k :=
        mul_le_mul_of_nonneg_right hMB (hδ k).le
      _ = δ k * B := by ring
      _ ≤ δ k * ((R k) ^ 3 / 2) :=
        mul_le_mul_of_nonneg_left hHalf (hδ k).le
      _ ≤ I k := hCharge k
  exact (le_div_iff₀ (hδ k)).2 hBound

/-- Summable actual physical mass, together with the exact cubic annular
charge, forces the R³-normalized physical persistence width to vanish. -/
theorem h3Path_scalar_cubicCharge_forces_scaledWidthCollapse244
    (R I δ : ℕ → ℝ)
    (hR : ∀ k, 0 ≤ R k)
    (hδ : ∀ k, 0 ≤ δ k)
    (hMassZero : Tendsto I atTop (𝓝 (0 : ℝ)))
    (hCharge : ∀ k, δ k * ((R k) ^ 3 / 2) ≤ I k) :
    Tendsto (fun k => δ k * (R k) ^ 3) atTop (𝓝 (0 : ℝ)) := by
  have hUpperZero : Tendsto (fun k => 2 * I k)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hMassZero.const_mul (2 : ℝ)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun k =>
      mul_nonneg (hδ k) (pow_nonneg (hR k) 3))
  · apply Filter.Eventually.of_forall
    intro k
    calc
      δ k * (R k) ^ 3 = 2 * (δ k * ((R k) ^ 3 / 2)) := by ring
      _ ≤ 2 * I k :=
        mul_le_mul_of_nonneg_left (hCharge k) (by norm_num)
  · exact hUpperZero

/-- Vanishing cubic-weighted width forces an eventual physical alternative:
either the ACTUAL peak-height charge δD is small, or the anchor D exceeds
any prescribed multiple of the cubic minimal-annulus frequency. -/
theorem h3Path_scalar_smallCubicClock_or_supercubicHeight244
    (R D δ : ℕ → ℝ)
    (hR : ∀ k, 0 ≤ R k)
    (hδ : ∀ k, 0 ≤ δ k)
    (hCollapse : Tendsto (fun k => δ k * (R k) ^ 3)
      atTop (𝓝 (0 : ℝ)))
    (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      δ k * D k ≤ ε ∨ M * (R k) ^ 3 < D k := by
  have hB : 0 < M + 1 := by linarith only [hM]
  have hSmall : ∀ᶠ k : ℕ in atTop,
      δ k * (R k) ^ 3 < ε / (M + 1) :=
    hCollapse.eventually (eventually_lt_nhds (div_pos hε hB))
  filter_upwards [hSmall] with k hk
  by_cases hExcess : M * (R k) ^ 3 < D k
  · exact Or.inr hExcess
  · have hD : D k ≤ M * (R k) ^ 3 := le_of_not_gt hExcess
    have hBound : δ k * D k ≤ δ k * (M * (R k) ^ 3) :=
      mul_le_mul_of_nonneg_left hD (hδ k)
    have hNonneg : 0 ≤ δ k * (R k) ^ 3 :=
      mul_nonneg (hδ k) (pow_nonneg (hR k) 3)
    have hCompare : δ k * (M * (R k) ^ 3) ≤
        (M + 1) * (δ k * (R k) ^ 3) := by
      calc
        _ = M * (δ k * (R k) ^ 3) := by ring
        _ ≤ (M + 1) * (δ k * (R k) ^ 3) :=
          mul_le_mul_of_nonneg_right (by linarith : M ≤ M + 1) hNonneg
    have hSmall' : (M + 1) * (δ k * (R k) ^ 3) < ε := by
      calc
        (M + 1) * (δ k * (R k) ^ 3) =
            (δ k * (R k) ^ 3) * (M + 1) := by ring
        _ < ε := (lt_div_iff₀ hB).mp hk
    exact Or.inl ((hBound.trans hCompare).trans hSmall'.le)

/-- If an anchor keeps a fixed positive δD charge despite a vanishing
cubic-width cost, its actual physical dissipation must grow faster than
EVERY fixed cubic multiple. This is a conditional shape constraint. -/
theorem h3Path_scalar_noncollapsedPeakCharge_forces_supercubicRatio244
    (R D δ : ℕ → ℝ)
    (hR : ∀ k, 0 < R k)
    (hδ : ∀ k, 0 ≤ δ k)
    (hCollapse : Tendsto (fun k => δ k * (R k) ^ 3)
      atTop (𝓝 (0 : ℝ)))
    (η : ℝ) (hη : 0 < η)
    (hPersistentCharge : ∀ᶠ k : ℕ in atTop, η ≤ δ k * D k) :
    Tendsto (fun k => D k / (R k) ^ 3) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  let B : ℝ := max M 0
  have hB : 0 ≤ B := le_max_right _ _
  have hMB : M ≤ B := le_max_left _ _
  have hHalf : 0 < η / 2 := by linarith only [hη]
  have hAlt := h3Path_scalar_smallCubicClock_or_supercubicHeight244
    R D δ (fun k => (hR k).le) hδ hCollapse B (η / 2) hB hHalf
  filter_upwards [hAlt, hPersistentCharge] with k hk hCharge
  rcases hk with hSmall | hLarge
  · exfalso
    linarith only [hSmall, hCharge, hη]
  · have hrp : 0 < (R k) ^ 3 := pow_pos (hR k) 3
    have hLower : M * (R k) ^ 3 ≤ B * (R k) ^ 3 :=
      mul_le_mul_of_nonneg_right hMB hrp.le
    exact (le_div_iff₀ hrp).2 (hLower.trans hLarge.le)

/-- At the very same exact-anchor disjoint physical PDE windows, actual
full-H³ integral masses tend to zero BUT their time-averaged dissipation
rates diverge. The sharp unconditional asymptotic alternative is a
vanishing physical peak-height charge OR supercubic instantaneous height.
If a fixed positive physical peak-height charge persists, the normalized
anchor H³ dissipation D_k/R_k³ must escape to +infinity. -/
theorem h3Path_noL2Trace_exactAnchor_physicalExposureIntermittency244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (_N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, K (v k) =
          ‖h3AuditActualSpectralVelocityTotal hH3 (τ (v k))‖ ∧
        C (v k) = h3PathActualProjectedSourceWindowEnvelope244 hH3
          (τ (v k)) (τ (v k) + (T - τ (v k)) / 2) ∧
        0 < δ (v k)) ∧
      (∀ k, 3 * (((v k : ℝ) + 1) ^ 3) / 4 <
        velocityH3DissipationAt u (τ (v k))) ∧
      Summable (fun k =>
        ∫ r in τ (v k)..(τ (v k) + δ (v k)),
          velocityH3DissipationAt u r) ∧
      Tendsto (fun k =>
        ∫ r in τ (v k)..(τ (v k) + δ (v k)),
          velocityH3DissipationAt u r) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun k =>
        (∫ r in τ (v k)..(τ (v k) + δ (v k)),
          velocityH3DissipationAt u r) / δ (v k)) atTop atTop ∧
      Tendsto (fun k => δ (v k) * ((v k : ℝ) + 1) ^ 3)
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ M ε : ℝ, 0 ≤ M → 0 < ε → ∀ᶠ k : ℕ in atTop,
        δ (v k) * velocityH3DissipationAt u (τ (v k)) ≤ ε ∨
          M * ((v k : ℝ) + 1) ^ 3 <
            velocityH3DissipationAt u (τ (v k))) ∧
      (∀ η : ℝ, 0 < η →
        (∀ᶠ k : ℕ in atTop,
          η ≤ δ (v k) * velocityH3DissipationAt u (τ (v k))) →
        Tendsto (fun k =>
          velocityH3DissipationAt u (τ (v k)) /
            (((v k : ℝ) + 1) ^ 3)) atTop atTop) := by
  obtain ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
      hSeparate, hCanonical, hFloor, _hDivergent,
      hIntegralSummable, hIntegralZero, _hExposureZero, hCharge⟩ :=
    h3Path_noL2Trace_exactAnchor_actualPhysicalExposureCollapse244
      hH3 hClass hMass hNoTrace hDInt
  let R : ℕ → ℝ := fun k => (v k : ℝ) + 1
  let I : ℕ → ℝ := fun k =>
    ∫ r in τ (v k)..(τ (v k) + δ (v k)),
      velocityH3DissipationAt u r
  let w : ℕ → ℝ := fun k => δ (v k)
  let H : ℕ → ℝ := fun k => velocityH3DissipationAt u (τ (v k))
  have hR (k : ℕ) : 0 < R k := by
    dsimp only [R]
    have hk : 0 ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hk]
  have hw (k : ℕ) : 0 < w k := (hCanonical k).2.2
  have hRadius : Tendsto (fun k => (R k) ^ 3) atTop atTop := by
    simpa only [R] using h3Path_strictMono_canonicalRadiusCube_escape244 v hv
  have hCharge' (k : ℕ) : w k * ((R k) ^ 3 / 2) ≤ I k := by
    simpa only [w, R, I] using hCharge k
  have hMean := h3Path_scalar_cubicCharge_forces_divergingWindowMean244
    R I w hw hRadius hCharge'
  have hWidthZero := h3Path_scalar_cubicCharge_forces_scaledWidthCollapse244
    R I w (fun k => (hR k).le) (fun k => (hw k).le)
    (by simpa only [I] using hIntegralZero) hCharge'
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
    hSeparate, hCanonical, hFloor, hIntegralSummable,
    hIntegralZero, ?_, ?_, ?_, ?_⟩
  · simpa only [I, w] using hMean
  · simpa only [R, w] using hWidthZero
  · intro M ε hM hε
    have hAlt := h3Path_scalar_smallCubicClock_or_supercubicHeight244
      R H w (fun k => (hR k).le) (fun k => (hw k).le)
      hWidthZero M ε hM hε
    simpa only [R, H, w] using hAlt
  · intro η hη hPersistent
    have hEvent : ∀ᶠ k : ℕ in atTop, η ≤ w k * H k := by
      simpa only [w, H] using hPersistent
    have hSuper := h3Path_scalar_noncollapsedPeakCharge_forces_supercubicRatio244
      R H w hR (fun k => (hw k).le) hWidthZero η hη hEvent
    simpa only [R, H] using hSuper

end
end PrimeTensor.FirstMonomialTriad
