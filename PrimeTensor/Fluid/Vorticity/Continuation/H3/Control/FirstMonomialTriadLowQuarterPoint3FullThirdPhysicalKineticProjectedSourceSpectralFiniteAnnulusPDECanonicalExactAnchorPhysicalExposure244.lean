import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECanonicalExactAnchorPhysicalRate244
import Mathlib.Tactic

/-!
# Actual full-H³ dissipation exposure on the canonical disjoint PDE clocks

The previous exact-anchor theorem established unbounded physical H³
viscous dissipation at its canonical anchor times and summability of the
cubic persistence charges. Here we sum the *full physical dissipation
integrals themselves* over exactly the same disjoint windows. These
integrals tend to zero even though D₃ at the left endpoint diverges.

The quotient of each integrated physical dissipation by its actual
left-endpoint height therefore tends to zero. It is an intrinsic
mean-height exposure time, NOT a statement that full dissipation is
uniformly comparable to its anchor value inside the selected window.
The theorem does not use a critical annular-width cap or derive a
regularity contradiction.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Entire physical integral masses on disjoint positive-time windows
are summable whenever the nonnegative density has finite enclosing
integral. This is stronger than the already proved summability of a
particular pointwise height floor times the selected widths. -/
theorem h3Path_disjointNonnegativeWindows_fullIntegral_summable244
    (f : ℝ → ℝ) (a T : ℝ) (τ δ : ℕ → ℝ)
    (haT : a ≤ T)
    (hf : ∀ r : ℝ, 0 ≤ f r)
    (hInt : IntervalIntegrable f volume a T)
    (hStart : ∀ k : ℕ, a ≤ τ k)
    (hWidth : ∀ k : ℕ, 0 ≤ δ k)
    (hEnd : ∀ k : ℕ, τ k + δ k ≤ T)
    (hSeparate : ∀ k : ℕ, τ k + δ k ≤ τ (k + 1)) :
    Summable (fun k : ℕ =>
      ∫ r in τ k..(τ k + δ k), f r) := by
  have hTermNonneg (k : ℕ) :
      0 ≤ ∫ r in τ k..(τ k + δ k), f r :=
    intervalIntegral.integral_nonneg
      (le_add_of_nonneg_right (hWidth k)) (fun r _ => hf r)
  have hBound := h3Path_disjointNonnegativeWindows_finiteIntegralSum_le244
    f a T τ δ haT hf hInt hStart hWidth hEnd hSeparate
  exact h3Path_nonnegativeBoundedRangeSums_summable244
    (fun k => ∫ r in τ k..(τ k + δ k), f r)
    (∫ r in a..T, f r) hTermNonneg hBound

/-- A summable nonnegative integral mass, divided by a diverging
positive left-endpoint height, has vanishing normalized exposure time. -/
theorem h3Path_scalar_summableMass_divergingHeight_exposureCollapse244
    (I H : ℕ → ℝ)
    (hMass : Summable I)
    (hNonneg : ∀ k, 0 ≤ I k)
    (hHeight : Tendsto H atTop atTop) :
    Tendsto (fun k => I k / H k) atTop (𝓝 (0 : ℝ)) := by
  have hTall : ∀ᶠ k : ℕ in atTop, 1 ≤ H k :=
    hHeight.eventually (eventually_ge_atTop 1)
  have hMassZero : Tendsto I atTop (𝓝 (0 : ℝ)) :=
    hMass.tendsto_atTop_zero
  apply squeeze_zero'
  · filter_upwards [hTall] with k hk
    exact div_nonneg (hNonneg k) (by linarith only [hk])
  · filter_upwards [hTall] with k hk
    have hkPos : 0 < H k := lt_of_lt_of_le (by norm_num) hk
    apply (div_le_iff₀ hkPos).2
    calc
      I k = I k * 1 := by ring
      _ ≤ I k * H k := mul_le_mul_of_nonneg_left hk (hNonneg k)
  · exact hMassZero

/-- A fixed positive fraction of an anchor peak cannot persist with
nonvanishing height-times-width when the full window integrals are
summable. The relative-peak persistence lower bound is explicitly a
separate hypothesis, not inferred from instantaneous dissipation. -/
theorem h3Path_scalar_relativePeakCharge_forces_heightWidthCollapse244
    (I height width : ℕ → ℝ) (θ : ℝ)
    (hθ : 0 < θ)
    (hI : Summable I)
    (hNonneg : ∀ᶠ k : ℕ in atTop, 0 ≤ height k * width k)
    (hExposure : ∀ᶠ k : ℕ in atTop,
      θ * (height k * width k) ≤ I k) :
    Tendsto (fun k => height k * width k) atTop (𝓝 (0 : ℝ)) := by
  have hIzero : Tendsto I atTop (𝓝 (0 : ℝ)) := hI.tendsto_atTop_zero
  have hScaledZero : Tendsto (fun k => θ⁻¹ * I k)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hIzero.const_mul θ⁻¹
  apply squeeze_zero' hNonneg _ hScaledZero
  filter_upwards [hExposure] with k hk
  have hScaled := mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr hθ.le)
  have hCancel : θ⁻¹ * (θ * (height k * width k)) =
      height k * width k := by
    field_simp [ne_of_gt hθ]
  calc
    height k * width k = θ⁻¹ * (θ * (height k * width k)) := hCancel.symm
    _ ≤ θ⁻¹ * I k := hScaled

/-- On one and the same EXACT-anchor canonical sequence, the *entire*
physical full-H³ dissipation integrals over the disjoint persistence
windows are summable and converge to zero, while the left-endpoint
full-H³ dissipation diverges. Their ratio is a vanishing intrinsic
physical exposure clock. The full-window integral retains the previously
proved cubic lower charge. No critical-width assumption is made. -/
theorem h3Path_noL2Trace_exactAnchor_actualPhysicalExposureCollapse244
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
      (∀ k, 3 * (((v k : ℝ) + 1) ^ 3) / 4 <
        velocityH3DissipationAt u (τ (v k))) ∧
      Tendsto (fun k => velocityH3DissipationAt u (τ (v k))) atTop atTop ∧
      Summable (fun k =>
        ∫ r in τ (v k)..(τ (v k) + δ (v k)),
          velocityH3DissipationAt u r) ∧
      Tendsto (fun k =>
        ∫ r in τ (v k)..(τ (v k) + δ (v k)),
          velocityH3DissipationAt u r) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun k =>
        (∫ r in τ (v k)..(τ (v k) + δ (v k)),
          velocityH3DissipationAt u r) /
          velocityH3DissipationAt u (τ (v k))) atTop (𝓝 (0 : ℝ)) ∧
      (∀ k, δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) ≤
        ∫ r in τ (v k)..(τ (v k) + δ (v k)),
          velocityH3DissipationAt u r) := by
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
  have hAnnulusFloor (k : ℕ) (r : ℝ)
      (hr : r ∈ Set.Icc (τ (v k)) (τ (v k) + δ (v k))) :
      (((v k : ℝ) + 1) ^ 3 / 2) ≤
        velocityH3DissipationAt u r := by
    rcases hAll k with ⟨_, _, _, _, _, _, _, _, _, hp, _, _⟩
    have hrClass : r ∈ Set.Ioo a T :=
      ⟨lt_of_lt_of_le (hTime (v k)).1 hr.1,
        lt_of_le_of_lt hr.2 (hEnd k)⟩
    exact (hp r hr).le.trans
      (h3Path_actualFiniteAnnulusDissipation_le_fullAt244
        hH3 hClass r hrClass ((v k : ℝ) + 1)
          ((N (v k) : ℝ) + 1))
  have hGap (k : ℕ) : ((v k : ℝ) + 1) ^ 3 / 4 <
      h3PathCubicAnnulusActualGap244 hH3 τ N (v k) := by
    rcases hAll k with ⟨_, _, _, _, _, _, _, _, _, _, hg, _⟩
    exact hg
  have hFloor (k : ℕ) :
      3 * (((v k : ℝ) + 1) ^ 3) / 4 <
        velocityH3DissipationAt u (τ (v k)) := by
    have hCross : 3 * (((v k : ℝ) + 1) ^ 3) / 4 <
        h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) -
        h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))) := by
      have hg := hGap k
      dsimp only [h3PathCubicAnnulusActualGap244] at hg
      linarith only [hg]
    exact lt_of_lt_of_le hCross
      (h3Path_actualFiniteAnnulusDissipation_le_fullAt244
        hH3 hClass (τ (v k)) (hTime (v k))
        ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1))
  have hDiverge : Tendsto
      (fun k => velocityH3DissipationAt u (τ (v k))) atTop atTop :=
    h3Path_scalar_cubicFloor_forces_dissipationEscape244
      (fun k => (v k : ℝ) + 1)
      (fun k => velocityH3DissipationAt u (τ (v k)))
      (h3Path_strictMono_canonicalRadiusCube_escape244 v hv) hFloor
  let f : ℕ → ℝ := fun k =>
    ∫ r in τ (v k)..(τ (v k) + δ (v k)),
      velocityH3DissipationAt u r
  have hIntegralNonneg (k : ℕ) : 0 ≤ f k := by
    dsimp only [f]
    exact intervalIntegral.integral_nonneg
      (le_add_of_nonneg_right (hWidth k).le)
      (fun r _ => velocityH3DissipationAt_nonneg u r)
  have hIntegralSummable : Summable f := by
    exact h3Path_disjointNonnegativeWindows_fullIntegral_summable244
      (velocityH3DissipationAt u) a T
      (fun k => τ (v k)) (fun k => δ (v k))
      hClass.terminal_start.2.le
      (fun r => velocityH3DissipationAt_nonneg u r)
      hDInt (fun k => (hTime (v k)).1.le)
      (fun k => (hWidth k).le) (fun k => (hEnd k).le)
      (fun k => (hSeparate k (k + 1) (Nat.lt_succ_self k)).le)
  have hIntegralZero : Tendsto f atTop (𝓝 (0 : ℝ)) :=
    hIntegralSummable.tendsto_atTop_zero
  have hExposureZero : Tendsto (fun k =>
      f k / velocityH3DissipationAt u (τ (v k))) atTop (𝓝 (0 : ℝ)) :=
    h3Path_scalar_summableMass_divergingHeight_exposureCollapse244
      f (fun k => velocityH3DissipationAt u (τ (v k)))
      hIntegralSummable hIntegralNonneg hDiverge
  have hIndividualCost (k : ℕ) :
      δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) ≤ f k := by
    have hSubInt : IntervalIntegrable (velocityH3DissipationAt u)
        volume (τ (v k)) (τ (v k) + δ (v k)) := by
      apply hDInt.mono_set
      rw [Set.uIcc_of_le (le_add_of_nonneg_right (hWidth k).le),
          Set.uIcc_of_le hClass.terminal_start.2.le]
      exact Set.Icc_subset_Icc (hTime (v k)).1.le (hEnd k).le
    have hCompare :
        (∫ _r in τ (v k)..(τ (v k) + δ (v k)),
           (((v k : ℝ) + 1) ^ 3 / 2)) ≤ f k := by
      dsimp only [f]
      exact intervalIntegral.integral_mono_on
        (le_add_of_nonneg_right (hWidth k).le)
        intervalIntegrable_const hSubInt (hAnnulusFloor k)
    have hConst :
        (∫ _r in τ (v k)..(τ (v k) + δ (v k)),
          (((v k : ℝ) + 1) ^ 3 / 2)) =
          δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2) := by
      simp <;> ring
    exact hConst ▸ hCompare
  refine ⟨τ, N, K, C, δ, v, hv, hCofinal, hTime,
    hSeparate, ?_, hFloor, hDiverge, ?_, ?_, ?_, ?_⟩
  · intro k
    rcases hAll k with ⟨hK, _, _, _, hC, _, _, _, _, _, _, _⟩
    exact ⟨hK, hC, hWidth k⟩
  · simpa only [f] using hIntegralSummable
  · simpa only [f] using hIntegralZero
  · simpa only [f] using hExposureZero
  · intro k
    simpa only [f] using hIndividualCost k

end
end PrimeTensor.FirstMonomialTriad
