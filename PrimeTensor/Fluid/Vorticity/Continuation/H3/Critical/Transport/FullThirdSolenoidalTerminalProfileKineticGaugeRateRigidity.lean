import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticGlobalBudgetChargeCollapse
import Mathlib.Tactic

/-!
# Asymptotic kinetic PDE-rate rigidity under noncompressed terminal clocks

The preceding physical kinetic construction supplies an arbitrary-gauge
frequency-escape diagonal and disjoint annular clocks. Finite extended H3
viscous dissipation makes the actual height-times-width charges tend to zero.

The remaining alternative can be sharpened to a quantified necessary
condition. On any such diagonal, if the height-weighted time remaining is
eventually bounded away from zero, the kinetic-only PDE rate must dominate
EVERY fixed multiple of the height squared. In particular, no globally
bounded normalized frequency-rate coefficient is compatible with that
noncompression premise. This is a conditional necessity, not a conclusion
that the requisite noncompression holds.

The physical theorem combines this quantitative rigidity with the SAME
arbitrary prescribed-gauge outer-frequency escape and the SAME global
extended viscous charge bound. It never replaces the selected times,
frequencies or explicit physical PDE widths.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- The exact kinetic width gives an exact normalized height-width charge.
This identity is valid independently of temporal integrability and is not
merely a one-sided PDE persistence estimate. -/
theorem thirdFull_scalar_exactKineticWidth_charge_minIdentity244
    (T x M Λ δ : ℝ) (hM : 0 ≤ M) (hΛ : 0 ≤ Λ)
    (hWidth : δ = min ((T - x) / 4)
      ((M / 4) / (2 * (Λ + 1)))) :
    δ * (M / 4) = min (((T - x) * M) / 16)
      (M ^ 2 / (32 * (Λ + 1))) := by
  have hM4 : 0 ≤ M / 4 := by linarith only [hM]
  have hDen : 0 < Λ + 1 := by linarith only [hΛ]
  have hTime : ((T - x) / 4) * (M / 4) =
      ((T - x) * M) / 16 := by ring
  have hRate : ((M / 4) / (2 * (Λ + 1))) * (M / 4) =
      M ^ 2 / (32 * (Λ + 1)) := by
    field_simp [ne_of_gt hDen]
    <;> ring
  rcases le_total ((T - x) / 4)
      ((M / 4) / (2 * (Λ + 1))) with hLeft | hRight
  · have hMult := mul_le_mul_of_nonneg_right hLeft hM4
    have hCmp : ((T - x) * M) / 16 ≤
        M ^ 2 / (32 * (Λ + 1)) := by
      calc
        ((T - x) * M) / 16 = ((T - x) / 4) * (M / 4) := hTime.symm
        _ ≤ ((M / 4) / (2 * (Λ + 1))) * (M / 4) := hMult
        _ = M ^ 2 / (32 * (Λ + 1)) := hRate
    rw [hWidth, min_eq_left hLeft, hTime, min_eq_left hCmp]
  · have hMult := mul_le_mul_of_nonneg_right hRight hM4
    have hCmp : M ^ 2 / (32 * (Λ + 1)) ≤
        ((T - x) * M) / 16 := by
      calc
        M ^ 2 / (32 * (Λ + 1)) =
            ((M / 4) / (2 * (Λ + 1))) * (M / 4) := hRate.symm
        _ ≤ ((T - x) / 4) * (M / 4) := hMult
        _ = ((T - x) * M) / 16 := hTime
    rw [hWidth, min_eq_right hRight, hRate, min_eq_right hCmp]

/-- If exact positive kinetic charges vanish but the height-weighted
remaining terminal clock does NOT compress, the physical kinetic-only PDE
rate outgrows every fixed multiple of the squared height. Neither a cutoff
upper bound nor any Fourier monotonicity is assumed. -/
theorem thirdFull_scalar_noncompressedKineticCharge_superquadraticRate244
    (T : ℝ) (x M Λ δ : ℕ → ℝ)
    (hM : ∀ k, 0 < M k) (hΛ : ∀ k, 0 ≤ Λ k)
    (hWidth : ∀ k, δ k = min ((T - x k) / 4)
      ((M k / 4) / (2 * (Λ k + 1))))
    (hZero : Tendsto (fun k => δ k * (M k / 4))
      atTop (𝓝 (0 : ℝ)))
    (η : ℝ) (hη : 0 < η)
    (hNoncompressed : ∀ᶠ k : ℕ in atTop,
      η ≤ (T - x k) * M k) :
    ∀ K : ℝ, 0 ≤ K → ∀ᶠ k : ℕ in atTop,
      K * (M k) ^ 2 ≤ Λ k + 1 := by
  intro K hK
  have hK1 : 0 < K + 1 := by linarith only [hK]
  let ε : ℝ := min (η / 32) (1 / (32 * (K + 1)))
  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min (by linarith only [hη]) (by positivity)
  have hεTime : ε ≤ η / 32 := by
    dsimp only [ε]
    exact min_le_left _ _
  have hTimeStrict : 16 * ε < η := by
    linarith only [hεTime, hη]
  have hPositiveDen : 0 < 32 * (K + 1) := by positivity
  have hεRate : ε * (32 * (K + 1)) ≤ 1 := by
    calc
      ε * (32 * (K + 1)) ≤
          (1 / (32 * (K + 1))) * (32 * (K + 1)) :=
        mul_le_mul_of_nonneg_right
          (show ε ≤ 1 / (32 * (K + 1)) from min_le_right _ _)
          hPositiveDen.le
      _ = 1 := by field_simp [ne_of_gt hPositiveDen]
  have hNear : ∀ᶠ k : ℕ in atTop,
      δ k * (M k / 4) < ε :=
    hZero.eventually (eventually_lt_nhds hε)
  filter_upwards [hNoncompressed, hNear] with k hClock hk
  have hFork := thirdFull_scalar_exactKineticWidth_smallCharge_fork244
    T (x k) (M k) (Λ k) (δ k) ε
    (hM k).le (hΛ k) (hWidth k) hk.le
  rcases hFork with hShort | hRate
  · have hImpossible : η ≤ 16 * ε := le_trans hClock hShort
    exact False.elim ((not_le_of_gt hTimeStrict) hImpossible)
  · have hScale : 0 ≤ Λ k + 1 := by linarith only [hΛ k]
    have hUpper : (K + 1) * (M k) ^ 2 ≤ Λ k + 1 := by
      calc
        (K + 1) * (M k) ^ 2 ≤
            (K + 1) * (32 * (Λ k + 1) * ε) :=
          mul_le_mul_of_nonneg_left hRate hK1.le
        _ = (Λ k + 1) * (ε * (32 * (K + 1))) := by ring
        _ ≤ (Λ k + 1) * 1 :=
          mul_le_mul_of_nonneg_left hεRate hScale
        _ = Λ k + 1 := by ring
    nlinarith only [hUpper, sq_nonneg (M k)]

/-- SAME arbitrary-gauge outer-frequency witnesses as the earlier physical
kinetic construction. Under an independently finite GLOBAL extended H3
budget their real viscous height-width charges are summable and vanish.
Whenever the selected height-weighted terminal clock is eventually at least
some eta>0, the verified physical kinetic PDE rate dominates K*height^2
for EVERY fixed K>=0, eventually on those SAME windows.

The noncompression hypothesis is explicit and conditional: it is not
derived from the Navier--Stokes path assumptions. -/
theorem thirdFullPhysical_noH3Trace_gaugeFiniteBudget_rateRigidity244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (G : ℕ → ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hGlobal :
      (∫⁻ r in Set.Ioo a T,
        ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) ≤
          ENNReal.ofReal C) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ)
        (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ, k ≤ v k ∧ G (v k) < N (v k)) ∧
      (∀ k : ℕ,
        ThirdFullKineticNaturalAnnularLocalWitness244
          hH3 b (τ (v k)) (v k) (N (v k))
          (thirdFullPhysicalKineticGaugeHeight244
            (velocityH3Energy0At u b) G (v k)) (δ (v k))) ∧
      Summable (fun k => δ (v k) *
        (thirdFullPhysicalKineticGaugeHeight244
          (velocityH3Energy0At u b) G (v k) / 4)) ∧
      Tendsto (fun k => δ (v k) *
        (thirdFullPhysicalKineticGaugeHeight244
          (velocityH3Energy0At u b) G (v k) / 4))
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ η : ℝ, 0 < η →
        (∀ᶠ k : ℕ in atTop,
          η ≤ (T - τ (v k)) *
            thirdFullPhysicalKineticGaugeHeight244
              (velocityH3Energy0At u b) G (v k)) →
        ∀ K : ℝ, 0 ≤ K → ∀ᶠ k : ℕ in atTop,
          K * (thirdFullPhysicalKineticGaugeHeight244
              (velocityH3Energy0At u b) G (v k)) ^ 2 ≤
            thirdFullPhysicalKineticLowBandDissipationRate244
              (N (v k)) (velocityH3Energy0At u b) +
            thirdFullPhysicalKineticLowBandDissipationRate244
              (v k) (velocityH3Energy0At u b) + 1) := by
  let E : ℝ := velocityH3Energy0At u b
  let M : ℕ → ℝ := thirdFullPhysicalKineticGaugeHeight244 E G
  have hE : 0 ≤ E := velocityH3Energy0At_nonneg u b
  have hM (n : ℕ) : 0 < M n :=
    thirdFullPhysicalKineticGaugeHeight_pos244 E hE G n
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
      hIndexGauge, hWindows, hCosts⟩ :=
    thirdFullPhysical_noH3Trace_kineticArbitraryGaugeEscapeGlobalCharges244
      hH3 hClass b hb hNoTrace G
  let w : ℕ → ℝ := fun k => δ (v k)
  let H : ℕ → ℝ := fun k => M (v k) / 4
  have hw (k : ℕ) : 0 ≤ w k := by
    rcases hWindows k with ⟨_, hp, _, _, _, _⟩
    exact hp.le
  have hH (k : ℕ) : 0 ≤ H k := by
    dsimp only [H]
    linarith only [hM (v k)]
  have hFinite (m : ℕ) :
      (∑ k ∈ Finset.range m,
        ENNReal.ofReal (H k) * ENNReal.ofReal (w k)) ≤
        ENNReal.ofReal C :=
    (hCosts m).trans hGlobal
  obtain ⟨hSummable, hZero⟩ :=
    thirdFull_scalar_finiteExtendedBudget_forces_realChargeSummable244
      w H C hw hH hC hFinite
  refine ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hIndexGauge, hWindows, hSummable, hZero, ?_⟩
  intro η hη hNoncompressed
  let x : ℕ → ℝ := fun k => τ (v k)
  let A : ℕ → ℝ := fun k => M (v k)
  let Λ : ℕ → ℝ := fun k =>
    thirdFullPhysicalKineticLowBandDissipationRate244
      (N (v k)) (velocityH3Energy0At u b) +
    thirdFullPhysicalKineticLowBandDissipationRate244
      (v k) (velocityH3Energy0At u b)
  have hA (k : ℕ) : 0 < A k := hM (v k)
  have hΛ (k : ℕ) : 0 ≤ Λ k := add_nonneg
    (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 (N (v k)) _)
    (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 (v k) _)
  have hWidth (k : ℕ) :
      w k = min ((T - x k) / 4)
        ((A k / 4) / (2 * (Λ k + 1))) := by
    rcases hWindows k with ⟨_, _, hEq, _, _, _⟩
    simpa only [w, x, A, Λ] using hEq
  have hZero' : Tendsto (fun k => w k * (A k / 4))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [H, A] using hZero
  have hClock : ∀ᶠ k : ℕ in atTop,
      η ≤ (T - x k) * A k := by
    simpa only [x, A, M, E] using hNoncompressed
  have hRate := thirdFull_scalar_noncompressedKineticCharge_superquadraticRate244
    T x A Λ w hA hΛ hWidth hZero' η hη hClock
  intro K hK
  simpa only [Λ, A, M, E] using hRate K hK

end
end PrimeTensor.FirstMonomialTriad
