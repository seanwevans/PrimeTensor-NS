import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileAnchoredPDESummability
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Actual terminal H³ radial escape: endpoint-clock or physical PDE-rate barrier

Finite total H³ dissipation forces the positive disjoint annular height-width
charges to vanish. The exact anchored PDE width is a minimum of three scales:
the remaining terminal clock, one unit, and the annular gap over the sum of
the genuine projected-source-dependent linear and quadratic rates.

When M grows, the unit-width option is ruled out. Because the initial finite
annulus was deliberately chosen above M/2 while the persistence floor is M/4,
the gap is > M/4. The remaining PDE-rate option therefore forces

  M^2 < 8*(Lambda + Xi + 1).

This is a necessary endpoint rate-or-clock alternative, not a contradiction:
very rapid terminal time compression or large physical source coefficients
remain possible under the current PDE hypotheses.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval

noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable local instance axisFintypeProfileRateBarrier244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A large prescribed annular height and a small EXACT physical PDE clock
force either terminal-clock compression or quadratic growth of the rate
coefficient. The crucial strict gap B-M/4 > M/4 is retained explicitly. -/
theorem thirdFull_exactPDEClock_smallCharge_forces_clockOrQuadraticRate244
    (t T M B Λ Ξ δ : ℝ)
    (hM : 1 ≤ M) (hHeight : M / 2 < B)
    (hΛ : 0 ≤ Λ) (hΞ : 0 ≤ Ξ)
    (hClock : δ = min ((T - t) / 4) (min (1 : ℝ)
      ((B - M / 4) / (2 * (Λ + Ξ + 1)))))
    (hCharge : δ * M < 1) :
    (T - t) * M < 4 ∨ M ^ 2 < 8 * (Λ + Ξ + 1) := by
  let Z : ℝ := Λ + Ξ + 1
  let gap : ℝ := B - M / 4
  have hZ : 0 < Z := by
    dsimp only [Z]
    linarith only [hΛ, hΞ]
  have hGap : M / 4 < gap := by
    dsimp only [gap]
    linarith only [hHeight]
  have hMpos : 0 < M := by linarith only [hM]
  have hExact : δ = min ((T - t) / 4)
      (min (1 : ℝ) (gap / (2 * Z))) := by
    simpa only [gap, Z] using hClock
  rcases le_total ((T - t) / 4)
      (min (1 : ℝ) (gap / (2 * Z))) with hLeft | hRight
  · left
    have hδClock : δ = (T - t) / 4 := by
      rw [hExact]
      exact min_eq_left hLeft
    have hSmall : ((T - t) / 4) * M < 1 := by
      simpa only [hδClock] using hCharge
    nlinarith only [hSmall]
  · have hδInner : δ = min (1 : ℝ) (gap / (2 * Z)) := by
      rw [hExact]
      exact min_eq_right hRight
    rcases le_total (1 : ℝ) (gap / (2 * Z)) with hOne | hRate
    · have hδOne : δ = 1 := hδInner.trans (min_eq_left hOne)
      have hSmall : M < 1 := by
        simpa only [hδOne, one_mul] using hCharge
      exact False.elim ((not_lt_of_ge hM) hSmall)
    · right
      have hδGap : δ = gap / (2 * Z) :=
        hδInner.trans (min_eq_right hRate)
      have hDiv : (gap * M) / (2 * Z) < 1 := by
        calc
          (gap * M) / (2 * Z) = (gap / (2 * Z)) * M := by ring
          _ = δ * M := by rw [hδGap]
          _ < 1 := hCharge
      have hRateBound : gap * M < 2 * Z := by
        have h2Z : 0 < 2 * Z := by positivity
        have h := (div_lt_iff₀ h2Z).mp hDiv
        linarith only [h]
      have hSquare : M ^ 2 / 4 < gap * M := by
        have hScaled := mul_lt_mul_of_pos_right hGap hMpos
        nlinarith only [hScaled]
      have hCombined := hSquare.trans hRateBound
      nlinarith only [hCombined]

/-- Main physical PDE-rate barrier for terminal H³ escape. Under finite full
viscous dissipation, every prescribed positive height profile tending to
infinity has ONE disjoint sequence of ACTUAL anchored Navier--Stokes windows
whose finite viscous charges are summable. On all sufficiently late selected
indices either the remaining terminal time is O(1/M) or the rate coefficients
Lambda+Xi are Omega(M^2). These alternatives are not ruled out here. -/
theorem thirdFullPhysical_noH3Trace_profileTerminalClock_or_quadraticPDERate244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T)
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n)
    (hMTop : Tendsto M atTop atTop) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ) (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k, ThirdFullProfileAnchoredPDEWindow244 hH3 M τ N K C δ (v k)) ∧
      Summable (fun k : ℕ => δ (v k) * (M (v k) / 4)) ∧
      (∀ᶠ k : ℕ in atTop,
        (T - τ (v k)) * M (v k) < 4 ∨
        M (v k) ^ 2 < 8 *
          (h3PathFiniteAnnulusPDEVariationCoefficient244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
              (K (v k)) (C (v k)) +
           h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
            ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
              (C (v k)) + 1)) := by
  obtain ⟨τ, N, K, C, δ, v, hMono, hLimit, hSeparated, hWindows, hSum⟩ :=
    thirdFullPhysical_noH3Trace_disjointProfileAnchoredPDECharges244
      hH3 hClass b hb hNoTrace hDInt M hM
  have hNonneg (k : ℕ) : 0 ≤ δ (v k) * (M (v k) / 4) := by
    have hInfo := (hWindows k).2
    rcases hInfo with ⟨_, _, _, hδ, _, _, _, _, _, _, _, _, _⟩
    exact mul_nonneg hδ.le (div_nonneg (hM (v k)).le (by norm_num))
  have hSummable : Summable
      (fun k : ℕ => δ (v k) * (M (v k) / 4)) :=
    summable_of_sum_range_le hNonneg hSum
  have hZero : Tendsto (fun k : ℕ => δ (v k) * (M (v k) / 4))
      atTop (𝓝 (0 : ℝ)) := hSummable.tendsto_atTop_zero
  have hSmall : ∀ᶠ k : ℕ in atTop, δ (v k) * M (v k) < 1 := by
    have hEv : ∀ᶠ k : ℕ in atTop,
        δ (v k) * (M (v k) / 4) < 1 / 4 :=
      hZero.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [hEv] with k hk
    nlinarith only [hk]
  have hLarge : ∀ᶠ k : ℕ in atTop, 1 ≤ M (v k) :=
    (hMTop.comp hMono.tendsto_atTop).eventually (eventually_ge_atTop 1)
  refine ⟨τ, N, K, C, δ, v, hMono, hLimit, hSeparated,
    (fun k => (hWindows k).2), hSummable, ?_⟩
  filter_upwards [hSmall, hLarge] with k hSmallK hLargeK
  have hData := (hWindows k).2
  rcases hData with
    ⟨_, hK, hC, _hδ, _hδone, _hEnd, _hBase, _hSource,
      hHeight, hClock, _hBudget, _hFloor, _hCost⟩
  let G : H3SpectralVelocityState :=
    h3AuditActualSpectralVelocityTotal hH3 (τ (v k))
  let B : ℝ :=
    h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1) G -
    h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1) G
  let Λ : ℝ := h3PathFiniteAnnulusPDEVariationCoefficient244
    ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (K (v k)) (C (v k))
  let Ξ : ℝ := h3PathFiniteAnnulusPDEAnchoredQuadraticCoefficient244
    ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))
  have hB : M (v k) / 2 < B := by
    simpa only [B, G] using hHeight
  have hΛ : 0 ≤ Λ :=
    h3Path_finiteAnnulusPDEVariationCoefficient_nonneg244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1)
      (K (v k)) (C (v k)) hK hC
  have hΞ : 0 ≤ Ξ :=
    h3Path_finiteAnnulusPDEAnchoredQuadraticCoefficient_nonneg244
      ((v k : ℝ) + 1) ((N (v k) : ℝ) + 1) (C (v k))
  have hExact : δ (v k) = min ((T - τ (v k)) / 4)
      (min (1 : ℝ) ((B - M (v k) / 4) / (2 * (Λ + Ξ + 1)))) := by
    simpa only [thirdFullProfileAnchoredPDEWidth244, B, Λ, Ξ, G]
      using hClock
  have hAlt := thirdFull_exactPDEClock_smallCharge_forces_clockOrQuadraticRate244
    (τ (v k)) T (M (v k)) B Λ Ξ (δ (v k))
    hLargeK hB hΛ hΞ hExact hSmallK
  simpa only [Λ, Ξ] using hAlt

end
end PrimeTensor.FirstMonomialTriad
