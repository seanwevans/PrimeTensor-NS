import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticGaugeEighthCutoffBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEDisjointCostCollapse244
import Mathlib.Tactic

/-!
# Finite extended physical H3 dissipation forces kinetic annular charge collapse

The preceding kinetic cofinal construction selected exact positive physical
annular windows and proved all their disjoint ENNReal height-width sums are
bounded by the single global extended physical H3 dissipation. If that
extended global cost is finite, conversion to real nonnegative sums proves
actual summability and hence decay of the SAME selected height-width charges.

Crucially, the exact kinetic width is a minimum of remaining physical time
and a frequency-controlled PDE rate. The scalar minimum identity gives the
sharp quantitative alternative: a small charge forces either a small
height-weighted terminal clock, or a large outer kinetic PDE rate. This
is a *necessary concentration law*, not global regularity and not a bound
on the rate/cutoff. No full-H3 endpoint trace or full-dissipation continuity
is assumed. Finite ENNReal cost is a separate, explicit premise.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter Topology
open scoped BigOperators Interval ENNReal

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

/-- An ENNReal bound on all nonnegative disjoint height-width sums gives
summability over the reals. The finite extended budget is an explicit input;
no interval integrability of the underlying full physical density is used. -/
theorem thirdFull_scalar_finiteExtendedBudget_forces_realChargeSummable244
    (w H : ℕ → ℝ) (C : ℝ)
    (hw : ∀ k, 0 ≤ w k) (hH : ∀ k, 0 ≤ H k) (hC : 0 ≤ C)
    (hBound : ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
        ENNReal.ofReal (H k) * ENNReal.ofReal (w k)) ≤
        ENNReal.ofReal C) :
    Summable (fun k => w k * H k) ∧
      Tendsto (fun k => w k * H k) atTop (𝓝 (0 : ℝ)) := by
  have hNonneg (k : ℕ) : 0 ≤ w k * H k :=
    mul_nonneg (hw k) (hH k)
  have hRealBound (m : ℕ) :
      (∑ k ∈ Finset.range m, w k * H k) ≤ C := by
    apply (ENNReal.ofReal_le_ofReal_iff hC).mp
    calc
      ENNReal.ofReal (∑ k ∈ Finset.range m, w k * H k) =
          ∑ k ∈ Finset.range m, ENNReal.ofReal (w k * H k) :=
        ENNReal.ofReal_sum_of_nonneg
          (s := Finset.range m) (f := fun k => w k * H k)
          (fun k _ => hNonneg k)
      _ = ∑ k ∈ Finset.range m,
            ENNReal.ofReal (H k) * ENNReal.ofReal (w k) := by
        apply Finset.sum_congr rfl
        intro k _hk
        calc
          ENNReal.ofReal (w k * H k) =
              ENNReal.ofReal (H k * w k) := by rw [mul_comm]
          _ = ENNReal.ofReal (H k) * ENNReal.ofReal (w k) :=
            ENNReal.ofReal_mul (hH k)
      _ ≤ ENNReal.ofReal C := hBound m
  have hSum : Summable (fun k => w k * H k) :=
    h3Path_nonnegativeBoundedRangeSums_summable244
      (fun k => w k * H k) C hNonneg hRealBound
  exact ⟨hSum, hSum.tendsto_atTop_zero⟩

/-- The exact minimum in a kinetic annular PDE clock yields a sharp
height-time or rate-height charge split. The constants 16 and 32 follow
by direct algebra, not from the weaker earlier midpoint-clock lemma. -/
theorem thirdFull_scalar_exactKineticWidth_smallCharge_fork244
    (T x M Λ δ B : ℝ)
    (hM : 0 ≤ M) (hΛ : 0 ≤ Λ)
    (hWidth : δ = min ((T - x) / 4)
      ((M / 4) / (2 * (Λ + 1))))
    (hCost : δ * (M / 4) ≤ B) :
    (T - x) * M ≤ 16 * B ∨
      M ^ 2 ≤ 32 * (Λ + 1) * B := by
  have hDen : 0 < 2 * (Λ + 1) := by linarith only [hΛ]
  rcases le_total ((T - x) / 4) ((M / 4) / (2 * (Λ + 1))) with hLe | hLe
  · left
    have hExact : δ = (T - x) / 4 :=
      hWidth.trans (min_eq_left hLe)
    rw [hExact] at hCost
    nlinarith only [hCost]
  · right
    have hExact : δ = (M / 4) / (2 * (Λ + 1)) :=
      hWidth.trans (min_eq_right hLe)
    rw [hExact] at hCost
    have hNormalized :
        (M / 4 * (M / 4)) / (2 * (Λ + 1)) ≤ B := by
      convert hCost using 1 <;> ring
    have hScaled := (div_le_iff₀ hDen).mp hNormalized
    nlinarith only [hScaled]

/-- The original no-terminal-H3-trace kinetic cofinal windows, with
exact radii N and widths delta, inherit SUMMABILITY and vanishing physical
height-width cost if the single global extended viscous integral is finite.
For any positive epsilon, sufficiently late witnesses must compress either
the true terminal time-weighted height or the inverse kinetic PDE rate.
No selected window is changed and no full-H3 interval L1 assumption enters. -/
theorem thirdFullPhysical_noH3Trace_finiteExtendedBudget_kineticChargeCollapse244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three} {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (hNoTrace : ¬ ∃ L : H3SpectralVelocityState,
      Tendsto (h3AuditActualSpectralVelocityTotal hH3)
        (𝓝[<] T) (𝓝 L))
    (M : ℕ → ℝ) (hM : ∀ n : ℕ, 0 < M n)
    (C : ℝ) (hC : 0 ≤ C)
    (hGlobal :
      (∫⁻ r in Set.Ioo a T,
        ENNReal.ofReal (velocityH3DissipationAt u r) ∂volume) ≤
          ENNReal.ofReal C) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ)
        (v : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      (∀ k : ℕ, k ≤ v k) ∧
      (∀ k : ℕ,
        ThirdFullKineticNaturalAnnularLocalWitness244
          hH3 b (τ (v k)) (v k) (N (v k))
          (M (v k)) (δ (v k))) ∧
      Summable (fun k => δ (v k) * (M (v k) / 4)) ∧
      Tendsto (fun k => δ (v k) * (M (v k) / 4))
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
        (T - τ (v k)) * M (v k) ≤ 16 * ε ∨
        (M (v k)) ^ 2 ≤
          32 * (thirdFullPhysicalKineticLowBandDissipationRate244
              (N (v k)) (velocityH3Energy0At u b) +
            thirdFullPhysicalKineticLowBandDissipationRate244
              (v k) (velocityH3Energy0At u b) + 1) * ε) := by
  obtain ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
      hIndex, hWindow, hCharge, _hDivergence⟩ :=
    thirdFullPhysical_noH3Trace_kineticDisjointGlobalExtendedBudget244
      hH3 hClass b hb hNoTrace M hM
  let w : ℕ → ℝ := fun k => δ (v k)
  let H : ℕ → ℝ := fun k => M (v k) / 4
  have hw (k : ℕ) : 0 ≤ w k := by
    rcases hWindow k with ⟨_, hp, _, _, _, _⟩
    exact hp.le
  have hH (k : ℕ) : 0 ≤ H k := by
    dsimp only [H]
    have hp := hM (v k)
    linarith only [hp]
  have hFinite (m : ℕ) :
      (∑ k ∈ Finset.range m,
        ENNReal.ofReal (H k) * ENNReal.ofReal (w k)) ≤
        ENNReal.ofReal C :=
    (hCharge m).trans hGlobal
  obtain ⟨hSummable, hZero⟩ :=
    thirdFull_scalar_finiteExtendedBudget_forces_realChargeSummable244
      w H C hw hH hC hFinite
  refine ⟨τ, N, δ, v, hv, hCofinal, hSeparated,
    hIndex, hWindow, hSummable, hZero, ?_⟩
  intro ε hε
  have hNear : ∀ᶠ k : ℕ in atTop, w k * H k < ε :=
    hZero.eventually (eventually_lt_nhds hε)
  filter_upwards [hNear] with k hk
  obtain ⟨_hnN, _hδ, hEq, _hEnd, _hFloor, _hCost⟩ := hWindow k
  let Λ : ℝ :=
    thirdFullPhysicalKineticLowBandDissipationRate244
      (N (v k)) (velocityH3Energy0At u b) +
    thirdFullPhysicalKineticLowBandDissipationRate244
      (v k) (velocityH3Energy0At u b)
  have hΛ : 0 ≤ Λ := add_nonneg
    (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 (N (v k)) _)
    (thirdFullPhysicalKineticLowBandDissipationRate_nonneg244 (v k) _)
  have hCost : δ (v k) * (M (v k) / 4) ≤ ε := by
    exact hk.le
  have hFork := thirdFull_scalar_exactKineticWidth_smallCharge_fork244
    T (τ (v k)) (M (v k)) Λ (δ (v k)) ε
    (hM (v k)).le hΛ (by simpa only [Λ] using hEq) hCost
  simpa only [Λ] using hFork

end
end PrimeTensor.FirstMonomialTriad
