import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralKineticAnchoredLowDissipationBudget244
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Kinetic-budget localization of time-averaged physical H³ dissipation

The previous kinetic-anchored theorem controls physical H³ dissipation below
any fixed radial cutoff by a constant C(b,ρ), uniformly at all later times.
This file identifies the exact temporal condition needed to promote this
upper budget into dominance of *integrated* high-frequency dissipation.

For a strict interval I=[s,t] within the tail, the proved comparison is

    ∫_I D_high ≤ ∫_I D_full ≤ ∫_I D_high + (t-s) C(b,ρ).

Thus large time-average full dissipation forces large time-average high-radial
dissipation. More precisely, on any sequence of strict intervals for which

    (n+1) C(b,ρ) (t_n-s_n) < ∫_{s_n}^{t_n} D_full,

the corresponding integrated high-frequency fraction tends to one.

This conditional temporal statement does *not* follow from an arbitrarily
large pointwise dissipation sequence without a persistence-width estimate;
none is smuggled into the hypotheses.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeH3IntegratedHighRadialAverage244
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3IntegratedHighRadialAverage244 :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- On strict physical time intervals, the integral of high-radial
physical H³ dissipation does not exceed the integral of full dissipation.
Only the interval integrability of the two functions is used. -/
theorem h3Path_highRadialDissipation_integral_le_full244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ρ : ℝ) (s t : ℝ)
    (hs : s ∈ Set.Ioo a T) (ht : t ∈ Set.Ioo a T) (hst : s ≤ t)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume s t)
    (hHighInt : IntervalIntegrable (fun r : ℝ =>
      h3PathActualHighRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 r)) volume s t) :
    (∫ r in s..t, h3PathActualHighRadialDissipation244 ρ
      (h3AuditActualSpectralVelocityTotal hH3 r)) ≤
      ∫ r in s..t, velocityH3DissipationAt u r := by
  apply intervalIntegral.integral_mono_on hst hHighInt hDInt
  intro r hr
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hLow : 0 ≤ h3PathActualLowRadialDissipation244 ρ
      (h3AuditActualSpectralVelocityTotal hH3 r) := by
    unfold h3PathActualLowRadialDissipation244
    apply integral_nonneg
    intro ξ
    exact h3TerminalSpectralDissipationSingleDensity_nonneg
      (h3AuditActualSpectralVelocityTotal hH3 r) ξ
  have hPartition := h3Path_actualRadialDissipation_partition244
    hH3 hClass r hrClass ρ
  linarith only [hLow, hPartition]

/-- A physical integrated dissipation cost above the low-frequency kinetic
budget must appear in the high-frequency integral. This is an integral
comparison, with no assumed persistence of individual high peaks. -/
theorem h3Path_fullDissipation_integral_excess_forces_highRadialCost244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (s t : ℝ) (hs : s ∈ Set.Ioo b T)
    (ht : t ∈ Set.Ioo b T) (hst : s ≤ t)
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume s t)
    (hHighInt : IntervalIntegrable (fun r : ℝ =>
      h3PathActualHighRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 r)) volume s t)
    (m : ℝ)
    (hExcess : (t - s) *
        (ρ ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling ρ *
          velocityH3Energy0At u b) + m) <
        (∫ r in s..t, velocityH3DissipationAt u r)) :
    (t - s) * m <
      (∫ r in s..t, h3PathActualHighRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 r)) := by
  have hBudget := h3Path_physicalDissipation_integral_le_highPlusKineticBudget244
    hH3 hClass b hb ρ hρ s t hs ht hst hDInt hHighInt
  have hExpand : (t - s) *
      (ρ ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling ρ *
        velocityH3Energy0At u b) + m) =
      (t - s) * (ρ ^ 2 *
        (h3TerminalRadialSobolevWeightSquareCeiling ρ *
          velocityH3Energy0At u b)) + (t - s) * m := by ring
  rw [hExpand] at hExcess
  linarith only [hExcess, hBudget]

/-- An algebraic time-average lemma: if the loss from full to high-frequency
integral is bounded by a nonnegative ceiling times interval length, and
full time-average is larger than `(n+1)` times that ceiling, then the high
fraction of the *integrated* full dissipation tends to one. -/
theorem h3Path_kineticCeiling_largeAverages_highIntegralShare_tendsto_one244
    (C width D H : ℕ → ℝ)
    (hC : ∀ n : ℕ, 0 ≤ C n)
    (hWidth : ∀ n : ℕ, 0 ≤ width n)
    (hLower : ∀ n : ℕ, H n ≤ D n)
    (hUpper : ∀ n : ℕ, D n ≤ H n + C n * width n)
    (hAverage : ∀ n : ℕ,
      ((n : ℝ) + 1) * (C n * width n) < D n) :
    Tendsto (fun n : ℕ => H n / D n) atTop (𝓝 1) := by
  let F : ℕ → ℝ := fun n => 1 - H n / D n
  have hDPos (n : ℕ) : 0 < D n := by
    have hCW : 0 ≤ C n * width n := mul_nonneg (hC n) (hWidth n)
    have hScaled : 0 ≤ ((n : ℝ) + 1) * (C n * width n) :=
      mul_nonneg (by positivity) hCW
    exact lt_of_le_of_lt hScaled (hAverage n)
  have hGap (n : ℕ) : 0 ≤ D n - H n := by
    linarith only [hLower n]
  have hGapLe (n : ℕ) : D n - H n ≤ C n * width n := by
    linarith only [hUpper n]
  have hFDiv (n : ℕ) : F n = (D n - H n) / D n := by
    dsimp only [F]
    have hD : D n ≠ 0 := ne_of_gt (hDPos n)
    field_simp [hD]
    <;> ring
  have hFNonneg (n : ℕ) : 0 ≤ F n := by
    rw [hFDiv]
    exact div_nonneg (hGap n) (hDPos n).le
  have hFBound (n : ℕ) : F n ≤ 1 / ((n : ℝ) + 1) := by
    rw [hFDiv]
    have hR : 0 < (n : ℝ) + 1 := by positivity
    have hMul : ((n : ℝ) + 1) * (D n - H n) ≤
        ((n : ℝ) + 1) * (C n * width n) :=
      mul_le_mul_of_nonneg_left (hGapLe n) hR.le
    have hResult : (D n - H n) * ((n : ℝ) + 1) ≤ D n := by
      nlinarith only [hMul, hAverage n]
    exact (div_le_div_iff₀ (hDPos n) hR).2 (by
      simpa only [one_mul] using hResult)
  have hNorm (n : ℕ) : ‖F n‖ ≤ 1 / ((n : ℝ) + 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hFNonneg n)]
    exact hFBound n
  have hInv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hFTendsto : Tendsto F atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).2 (by
      simpa only [sub_zero] using
        (squeeze_zero'
          (Filter.Eventually.of_forall (fun n => norm_nonneg (F n)))
          (Filter.Eventually.of_forall hNorm) hInv))
  have hOneMinus : Tendsto (fun n : ℕ => 1 - F n)
      atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hFTendsto
  have hEq : (fun n : ℕ => 1 - F n) =
      (fun n : ℕ => H n / D n) := by
    funext n
    dsimp only [F]
    ring
  simpa only [sub_zero, hEq] using hOneMinus

/-- For any sequence of positive-length strict time windows, if average
physical H³ dissipation grows above `(n+1)` times the fixed kinetic-anchored
low-frequency ceiling, the fraction of the *time-integrated* dissipation
above that cutoff tends to one on those same windows. -/
theorem h3Path_kineticAnchored_highRadialIntegratedShare_tendsto_one244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (b : ℝ) (hb : b ∈ Set.Ioo a T)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (s t : ℕ → ℝ)
    (hs : ∀ n : ℕ, s n ∈ Set.Ioo b T)
    (ht : ∀ n : ℕ, t n ∈ Set.Ioo b T)
    (hst : ∀ n : ℕ, s n < t n)
    (hDInt : ∀ n : ℕ,
      IntervalIntegrable (velocityH3DissipationAt u) volume (s n) (t n))
    (hHighInt : ∀ n : ℕ,
      IntervalIntegrable (fun r : ℝ =>
        h3PathActualHighRadialDissipation244 ρ
          (h3AuditActualSpectralVelocityTotal hH3 r)) volume (s n) (t n))
    (hAverage : ∀ n : ℕ,
      ((n : ℝ) + 1) *
          ((ρ ^ 2 * (h3TerminalRadialSobolevWeightSquareCeiling ρ *
            velocityH3Energy0At u b)) * (t n - s n)) <
        (∫ r in s n..t n, velocityH3DissipationAt u r)) :
    Tendsto (fun n : ℕ =>
      (∫ r in s n..t n, h3PathActualHighRadialDissipation244 ρ
        (h3AuditActualSpectralVelocityTotal hH3 r)) /
      (∫ r in s n..t n, velocityH3DissipationAt u r))
      atTop (𝓝 1) := by
  let C : ℝ := ρ ^ 2 *
    (h3TerminalRadialSobolevWeightSquareCeiling ρ * velocityH3Energy0At u b)
  let W : ℕ → ℝ := fun n => t n - s n
  let D : ℕ → ℝ := fun n =>
    ∫ r in s n..t n, velocityH3DissipationAt u r
  let H : ℕ → ℝ := fun n =>
    ∫ r in s n..t n, h3PathActualHighRadialDissipation244 ρ
      (h3AuditActualSpectralVelocityTotal hH3 r)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (sq_nonneg ρ)
      (mul_nonneg (h3TerminalRadialSobolevWeightSquareCeiling_pos ρ).le
        (velocityH3Energy0At_nonneg u b))
  have hWidth (n : ℕ) : 0 ≤ W n := by
    dsimp only [W]
    linarith only [hst n]
  have hLower (n : ℕ) : H n ≤ D n := by
    have h := h3Path_highRadialDissipation_integral_le_full244
      hH3 hClass ρ (s n) (t n)
      ⟨lt_trans hb.1 (hs n).1, (hs n).2⟩
      ⟨lt_trans hb.1 (ht n).1, (ht n).2⟩
      (hst n).le (hDInt n) (hHighInt n)
    exact h
  have hUpper (n : ℕ) : D n ≤ H n + C * W n := by
    have h := h3Path_physicalDissipation_integral_le_highPlusKineticBudget244
      hH3 hClass b hb ρ hρ (s n) (t n)
      (hs n) (ht n) (hst n).le (hDInt n) (hHighInt n)
    change D n ≤ W n * C + H n at h
    calc
      D n ≤ W n * C + H n := h
      _ = H n + C * W n := by ring
  have hHuge (n : ℕ) :
      ((n : ℝ) + 1) * (C * W n) < D n := by
    exact hAverage n
  have hTendsto :=
    h3Path_kineticCeiling_largeAverages_highIntegralShare_tendsto_one244
      (fun _ : ℕ => C) W D H (fun _ => hC)
      hWidth hLower hUpper hHuge
  exact hTendsto

end
end PrimeTensor.FirstMonomialTriad
