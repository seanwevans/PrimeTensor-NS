import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalTopRawCubicClock244
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.Transfer.Absorption.Profile.Component.Representative
import Mathlib.Tactic

/-!
# Freeze one actual third-radial Leray forcing coordinate at terminal escape

A physical fourth-radial mass escaping every bound forces unbounded genuine
third-radial Leray forcing mass. The forcing mass is an exact finite sum

  (2π)^6 * ∑ (j : Fin 3), ‖F³_j(t)‖².

A finite-union argument freezes a SINGLE j before taking the forcing-growth
threshold. Continuity of this fixed Hilbert-state path on positive strict
time slices then forces unboundedness on EVERY later subtail, not just on
(s,T). Its squared norm is exactly the already formalized raw Fourier integral
of |ξ|^6 times the squared Leray projection of div(U tensor U).

These are necessary conditions for physical D3 escape, not a bound on the
nonlinear product or a proof of continuation.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 1800000

/-- A finite sum cannot escape every finite ceiling unless one FIXED summand
escapes every ceiling. No sign assumption on the summands is needed. -/
theorem h3_scalar_unboundedFiniteSum_forces_fixedSummand244
    {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (S : Set ℝ)
    (hSum : ∀ K : ℝ, ∃ r : ℝ, r ∈ S ∧ K < ∑ j : ι, f j r) :
    ∃ j : ι, ∀ K : ℝ, ∃ r : ℝ, r ∈ S ∧ K < f j r := by
  classical
  by_contra hNone
  have hNot (j : ι) :
      ¬ (∀ K : ℝ, ∃ r : ℝ, r ∈ S ∧ K < f j r) := by
    intro hUnbounded
    exact hNone ⟨j, hUnbounded⟩
  have hBound (j : ι) :
      ∃ B : ℝ, ∀ r : ℝ, r ∈ S → f j r ≤ B := by
    have hn := hNot j
    push Not at hn
    exact hn
  choose B hB using hBound
  obtain ⟨r, hr, hLarge⟩ := hSum (∑ j : ι, B j)
  have hSmall : (∑ j : ι, f j r) ≤ ∑ j : ι, B j := by
    apply Finset.sum_le_sum
    intro j hj
    exact hB j r hr
  exact (not_lt_of_ge hSmall) hLarge

/-- Escape of physical D3 freezes a single actual third-radial Leray
forcing Hilbert component, with no D3 positivity or endpoint-Cauchy premise. -/
theorem h3Path_unboundedPhysicalTop_forces_fixedThirdRadialForcingComponent244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t) :
    ∃ j₀ : Fin 3, ∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
        hH3 hClass j₀ r‖ : ℝ) ^ 2 := by
  let f (j : Fin 3) (r : ℝ) : ℝ :=
    (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
      hH3 hClass j r‖ : ℝ) ^ 2
  let c : ℝ := (2 * Real.pi) ^ 6
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hSum : ∀ K : ℝ, ∃ r, r ∈ Set.Ioo s T ∧
      K < ∑ j : Fin 3, f j r := by
    intro K
    obtain ⟨r, hr, hSpike⟩ :=
      h3Path_unboundedPhysicalTop_forces_highThirdRadialFourierNormSum244
        hH3 hClass hs hEscape (c * K)
    have hScaled : c * K < c * (∑ j : Fin 3, f j r) := by
      change c * K < c * (∑ j : Fin 3, f j r) at hSpike
      exact hSpike
    have hUnscaled : K < ∑ j : Fin 3, f j r := by
      by_contra hNot
      have hLe : (∑ j : Fin 3, f j r) ≤ K := le_of_not_gt hNot
      have hScaledLe : c * (∑ j : Fin 3, f j r) ≤ c * K :=
        mul_le_mul_of_nonneg_left hLe hc.le
      exact (not_lt_of_ge hScaledLe) hScaled
    exact ⟨r, hr, hUnscaled⟩
  obtain ⟨j₀, hj₀⟩ :=
    h3_scalar_unboundedFiniteSum_forces_fixedSummand244
      f (Set.Ioo s T) hSum
  exact ⟨j₀, hj₀⟩

/-- The SAME physical Leray forcing coordinate is unbounded on every later
strict terminal subtail. The step from an initial tail to arbitrary late
tails uses the established strong continuity of each Hilbert forcing path. -/
theorem h3Path_unboundedPhysicalTop_forces_fixedThirdRadialForcingCofinal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t) :
    ∃ j₀ : Fin 3, ∀ σ : ℝ, σ ∈ Set.Ioo s T →
      ∀ K : ℝ, ∃ r, r ∈ Set.Ioo σ T ∧
        K < (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
          hH3 hClass j₀ r‖ : ℝ) ^ 2 := by
  obtain ⟨j₀, hj₀⟩ :=
    h3Path_unboundedPhysicalTop_forces_fixedThirdRadialForcingComponent244
      hH3 hClass hs hEscape
  refine ⟨j₀, ?_⟩
  intro σ hσ K
  let f : ℝ → ℝ := fun r =>
    (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
      hH3 hClass j₀ r‖ : ℝ) ^ 2
  have hInside : Set.Icc s σ ⊆ Set.Ioo a T := by
    intro r hr
    exact ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 hσ.2⟩
  have hContinuous : ContinuousOn f (Set.Icc s σ) := by
    change ContinuousOn (fun r : ℝ =>
      (‖h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path
        hH3 hClass j₀ r‖ : ℝ) ^ 2) (Set.Icc s σ)
    exact ((h3TerminalPhysicalTopDissipationForcingThirdRadialFourierL2Path_continuousOn
      hH3 hClass j₀).norm.pow 2).mono hInside
  obtain ⟨r₀, _hr₀, hMax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hσ.1.le) hContinuous
  obtain ⟨r, hr, hLarge⟩ := hj₀ (max K (f r₀))
  change max K (f r₀) < f r at hLarge
  have hLate : σ < r := by
    by_contra hNot
    have hrSmall : r ∈ Set.Icc s σ := ⟨hr.1.le, le_of_not_gt hNot⟩
    have hBound : f r ≤ f r₀ := hMax hrSmall
    have hStrict : f r₀ < f r :=
      lt_of_le_of_lt (le_max_right K (f r₀)) hLarge
    exact (not_lt_of_ge hBound) hStrict
  exact ⟨r, ⟨hLate, hr.2⟩,
    lt_of_le_of_lt (le_max_left K (f r₀)) hLarge⟩

/-- The frozen cofinal coordinate is the genuine weighted Fourier Leray
velocity-product integral, via the prior raw representative identity. -/
theorem h3Path_unboundedPhysicalTop_forces_fixedRawLerayFourierMassCofinal244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T)
    (hEscape : ∀ M : ℝ, ∃ t, t ∈ Set.Ioo s T ∧
      M < velocityH3Dissipation3At u t) :
    ∃ j₀ : Fin 3, ∀ σ : ℝ, σ ∈ Set.Ioo s T →
      ∀ K : ℝ, ∃ r, r ∈ Set.Ioo σ T ∧
        K < h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath
          hH3 hClass j₀ r := by
  obtain ⟨j₀, hj₀⟩ :=
    h3Path_unboundedPhysicalTop_forces_fixedThirdRadialForcingCofinal244
      hH3 hClass hs hEscape
  refine ⟨j₀, ?_⟩
  intro σ hσ K
  obtain ⟨r, hr, hLarge⟩ := hj₀ σ hσ K
  refine ⟨r, hr, ?_⟩
  have hrClass : r ∈ Set.Ioo a T :=
    ⟨lt_trans hs.1 (lt_trans hσ.1 hr.1), hr.2⟩
  rw [h3TerminalPhysicalTopDissipationForcingThirdRadialRawFourierMassPath_eq_norm_sq_path
    hH3 hClass hrClass j₀]
  exact hLarge

end
end PrimeTensor.FirstMonomialTriad
