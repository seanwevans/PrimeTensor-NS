import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEFirstCrossingShellNinthEighth244
import Mathlib.Tactic

/-!
# Critical kinetic shell mass versus relative Fourier frequency

At the canonical physical first crossing, the width-averaged shell pigeonhole
produces (3/4) R^3 < 4 L J^8 μ, where R is the inner frequency, L the
number of integer shells, J the selected shell's outer shifted frequency,
and μ its actual raw Fourier kinetic mass.

This module proves a sharp *conditional location/mass alternative*:

  A R < J  or  3 < 16 A^8 L R^5 μ.

Consequently, if the critical width-weighted kinetic shell mass L R^5 μ
vanishes, J/R tends to +∞: the selected energetic shell has to migrate
arbitrarily far from the inner frequency scale. This is conditional; neither
the kinetic vanishing nor a width bound is inferred from finite H³
dissipation. The physical theorem retains the ninth/eighth PDE alternative
on the exact same disjoint-window witnesses.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Pure arithmetic: a shell paying the cubic dissipation cost either lies
above A times the inner frequency, or has nonvanishing *critical* kinetic
mass L R^5 μ. No unjustified upper bound on annular width is used. -/
theorem h3Path_widthShell_nearInner_or_criticalMass244
    (R J L μ A : ℝ) (hR : 0 < R) (hJ : 0 ≤ J)
    (hL : 0 ≤ L) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (hCost : 3 * R ^ 3 / 4 < L * (4 * J ^ 8 * μ)) :
    A * R < J ∨ 3 < 16 * A ^ 8 * L * R ^ 5 * μ := by
  by_cases hFar : A * R < J
  · exact Or.inl hFar
  · right
    have hNear : J ≤ A * R := le_of_not_gt hFar
    have hPower : J ^ 8 ≤ (A * R) ^ 8 :=
      pow_le_pow_left₀ hJ hNear 8
    have hCoefficient : 0 ≤ L * (4 * μ) := by positivity
    have hUpper : L * (4 * J ^ 8 * μ) ≤
        L * (4 * (A * R) ^ 8 * μ) := by
      calc
        _ = (L * (4 * μ)) * J ^ 8 := by ring
        _ ≤ (L * (4 * μ)) * (A * R) ^ 8 :=
          mul_le_mul_of_nonneg_left hPower hCoefficient
        _ = L * (4 * (A * R) ^ 8 * μ) := by ring
    have hUpperCost : 3 * R ^ 3 / 4 <
        L * (4 * (A * R) ^ 8 * μ) := lt_of_lt_of_le hCost hUpper
    have hCancel : R ^ 3 * 3 <
        R ^ 3 * (16 * A ^ 8 * L * R ^ 5 * μ) := by
      calc
        _ = 4 * (3 * R ^ 3 / 4) := by ring
        _ < 4 * (L * (4 * (A * R) ^ 8 * μ)) :=
          mul_lt_mul_of_pos_left hUpperCost (by norm_num)
        _ = R ^ 3 * (16 * A ^ 8 * L * R ^ 5 * μ) := by ring
    have hR3 : 0 < R ^ 3 := pow_pos hR 3
    by_contra hNot
    have hReverse : 16 * A ^ 8 * L * R ^ 5 * μ ≤ 3 :=
      le_of_not_gt hNot
    have hScaledReverse :=
      mul_le_mul_of_nonneg_left hReverse hR3.le
    exact (not_le_of_gt hCancel) hScaledReverse

/-- If the critical kinetic mass of width-averaged shells goes to zero,
those selected shells cannot stay in any fixed multiple of their inner
frequency, even though their *absolute* raw L² mass may also vanish. -/
theorem h3Path_widthShell_criticalMassVanishing_relativeEscape244
    (R J L μ : ℕ → ℝ)
    (hR : ∀ k, 0 < R k) (hJ : ∀ k, 0 ≤ J k)
    (hL : ∀ k, 0 ≤ L k) (hμ : ∀ k, 0 ≤ μ k)
    (hCost : ∀ k, 3 * (R k) ^ 3 / 4 <
      L k * (4 * (J k) ^ 8 * μ k))
    (hCritical : Tendsto (fun k => L k * (R k) ^ 5 * μ k)
      atTop (𝓝 0)) :
    Tendsto (fun k => J k / R k) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro A
  let B : ℝ := max A 0
  have hB : 0 ≤ B := le_max_right _ _
  have hSmall : ∀ᶠ k : ℕ in atTop,
      16 * B ^ 8 * (L k * R k ^ 5 * μ k) < 3 := by
    have hScaled : Tendsto
        (fun k : ℕ => 16 * B ^ 8 * (L k * R k ^ 5 * μ k))
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hCritical.const_mul (16 * B ^ 8)
    exact hScaled.eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 3))
  filter_upwards [hSmall] with k hk
  have hAlternative := h3Path_widthShell_nearInner_or_criticalMass244
    (R k) (J k) (L k) (μ k) B (hR k) (hJ k) (hL k)
    (hμ k) hB (hCost k)
  rcases hAlternative with hFar | hMass
  · have hAB : A ≤ B := le_max_left _ _
    have hALe : A * R k ≤ B * R k :=
      mul_le_mul_of_nonneg_right hAB (hR k).le
    exact (le_div_iff₀ (hR k)).2 (lt_of_le_of_lt hALe hFar).le
  · have hEq : 16 * B ^ 8 * (L k * R k ^ 5 * μ k) =
        16 * B ^ 8 * L k * R k ^ 5 * μ k := by ring
    rw [hEq] at hk
    exact False.elim (lt_asymm hMass hk)

/-- The physical selected Fourier shell admits the pointwise near-inner
location/critical-mass alternative. The shell is selected by the same
quadratic-sharp PDE windows which supply conditional ninth/eighth growth.
A vanishing *width-weighted* critical kinetic mass therefore forces its
frequency to escape every multiple of the inner radius. -/
theorem h3Path_noL2Trace_finiteDissipation_criticalShellEscape244
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hMass : 0 < h3PathCanonicalTerminalKineticEnergyAt u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U))
    (hDInt : IntervalIntegrable (velocityH3DissipationAt u) volume a T) :
    ∃ (τ : ℕ → ℝ) (N : ℕ → ℕ) (K C δ : ℕ → ℝ)
        (v m : ℕ → ℕ),
      StrictMono v ∧
      Tendsto (fun k : ℕ => τ (v k)) atTop (𝓝 T) ∧
      (∀ n : ℕ, τ n ∈ Set.Ioo a T) ∧
      (∀ k l : ℕ, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k : ℕ => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k : ℕ, v k ≤ m k ∧ m k < N (v k) ∧
        0 < h3PathActualBandRawKineticMass244
          ((m k : ℝ) + 1) ((m k : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ A : ℝ, 0 ≤ A → ∀ k : ℕ,
        A * ((v k : ℝ) + 1) < ((m k : ℝ) + 3) ∨
        3 < 16 * A ^ 8 * ((N (v k) - v k : ℕ) : ℝ) *
          (((v k : ℝ) + 1) ^ 5) *
          h3PathActualBandRawKineticMass244
            ((m k : ℝ) + 1) ((m k : ℝ) + 2)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (Tendsto (fun k : ℕ =>
          ((N (v k) - v k : ℕ) : ℝ) * (((v k : ℝ) + 1) ^ 5) *
          h3PathActualBandRawKineticMass244
            ((m k : ℝ) + 1) ((m k : ℝ) + 2)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))
        atTop (𝓝 0) →
        Tendsto (fun k : ℕ =>
          ((m k : ℝ) + 3) / ((v k : ℝ) + 1)) atTop atTop) ∧
      (∀ η B S M : ℝ, 0 < η → 0 ≤ B → 0 ≤ M →
        ∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) →
            h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
              B * ((v k : ℝ) + 1) ^ 6 →
            C (v k) ^ 2 ≤ S ^ 2 →
              M * ((v k : ℝ) + 1) ^ 9 <
                (((N (v k) : ℝ) + 1) + 1) ^ 8) := by
  obtain ⟨τ, N, K, C, δ, v, m, hv, hCofinal, hTime, hSeparate,
      _hGap, hSummable, _hMinimal, _hTail, _hBand, hShell,
      _hLast, hOuter⟩ :=
    h3Path_noL2Trace_finiteDissipation_minimalShellNinthEighth244
      hH3 hClass hMass hNoTrace hDInt
  let R : ℕ → ℝ := fun k => ((v k : ℝ) + 1)
  let J : ℕ → ℝ := fun k => ((m k : ℝ) + 3)
  let L : ℕ → ℝ := fun k => ((N (v k) - v k : ℕ) : ℝ)
  let μ : ℕ → ℝ := fun k =>
    h3PathActualBandRawKineticMass244
      ((m k : ℝ) + 1) ((m k : ℝ) + 2)
      (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))
  have hR : ∀ k, 0 < R k := by
    intro k
    dsimp only [R]
    positivity
  have hJ : ∀ k, 0 ≤ J k := by
    intro k
    dsimp only [J]
    positivity
  have hL : ∀ k, 0 ≤ L k := by
    intro k
    dsimp only [L]
    exact Nat.cast_nonneg _
  have hμ : ∀ k, 0 ≤ μ k := by
    intro k
    dsimp only [μ]
    exact (hShell k).2.2.2.1.le
  have hCost (k : ℕ) : 3 * (R k) ^ 3 / 4 <
      L k * (4 * (J k) ^ 8 * μ k) := by
    simpa only [R, J, L, μ] using (hShell k).2.2.2.2
  refine ⟨τ, N, K, C, δ, v, m, hv, hCofinal, hTime,
    hSeparate, hSummable, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(hShell k).1, (hShell k).2.1, (hShell k).2.2.2.1⟩
  · intro A hA k
    have hAlt := h3Path_widthShell_nearInner_or_criticalMass244
      (R k) (J k) (L k) (μ k) A (hR k) (hJ k) (hL k)
      (hμ k) hA (hCost k)
    simpa only [R, J, L, μ] using hAlt
  · intro hCritical
    exact h3Path_widthShell_criticalMassVanishing_relativeEscape244
      R J L μ hR hJ hL hμ hCost
      (by simpa only [R, J, L, μ] using hCritical)
  · intro η B S M hη hB hM
    filter_upwards [hOuter η B S M hη hB hM] with k hk
    intro hGeom hLinear hSource
    exact (hk hGeom hLinear hSource).1

end
end PrimeTensor.FirstMonomialTriad
