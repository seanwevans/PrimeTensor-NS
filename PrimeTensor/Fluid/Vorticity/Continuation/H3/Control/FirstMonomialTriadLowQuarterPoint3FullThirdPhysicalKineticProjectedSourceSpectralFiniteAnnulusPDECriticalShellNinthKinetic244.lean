import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECriticalWidthNinthEighth244
import Mathlib.Tactic

/-!
# Ninth/eighth energetic-shell localization under sixth-power kinetic depletion

The synchronized minimal first-crossing shell satisfies
  3 R^3 / 4 < L * (4 * J^8 * μ),
where R=v+1, L=N(v)-v, J=m+3, and μ is *actual shell-local* kinetic Fourier mass.
This file upgrades the earlier fifth-power critical-mass versus J/R alternative
into a ninth/eighth-frequency alternative:
  A R^9 < J^8  OR  3 < 16 A L R^6 μ.
Thus L R^6 μ -> 0 implies J^8/R^9 -> +∞, on the same physical PDE clocks.
The PDE ninth/eighth *width* divergence remains a separate conditional branch;
it does not force energetic-shell localization by itself.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Ninth/eighth frequency vs sixth-power-normalized Fourier kinetic mass:
no mass depletion assumption is hidden in this pointwise alternative. -/
theorem h3Path_widthShell_ninthEighth_or_sixthMass244
    (R J L μ A : ℝ) (hR : 0 < R)
    (hL : 0 ≤ L) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (hCost : 3 * R ^ 3 / 4 < L * (4 * J ^ 8 * μ)) :
    A * R ^ 9 < J ^ 8 ∨ 3 < 16 * A * L * R ^ 6 * μ := by
  by_cases hFar : A * R ^ 9 < J ^ 8
  · exact Or.inl hFar
  · right
    have hNear : J ^ 8 ≤ A * R ^ 9 := le_of_not_gt hFar
    have hCoef : 0 ≤ 16 * L * μ := by positivity
    have hCost' : 3 * R ^ 3 < 16 * L * J ^ 8 * μ := by
      calc
        _ = 4 * (3 * R ^ 3 / 4) := by ring
        _ < 4 * (L * (4 * J ^ 8 * μ)) :=
          mul_lt_mul_of_pos_left hCost (by norm_num)
        _ = 16 * L * J ^ 8 * μ := by ring
    have hUpper : 16 * L * J ^ 8 * μ ≤
        16 * L * (A * R ^ 9) * μ := by
      calc
        _ = (16 * L * μ) * J ^ 8 := by ring
        _ ≤ (16 * L * μ) * (A * R ^ 9) :=
          mul_le_mul_of_nonneg_left hNear hCoef
        _ = 16 * L * (A * R ^ 9) * μ := by ring
    have hCancel : R ^ 3 * 3 <
        R ^ 3 * (16 * A * L * R ^ 6 * μ) := by
      calc
        _ = 3 * R ^ 3 := by ring
        _ < 16 * L * J ^ 8 * μ := hCost'
        _ ≤ 16 * L * (A * R ^ 9) * μ := hUpper
        _ = R ^ 3 * (16 * A * L * R ^ 6 * μ) := by ring
    by_contra hNot
    have hReverse : 16 * A * L * R ^ 6 * μ ≤ 3 :=
      le_of_not_gt hNot
    have hScaled := mul_le_mul_of_nonneg_left hReverse
      (pow_nonneg hR.le 3)
    exact (not_le_of_gt hCancel) hScaled

/-- If width times sixth-power-normalized kinetic mass vanishes, the
selected shell itself escapes the *critical* ninth/eighth scale, not only
fixed multiples of the inner radius. -/
theorem h3Path_widthShell_sixthMassVanishing_ninthEighthEscape244
    (R J L μ : ℕ → ℝ)
    (hR : ∀ k, 0 < R k)
    (hL : ∀ k, 0 ≤ L k)
    (hμ : ∀ k, 0 ≤ μ k)
    (hCost : ∀ k, 3 * (R k) ^ 3 / 4 <
      L k * (4 * (J k) ^ 8 * μ k))
    (hSixth : Tendsto (fun k => L k * (R k) ^ 6 * μ k)
      atTop (𝓝 0)) :
    Tendsto (fun k => (J k) ^ 8 / (R k) ^ 9) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro A
  let B : ℝ := max A 0 + 1
  have hB : 0 ≤ B := by
    have hMax : (0 : ℝ) ≤ max A 0 := le_max_right _ _
    dsimp only [B]
    linarith only [hMax]
  have hAB : A ≤ B := by
    have hMax : A ≤ max A 0 := le_max_left _ _
    dsimp only [B]
    linarith only [hMax]
  have hSmall : ∀ᶠ k : ℕ in atTop,
      16 * B * (L k * R k ^ 6 * μ k) < 3 := by
    have hScaled : Tendsto
        (fun k : ℕ => 16 * B * (L k * R k ^ 6 * μ k))
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hSixth.const_mul (16 * B)
    exact hScaled.eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 3))
  filter_upwards [hSmall] with k hk
  have hAlternative := h3Path_widthShell_ninthEighth_or_sixthMass244
    (R k) (J k) (L k) (μ k) B (hR k) (hL k) (hμ k)
    hB (hCost k)
  rcases hAlternative with hFar | hMass
  · have hR9 : 0 < (R k) ^ 9 := pow_pos (hR k) 9
    have hDiv : B < (J k) ^ 8 / (R k) ^ 9 :=
      (lt_div_iff₀ hR9).2 hFar
    exact hAB.trans hDiv.le
  · have hEq : 16 * B * (L k * R k ^ 6 * μ k) =
        16 * B * L k * R k ^ 6 * μ k := by ring
    rw [hEq] at hk
    exact False.elim (lt_asymm hMass hk)

/-- Actual terminal snapshots carry the sixth-power kinetic-shell
alternative. On a separate, explicitly conditional PDE regime, the
containing annular width has the previously proved ninth/eighth gain.
The selected shell is NOT claimed to sit near the escaping outer cutoff. -/
theorem h3Path_noL2Trace_finiteDissipation_ninthEighthEnergeticShell244
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
      Tendsto (fun k => τ (v k)) atTop (𝓝 T) ∧
      (∀ n, τ n ∈ Set.Ioo a T) ∧
      (∀ k l, k < l → τ (v k) + δ (v k) < τ (v l)) ∧
      Summable (fun k => δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ∧
      (∀ k, v k ≤ m k ∧ m k < N (v k) ∧
        0 < h3PathActualBandRawKineticMass244
          ((m k : ℝ) + 1) ((m k : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (∀ A : ℝ, 0 ≤ A → ∀ k : ℕ,
        A * (((v k : ℝ) + 1) ^ 9) < ((m k : ℝ) + 3) ^ 8 ∨
        3 < 16 * A * ((N (v k) - v k : ℕ) : ℝ) *
          (((v k : ℝ) + 1) ^ 6) *
          h3PathActualBandRawKineticMass244
            ((m k : ℝ) + 1) ((m k : ℝ) + 2)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k)))) ∧
      (Tendsto (fun k : ℕ =>
          ((N (v k) - v k : ℕ) : ℝ) * (((v k : ℝ) + 1) ^ 6) *
          h3PathActualBandRawKineticMass244
            ((m k : ℝ) + 1) ((m k : ℝ) + 2)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))
        atTop (𝓝 0) →
        Tendsto (fun k : ℕ =>
          (((m k : ℝ) + 3) ^ 8) / (((v k : ℝ) + 1) ^ 9))
          atTop atTop) ∧
      (∀ η B S : ℝ, 0 < η → 0 ≤ B →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * ((v k : ℝ) + 1) ^ 6 ∧
          C (v k) ^ 2 ≤ S ^ 2) →
        Tendsto (fun k : ℕ =>
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 /
            (((v k : ℝ) + 1) ^ 9)) atTop atTop) := by
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
  have hR : ∀ k, 1 ≤ R k := by
    intro k
    dsimp only [R]
    have hNat : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hNat]
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
  have hOuterEq (k : ℕ) :
      R k + L k + 1 = ((N (v k) : ℝ) + 2) := by
    have hVN : v k ≤ N (v k) :=
      (hShell k).1.trans (hShell k).2.1.le
    dsimp only [R, L]
    rw [Nat.cast_sub hVN]
    ring
  refine ⟨τ, N, K, C, δ, v, m, hv, hCofinal, hTime,
    hSeparate, hSummable, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(hShell k).1, (hShell k).2.1, (hShell k).2.2.2.1⟩
  · intro A hA k
    have hAlt := h3Path_widthShell_ninthEighth_or_sixthMass244
      (R k) (J k) (L k) (μ k) A
      (lt_of_lt_of_le zero_lt_one (hR k)) (hL k) (hμ k) hA (hCost k)
    simpa only [R, J, L, μ] using hAlt
  · intro hSixth
    exact h3Path_widthShell_sixthMassVanishing_ninthEighthEscape244
      R J L μ
      (fun k => lt_of_lt_of_le zero_lt_one (hR k)) hL hμ hCost
      (by simpa only [R, J, L, μ] using hSixth)
  · intro η B S hη hB hRegime
    have hSep : ∀ M : ℝ, 0 ≤ M → ∀ᶠ k : ℕ in atTop,
        M * (R k) ^ 9 < (R k + L k + 1) ^ 8 := by
      intro M hM
      have hImp := hOuter η B S M hη hB hM
      filter_upwards [hImp, hRegime] with k hk hReg
      have hAtK := (hk hReg.1 hReg.2.1 hReg.2.2).1
      rw [hOuterEq k]
      dsimp only [R]
      convert hAtK using 1
      ring
    have hWidth := h3Path_ninthEighth_widthPowerRatio_tendsto_atTop244
      R L hR hL hSep
    simpa only [R, L] using hWidth

end
end PrimeTensor.FirstMonomialTriad
