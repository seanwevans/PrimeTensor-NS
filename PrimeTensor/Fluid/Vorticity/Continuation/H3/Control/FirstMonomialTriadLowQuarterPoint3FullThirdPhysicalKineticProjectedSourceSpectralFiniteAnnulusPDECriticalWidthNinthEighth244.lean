import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECriticalShellWidthEscape244
import Mathlib.Tactic

/-!
# Exact ninth/eighth growth transferred from the outer cutoff to annular width

The prior physical PDE alternative forces M R^9 < (R+L+1)^8 for each fixed
M >= 0, with R = v+1 and L = N(v)-v. It already forces L/R -> infinity.
Once L >= R, the elementary bound R+L+1 <= 2(L+1) transfers the entire
ninth/eighth separation to the literal width, retaining the exponent 9/8:
  for every M >= 0, eventually M R^9 < (L+1)^8.

The conclusion is CONDITIONAL on the same noncompression, linear-rate, and
physical-source-ceiling regime; it does not infer these hypotheses from
Navier--Stokes, and it does not force the selected shell to be near the outer
cutoff. The shell and disjoint physical clocks remain synchronized.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- If the width already exceeds the inner cutoff, transferring an outer
ninth/eighth gain to the width costs only the fixed factor 2^8 = 256. -/
theorem h3Path_ninthEighth_outerGain_to_widthGain_point244
    (R L M : ℝ) (hR : 1 ≤ R) (hRL : R ≤ L)
    (hOuter : (256 * M) * R ^ 9 < (R + L + 1) ^ 8) :
    M * R ^ 9 < (L + 1) ^ 8 := by
  have hNonneg : 0 ≤ R + L + 1 := by
    linarith only [hR, hRL]
  have hUpper : R + L + 1 ≤ 2 * (L + 1) := by
    linarith only [hRL]
  have hPower : (R + L + 1) ^ 8 ≤ (2 * (L + 1)) ^ 8 :=
    pow_le_pow_left₀ hNonneg hUpper 8
  have hPowerBound : (R + L + 1) ^ 8 ≤ 256 * (L + 1) ^ 8 := by
    calc
      _ ≤ (2 * (L + 1)) ^ 8 := hPower
      _ = 256 * (L + 1) ^ 8 := by ring
  have hScaled : 256 * (M * R ^ 9) < 256 * (L + 1) ^ 8 := by
    calc
      _ = (256 * M) * R ^ 9 := by ring
      _ < (R + L + 1) ^ 8 := hOuter
      _ ≤ 256 * (L + 1) ^ 8 := hPowerBound
  by_contra hNot
  have hReverse : (L + 1) ^ 8 ≤ M * R ^ 9 := le_of_not_gt hNot
  have hReverseScaled :=
    mul_le_mul_of_nonneg_left hReverse (by norm_num : (0 : ℝ) ≤ 256)
  exact (not_le_of_gt hScaled) hReverseScaled

/-- For a sequence, the PDE ninth/eighth bound on outer radii transfers to
the actual annular width with no loss of the critical exponent. -/
theorem h3Path_ninthEighth_outerGain_to_widthGain244
    (R L : ℕ → ℝ) (hR : ∀ k, 1 ≤ R k) (hL : ∀ k, 0 ≤ L k)
    (hOuter : ∀ M : ℝ, 0 ≤ M → ∀ᶠ k : ℕ in atTop,
      M * (R k) ^ 9 < (R k + L k + 1) ^ 8) :
    ∀ M : ℝ, 0 ≤ M → ∀ᶠ k : ℕ in atTop,
      M * (R k) ^ 9 < (L k + 1) ^ 8 := by
  have hRelative := h3Path_ninthEighthSeparation_forces_relativeWidthEscape244
    R L hR hL hOuter
  have hWide : ∀ᶠ k : ℕ in atTop, (1 : ℝ) ≤ L k / R k :=
    hRelative.eventually (eventually_ge_atTop (1 : ℝ))
  intro M hM
  have hOuterEvent := hOuter (256 * M)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 256) hM)
  filter_upwards [hWide, hOuterEvent] with k hkWide hkOuter
  have hPos : 0 < R k := lt_of_lt_of_le zero_lt_one (hR k)
  have hRL : R k ≤ L k := by
    have hMul := (le_div_iff₀ hPos).1 hkWide
    simpa only [one_mul] using hMul
  exact h3Path_ninthEighth_outerGain_to_widthGain_point244
    (R k) (L k) M (hR k) hRL hkOuter

/-- The actual critical ninth/eighth width quotient diverges, not merely
its weaker first-power relative width quotient. -/
theorem h3Path_ninthEighth_widthPowerRatio_tendsto_atTop244
    (R L : ℕ → ℝ) (hR : ∀ k, 1 ≤ R k) (hL : ∀ k, 0 ≤ L k)
    (hOuter : ∀ M : ℝ, 0 ≤ M → ∀ᶠ k : ℕ in atTop,
      M * (R k) ^ 9 < (R k + L k + 1) ^ 8) :
    Tendsto (fun k : ℕ => (L k + 1) ^ 8 / (R k) ^ 9)
      atTop atTop := by
  have hWidth := h3Path_ninthEighth_outerGain_to_widthGain244
    R L hR hL hOuter
  apply Filter.tendsto_atTop.2
  intro A
  let M : ℝ := max A 0 + 1
  have hM : 0 ≤ M := by
    dsimp only [M]
    have hMax : (0 : ℝ) ≤ max A 0 := le_max_right _ _
    linarith only [hMax]
  have hAM : A ≤ M := by
    dsimp only [M]
    have hMax : A ≤ max A 0 := le_max_left _ _
    linarith only [hMax]
  filter_upwards [hWidth M hM] with k hk
  have hRPos : 0 < (R k) ^ 9 :=
    pow_pos (lt_of_lt_of_le zero_lt_one (hR k)) 9
  have hDiv : M < (L k + 1) ^ 8 / (R k) ^ 9 :=
    (lt_div_iff₀ hRPos).2 hk
  exact hAM.trans hDiv.le

/-- Same-witness physical improvement: on the previously established
PDE branch, the LITERAL first-crossing width retains ninth/eighth growth.
The selected positive-kinetic shell and disjoint quadratic-sharp clocks are
unchanged. No source or noncompression bound is manufactured here. -/
theorem h3Path_noL2Trace_finiteDissipation_criticalWidthNinthEighth244
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
      (Tendsto (fun k : ℕ =>
          ((N (v k) - v k : ℕ) : ℝ) * (((v k : ℝ) + 1) ^ 5) *
          h3PathActualBandRawKineticMass244
            ((m k : ℝ) + 1) ((m k : ℝ) + 2)
            (h3AuditActualSpectralVelocityTotal hH3 (τ (v k))))
        atTop (𝓝 0) →
        Tendsto (fun k : ℕ =>
          ((N (v k) - v k : ℕ) : ℝ) / ((v k : ℝ) + 1)) atTop atTop) ∧
      (∀ η B S : ℝ, 0 < η → 0 ≤ B →
        (∀ᶠ k : ℕ in atTop,
          η ≤ ((v k : ℝ) + 1) ^ 3 * (((T - τ (v k)) / 2) / 2) ∧
          h3PathCubicAnnulusActualLinearRate244 N K C (v k) + 1 ≤
            B * ((v k : ℝ) + 1) ^ 6 ∧
          C (v k) ^ 2 ≤ S ^ 2) →
        (∀ M : ℝ, 0 ≤ M → ∀ᶠ k : ℕ in atTop,
          M * (((v k : ℝ) + 1) ^ 9) <
            (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8) ∧
        Tendsto (fun k : ℕ =>
          (((N (v k) - v k : ℕ) : ℝ) + 1) ^ 8 /
            (((v k : ℝ) + 1) ^ 9)) atTop atTop) := by
  obtain ⟨τ, N, K, C, δ, v, m, hv, hCofinal, hTime, hSeparate,
      hSummable, hSelected, _hAlternative, hCritical, hOuter⟩ :=
    h3Path_noL2Trace_finiteDissipation_criticalShellEscape244
      hH3 hClass hMass hNoTrace hDInt
  have hShell : ∀ k, v k ≤ m k ∧ m k < N (v k) := by
    intro k
    exact ⟨(hSelected k).1, (hSelected k).2.1⟩
  let R : ℕ → ℝ := fun k => ((v k : ℝ) + 1)
  let L : ℕ → ℝ := fun k => ((N (v k) - v k : ℕ) : ℝ)
  have hR : ∀ k, 1 ≤ R k := by
    intro k
    dsimp only [R]
    have hNat : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hNat]
  have hL : ∀ k, 0 ≤ L k := by
    intro k
    dsimp only [L]
    exact Nat.cast_nonneg _
  have hOuterEq (k : ℕ) :
      R k + L k + 1 = ((N (v k) : ℝ) + 2) := by
    have hVN : v k ≤ N (v k) :=
      (hShell k).1.trans (hShell k).2.le
    dsimp only [R, L]
    rw [Nat.cast_sub hVN]
    ring
  refine ⟨τ, N, K, C, δ, v, m, hv, hCofinal, hTime,
    hSeparate, hSummable, hSelected, ?_, ?_⟩
  · intro hVanishing
    have hShellEscape := hCritical hVanishing
    exact h3Path_selectedIntegerShell_relativeEscape_forces_widthEscape244
      v m N hShell hShellEscape
  · intro η B S hη hB hRegime
    have hSep : ∀ M : ℝ, 0 ≤ M → ∀ᶠ k : ℕ in atTop,
        M * (R k) ^ 9 < (R k + L k + 1) ^ 8 := by
      intro M hM
      have hImp := hOuter η B S M hη hB hM
      filter_upwards [hImp, hRegime] with k hk hReg
      have hAtK := hk hReg.1 hReg.2.1 hReg.2.2
      rw [hOuterEq k]
      dsimp only [R]
      convert hAtK using 1
      ring
    have hWidth := h3Path_ninthEighth_outerGain_to_widthGain244
      R L hR hL hSep
    have hRatio := h3Path_ninthEighth_widthPowerRatio_tendsto_atTop244
      R L hR hL hSep
    constructor
    · intro M hM
      simpa only [R, L] using hWidth M hM
    · simpa only [R, L] using hRatio

end
end PrimeTensor.FirstMonomialTriad
