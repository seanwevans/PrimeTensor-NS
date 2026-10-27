import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDECriticalShellFrequency244
import Mathlib.Tactic

/-!
# Critical shell depletion and physical ninth/eighth separation force relative width escape

For the canonical width-averaged energetic shell, R = v+1, J = m+3,
L = N(v)-v, and the shell lies inside the first-crossing annulus. Thus
J <= R+L+1. This geometric inequality upgrades conditional relative-shell
escape (J/R -> +infinity) into relative annular-width escape (L/R -> +infinity).

More strongly, the conditional physical PDE ninth/eighth barrier
  M R^9 < (R+L+1)^8  eventually, for EVERY constant M >= 0,
forces the same relative-width escape WITHOUT kinetic depletion. Both
mechanisms hold on the SAME previously selected physical PDE witnesses.

The PDE geometric/noncompression, linear rate, source and terminal full-H3
integrability assumptions are not established here and remain explicit.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory Set Filter
open scoped BigOperators Interval InnerProductSpace RealInnerProductSpace Topology

noncomputable section
set_option maxHeartbeats 1800000

/-- Geometry alone: an escaping energetic shell inside an annulus forces its
width to escape relative to its positive inner frequency. The extra 1
accounts for the shift between the unit-shell and outer-frequency radii. -/
theorem h3Path_relativeShellEscape_forces_relativeWidthEscape244
    (R J L : ℕ → ℝ)
    (hR : ∀ k, 1 ≤ R k)
    (hJBound : ∀ k, J k ≤ R k + L k + 1)
    (hEscape : Tendsto (fun k => J k / R k) atTop atTop) :
    Tendsto (fun k => L k / R k) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro A
  have hLarge : ∀ᶠ k : ℕ in atTop, A + 2 ≤ J k / R k :=
    hEscape.eventually (eventually_ge_atTop (A + 2))
  filter_upwards [hLarge] with k hk
  have hPos : 0 < R k := lt_of_lt_of_le zero_lt_one (hR k)
  have hScaled : (A + 2) * R k ≤ J k :=
    (le_div_iff₀ hPos).1 hk
  have hWidth : A * R k ≤ L k := by
    nlinarith only [hScaled, hJBound k, hR k]
  exact (le_div_iff₀ hPos).2 hWidth

/-- If the ninth/eighth separation holds at one radius with multiplier
(A+2)^8, then the annulus has width strictly greater than A times its
inner radius. No kinetic mass assumption appears in this implication. -/
theorem h3Path_ninthEighthSeparation_forces_superlinearWidthPoint244
    (R L A : ℝ) (hR : 1 ≤ R) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hSeparation : (A + 2) ^ 8 * R ^ 9 < (R + L + 1) ^ 8) :
    A * R < L := by
  by_contra hNot
  have hNarrow : L ≤ A * R := le_of_not_gt hNot
  have hUpper : R + L + 1 ≤ (A + 2) * R := by
    nlinarith only [hNarrow, hR]
  have hNonneg : 0 ≤ R + L + 1 := by linarith only [hR, hL]
  have hPower : (R + L + 1) ^ 8 ≤ ((A + 2) * R) ^ 8 :=
    pow_le_pow_left₀ hNonneg hUpper 8
  have hR8 : R ^ 8 ≤ R ^ 9 := by
    calc
      _ = R ^ 8 * 1 := by ring
      _ ≤ R ^ 8 * R := mul_le_mul_of_nonneg_left hR (by positivity)
      _ = R ^ 9 := by ring
  have hBound : (R + L + 1) ^ 8 ≤ (A + 2) ^ 8 * R ^ 9 := by
    calc
      _ ≤ ((A + 2) * R) ^ 8 := hPower
      _ = (A + 2) ^ 8 * R ^ 8 := by ring
      _ ≤ (A + 2) ^ 8 * R ^ 9 :=
        mul_le_mul_of_nonneg_left hR8 (by positivity)
  exact (not_lt_of_ge hBound) hSeparation

/-- An eventual ninth/eighth cutoff barrier for every multiplier implies
unbounded annular width relative to the inner cutoff, even when the
width-averaged shell's critical kinetic mass does not vanish. -/
theorem h3Path_ninthEighthSeparation_forces_relativeWidthEscape244
    (R L : ℕ → ℝ)
    (hR : ∀ k, 1 ≤ R k) (hL : ∀ k, 0 ≤ L k)
    (hSeparation : ∀ M : ℝ, 0 ≤ M → ∀ᶠ k : ℕ in atTop,
      M * (R k) ^ 9 < (R k + L k + 1) ^ 8) :
    Tendsto (fun k => L k / R k) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro A
  let B : ℝ := max A 0
  have hB : 0 ≤ B := le_max_right _ _
  have hAB : A ≤ B := le_max_left _ _
  have hEvent := hSeparation ((B + 2) ^ 8) (by positivity)
  filter_upwards [hEvent] with k hk
  have hFar := h3Path_ninthEighthSeparation_forces_superlinearWidthPoint244
    (R k) (L k) B (hR k) (hL k) hB hk
  have hPos : 0 < R k := lt_of_lt_of_le zero_lt_one (hR k)
  have hAWidth : A * R k ≤ L k :=
    (mul_le_mul_of_nonneg_right hAB hPos.le).trans hFar.le
  exact (le_div_iff₀ hPos).2 hAWidth

/-- For the integer-selected physical shell, its shifted frequency obeys
the exact annular geometry J <= R+L+1, with L=N(v)-v. -/
theorem h3Path_selectedIntegerShell_annularWidthGeometry244
    (v m N : ℕ → ℕ)
    (hShell : ∀ k, v k ≤ m k ∧ m k < N (v k))
    (k : ℕ) :
    ((m k : ℝ) + 3) ≤
      ((v k : ℝ) + 1) + ((N (v k) - v k : ℕ) : ℝ) + 1 := by
  have hV : v k ≤ N (v k) := (hShell k).1.trans (hShell k).2.le
  have hmNext : m k + 1 ≤ N (v k) := Nat.succ_le_of_lt (hShell k).2
  have hmCast : (m k : ℝ) + 1 ≤ (N (v k) : ℝ) := by
    have hCast : (((m k + 1 : ℕ) : ℝ)) ≤ (N (v k) : ℝ) := by
      exact_mod_cast hmNext
    simpa only [Nat.cast_add, Nat.cast_one] using hCast
  rw [Nat.cast_sub hV]
  linarith only [hmCast]

/-- The same integer shell cannot undergo relative-frequency escape while
the width of its containing minimal first-crossing annulus stays linear. -/
theorem h3Path_selectedIntegerShell_relativeEscape_forces_widthEscape244
    (v m N : ℕ → ℕ)
    (hShell : ∀ k, v k ≤ m k ∧ m k < N (v k))
    (hEscape : Tendsto (fun k : ℕ =>
       ((m k : ℝ) + 3) / ((v k : ℝ) + 1)) atTop atTop) :
    Tendsto (fun k : ℕ =>
       ((N (v k) - v k : ℕ) : ℝ) / ((v k : ℝ) + 1)) atTop atTop := by
  let R : ℕ → ℝ := fun k => ((v k : ℝ) + 1)
  let J : ℕ → ℝ := fun k => ((m k : ℝ) + 3)
  let L : ℕ → ℝ := fun k => ((N (v k) - v k : ℕ) : ℝ)
  have hR : ∀ k, 1 ≤ R k := by
    intro k
    dsimp only [R]
    have hNat : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hNat]
  have hGeom : ∀ k, J k ≤ R k + L k + 1 := by
    intro k
    exact h3Path_selectedIntegerShell_annularWidthGeometry244 v m N hShell k
  exact h3Path_relativeShellEscape_forces_relativeWidthEscape244
    R J L hR hGeom (by simpa only [R, J] using hEscape)

/-- Both width-escape mechanisms apply to exactly the same cofinal physical
quadratic-sharp PDE-window witnesses, with the energetic unit shell retained.
The kinetic-depletion route is conditional on critical mass vanishing; the
PDE route requires only its previously exposed noncompression/rate/source
regime and DOES NOT require critical kinetic depletion. -/
theorem h3Path_noL2Trace_finiteDissipation_twoWidthEscapeMechanisms244
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
        Tendsto (fun k : ℕ =>
          ((N (v k) - v k : ℕ) : ℝ) / ((v k : ℝ) + 1)) atTop atTop) := by
  obtain ⟨τ, N, K, C, δ, v, m, hv, hCofinal, hTime, hSeparate,
      hSummable, hSelected, _hMassAlternative, hCritical, hOuter⟩ :=
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
    have hNN : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hNN]
  have hL : ∀ k, 0 ≤ L k := by
    intro k
    exact Nat.cast_nonneg _
  have hOuterEq (k : ℕ) :
      R k + L k + 1 = ((N (v k) : ℝ) + 2) := by
    have hVN : v k ≤ N (v k) := (hShell k).1.trans (hShell k).2.le
    dsimp only [R, L]
    rw [Nat.cast_sub hVN]
    ring
  refine ⟨τ, N, K, C, δ, v, m, hv, hCofinal, hTime, hSeparate,
    hSummable, hSelected, ?_, ?_⟩
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
    have hWidth := h3Path_ninthEighthSeparation_forces_relativeWidthEscape244
      R L hR hL hSep
    simpa only [R, L] using hWidth

end
end PrimeTensor.FirstMonomialTriad
