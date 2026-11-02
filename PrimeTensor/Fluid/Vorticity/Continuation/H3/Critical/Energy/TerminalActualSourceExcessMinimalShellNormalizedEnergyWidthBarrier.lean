import PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessMinimalShellSublinearEnergyWidthEscape
import Mathlib.Tactic

/-!
# Unconditional normalized H3 anchor energy / minimal annulus width obstruction

A minimal quarter-cubic first crossing has R^3 < 4 (Q+1)^2 E3.
Dividing by its strictly positive cubic radius gives the exact
nonasymptotic product constraint

  1 < 4 (E3/R) ((Q+1)/R)^2.

On the true minimal first crossing Q+1=R+L+1, L=N-n. Hence EVERY
window, independently of any asymptotic source, kinetic depletion,
terminal-clock, or H3 energy bound, obeys the alternative

  D R < L  OR  1 < 4 (D+2)^2 (E3/R)

for each D>=0. The second arm is a concrete normalized physical H3
energy floor whenever annular width stays at most linear in R.

Both obstructions are transferred to the same disjoint no-terminal-L2-trace
PDE windows carrying minimality, last-shell Fourier kinetic mass,
width-averaged energetic shell, and the exact sixth/ninth PDE-rate alternative.
No finite full terminal H3 dissipation hypothesis is used.
-/

namespace PrimeTensor.Bridge.Euclidean

open Set Filter MeasureTheory
open PrimeTensor.FirstMonomialTriad
open scoped BigOperators Topology Interval ENNReal

noncomputable section
set_option maxHeartbeats 1800000

noncomputable local instance axisFintypeMinimalNormalizedEnergyWidth
    (d : Depth) : Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceMinimalNormalizedEnergyWidth :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The exact cubic energy/outer-radius product at a physical crossing.
This is independent of the choice of positive frequency normalization. -/
theorem h3Critical_scalar_quarterCubic_normalizedEnergyOuterProduct
    (R Q E : ℝ) (hR : 0 < R)
    (hCross : R ^ 3 < 4 * (Q + 1) ^ 2 * E) :
    1 < 4 * (E / R) * ((Q + 1) / R) ^ 2 := by
  have hEq :
      R ^ 3 * (4 * (E / R) * ((Q + 1) / R) ^ 2) =
        4 * (Q + 1) ^ 2 * E := by
    field_simp [ne_of_gt hR]
    <;> ring
  have hScaled :
      R ^ 3 * (1 : ℝ) <
        R ^ 3 * (4 * (E / R) * ((Q + 1) / R) ^ 2) := by
    rw [hEq]
    simpa only [mul_one] using hCross
  by_contra hNot
  have hLe : 4 * (E / R) * ((Q + 1) / R) ^ 2 ≤ 1 :=
    le_of_not_gt hNot
  have hScaledReverse :
      R ^ 3 * (4 * (E / R) * ((Q + 1) / R) ^ 2) ≤
        R ^ 3 * (1 : ℝ) :=
    mul_le_mul_of_nonneg_left hLe (pow_pos hR 3).le
  exact (not_lt_of_ge hScaledReverse) hScaled

/-- Every first crossing has a quantitative dichotomy, with NO
asymptotic assumption: either its true integer width exceeds D*R,
or its normalized physical H3 anchor energy has a fixed positive floor. -/
theorem h3Critical_scalar_minimalWidth_or_normalizedEnergyFloor
    (R L E D : ℝ) (hR : 1 ≤ R) (hL : 0 ≤ L) (hE : 0 ≤ E)
    (hCross : R ^ 3 < 4 * (R + L + 1) ^ 2 * E) :
    D * R < L ∨ 1 < 4 * (D + 2) ^ 2 * (E / R) := by
  by_cases hWide : D * R < L
  · exact Or.inl hWide
  · right
    have hNarrow : L ≤ D * R := le_of_not_gt hWide
    have hOuter : (R + L) + 1 ≤ (D + 2) * R := by
      nlinarith only [hNarrow, hR]
    have hRQ : R ≤ R + L := by linarith only [hL]
    have hEnergy := h3Critical_scalar_quarterCubic_relativeOuter_forces_energyGrowth
      R (R + L) E (D + 2) hR hRQ hE hCross hOuter
    have hPos : 0 < R := lt_of_lt_of_le (by norm_num) hR
    have hNormalized : 1 < (4 * (D + 2) ^ 2 * E) / R :=
      (lt_div_iff₀ hPos).2 (by simpa only [one_mul] using hEnergy)
    convert hNormalized using 1
    ring

/-- The SAME minimal-shell, disjoint, exact-PDE source-rate witnesses carry
an unconditional normalized physical H3 energy--width restriction at every
index, not just in the sublinear-energy branch. The shell mass and the
sixth/ninth-rate alternative are retained without replacement witnesses. -/
theorem h3Critical_noL2Trace_disjointMinimalShell_energyWidthUncertainty
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hNoTrace : ¬ ∃ U : H3PhysicalRealFinVectorL2Hilbert,
      Tendsto (h3AuditInitialOldPhysicalHilbertTotal hH3)
        (𝓝[<] T) (𝓝 U)) :
    ∃ t : ℕ → ℝ, ∃ N m : ℕ → ℕ, ∃ C δ : ℕ → ℝ,
    ∃ v j : ℕ → ℕ,
      StrictMono v ∧
      Tendsto (fun k => t (v k)) atTop (𝓝 T) ∧
      (∀ k l : ℕ, k < l → t (v k) + δ (v k) < t (v l)) ∧
      (∀ k : ℕ, h3CriticalMinimalShellEnergyWindow
        hH3 (t (v k)) (v k) (N (v k)) (m (v k))
        (C (v k)) (δ (v k))) ∧
      (∀ q : ℕ,
        (∑ k ∈ Finset.range q,
          δ (v k) * (((v k : ℝ) + 1) ^ 3 / 2)) ≤
        ∑ k ∈ Finset.range q,
          (∫ s in t (v k)..(t (v k) + δ (v k)),
            h3PathActualLowRadialDissipation244 ((N (v k) : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s) -
            h3PathActualLowRadialDissipation244 ((v k : ℝ) + 1)
              (h3AuditActualSpectralVelocityTotal hH3 s))) ∧
      h3CriticalMinimalShellPhysicalSixthNinthAlternative (u := u)
        T t N C δ v ∧
      (∀ᶠ k : ℕ in atTop,
        v k ≤ j k ∧ j k < N (v k) ∧
        0 < h3PathActualBandRawKineticMass244
          ((j k : ℝ) + 1) ((j k : ℝ) + 2)
          (h3AuditActualSpectralVelocityTotal hH3 (t (v k)))) ∧
      (∀ k : ℕ,
        1 < 4 * (velocityH3EnergyAt u (t (v k)) / ((v k : ℝ) + 1)) *
          (((N (v k) : ℝ) + 2) / ((v k : ℝ) + 1)) ^ 2 ∧
        ∀ D : ℝ,
          D * ((v k : ℝ) + 1) < ((N (v k) - v k : ℕ) : ℝ) ∨
          1 < 4 * (D + 2) ^ 2 *
            (velocityH3EnergyAt u (t (v k)) / ((v k : ℝ) + 1))) := by
  obtain ⟨t, N, m, C, δ, v, j, hv, hCofinal, hSeparated,
      hWindows, hSum, hRates, hShell, _hSublinear⟩ :=
    h3Critical_noL2Trace_disjointMinimalShell_sublinearEnergyWidthEscape
      hH3 hClass hNoTrace
  refine ⟨t, N, m, C, δ, v, j, hv, hCofinal, hSeparated,
    hWindows, hSum, hRates, hShell, ?_⟩
  intro k
  let R : ℝ := (v k : ℝ) + 1
  let L : ℝ := ((N (v k) - v k : ℕ) : ℝ)
  let E : ℝ := velocityH3EnergyAt u (t (v k))
  have hR : 1 ≤ R := by
    dsimp only [R]
    have hn : (0 : ℝ) ≤ (v k : ℝ) := Nat.cast_nonneg _
    linarith only [hn]
  have hN : v k ≤ N (v k) := by
    rcases hWindows k with ⟨hNm, hvm, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
    omega
  have hL : 0 ≤ L := by dsimp only [L]; exact Nat.cast_nonneg _
  have hE : 0 ≤ E := by
    rcases hWindows k with ⟨_, _, _, _, _, _, _, hEnergy, _, _, _, _, _, _, _⟩
    exact (sq_nonneg _).trans hEnergy
  have hGeometry : R + L + 1 = (N (v k) : ℝ) + 2 := by
    dsimp only [R, L]
    rw [Nat.cast_sub hN]
    ring
  have hPhysical : R ^ 3 < 4 * (R + L + 1) ^ 2 * E := by
    rcases hWindows k with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hEnergyOuter, _, _⟩
    rw [hGeometry]
    simpa only [R, E] using hEnergyOuter
  constructor
  · have hProduct := h3Critical_scalar_quarterCubic_normalizedEnergyOuterProduct
      R (R + L) E (lt_of_lt_of_le (by norm_num) hR) hPhysical
    rw [hGeometry] at hProduct
    simpa only [R, E] using hProduct
  · intro D
    have hGate := h3Critical_scalar_minimalWidth_or_normalizedEnergyFloor
      R L E D hR hL hE hPhysical
    simpa only [R, L, E] using hGate

end
end PrimeTensor.Bridge.Euclidean
